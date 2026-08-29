// solve_775.cpp — three-value AND/OR solver for the 7,7,5-game with D4
// symmetry canonicalization and pairing-strategy acceleration, following
// Hsu et al. (TCS 2020) "On solving the 7,7,5-game and the 8,8,5-game".
//
// UNTRUSTED direction probe: determines the game value of empty 7x7
// five-in-a-row (standard rules) empirically.  Not a proof artifact.
//
// Values: 0 = black win, 1 = white win, 2 = draw.

#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <unordered_map>
#include <vector>

namespace {

constexpr int size = 7;
constexpr int winLen = 5;
constexpr int cells = size * size;

using Bits = std::uint64_t;

int idx(int x, int y) {
  return y * size + x;
}

struct Window {
  int start = 0;
  int dx = 0;
  int dy = 0;
};

std::vector<Window> allWindows() {
  std::vector<Window> windows;
  for (int y = 0; y < size; ++y) {
    for (int x = 0; x <= size - winLen; ++x) {
      windows.push_back({idx(x, y), 1, 0});
    }
  }
  for (int x = 0; x < size; ++x) {
    for (int y = 0; y <= size - winLen; ++y) {
      windows.push_back({idx(x, y), 0, 1});
    }
  }
  for (int y = 0; y <= size - winLen; ++y) {
    for (int x = 0; x <= size - winLen; ++x) {
      windows.push_back({idx(x, y), 1, 1});
    }
  }
  for (int y = winLen - 1; y < size; ++y) {
    for (int x = 0; x <= size - winLen; ++x) {
      windows.push_back({idx(x, y), 1, -1});
    }
  }
  return windows;
}

int cellAt(const Window& w, int i) {
  const int x = w.start % size + i * w.dx;
  const int y = w.start / size + i * w.dy;
  return idx(x, y);
}

// D4 symmetries: for each transformed coordinate, the bit position mapping.
std::array<std::array<int, cells>, 8> symMap() {
  std::array<std::array<int, cells>, 8> map{};
  for (int c = 0; c < cells; ++c) {
    const int x = c % size;
    const int y = c / size;
    const int xs[8] = {x, size - 1 - x, x, size - 1 - x, y, size - 1 - y, y,
                       size - 1 - y};
    const int ys[8] = {y, y, size - 1 - y, size - 1 - y, x, x, size - 1 - x,
                       size - 1 - x};
    for (int s = 0; s < 8; ++s) {
      map[s][c] = idx(xs[s], ys[s]);
    }
  }
  return map;
}

const std::array<std::array<int, cells>, 8> kSym = symMap();

struct Position {
  Bits black = 0;
  Bits white = 0;
  bool turnBlack = true;

  bool operator==(const Position& other) const {
    return black == other.black && white == other.white &&
           turnBlack == other.turnBlack;
  }
};

struct PositionHash {
  std::size_t operator()(const Position& p) const {
    std::uint64_t h = p.black;
    h ^= p.white + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    h ^= (p.turnBlack ? 0x12345678ULL : 0x87654321ULL);
    return static_cast<std::size_t>(h);
  }
};

Bits symBits(Bits b, int s) {
  Bits result = 0;
  for (int c = 0; c < cells; ++c) {
    if ((b & (Bits{1} << c)) != 0) {
      result |= Bits{1} << kSym[s][c];
    }
  }
  return result;
}

Position canonical(const Position& p) {
  Position best = p;
  for (int s = 1; s < 8; ++s) {
    const Position q{symBits(p.black, s), symBits(p.white, s), p.turnBlack};
    if (q.black < best.black || (q.black == best.black && q.white < best.white)) {
      best = q;
    }
  }
  return best;
}

bool hasFive(Bits stones) {
  const std::vector<Window> windows = allWindows();
  for (const Window& w : windows) {
    int count = 0;
    for (int i = 0; i < winLen; ++i) {
      if ((stones & (Bits{1} << cellAt(w, i))) != 0) {
        ++count;
      }
    }
    if (count == winLen) {
      return true;
    }
  }
  return false;
}

std::vector<int> emptyCells(const Position& p) {
  std::vector<int> result;
  for (int c = 0; c < cells; ++c) {
    if (((p.black | p.white) & (Bits{1} << c)) == 0) {
      result.push_back(c);
    }
  }
  return result;
}

// Pairing validity for the defender: every window without a white (breaker)
// stone contains a full pair of (maker, defender) free cells.
// Returns the pair list if a covering pairing exists (simple greedy+backtrack).
bool findPairing(const Position& p, bool defenderBlack,
                 std::vector<std::pair<int, int>>& pairs) {
  const Bits defender = defenderBlack ? p.black : p.white;
  const Bits maker = defenderBlack ? p.white : p.black;
  const std::vector<Window> windows = allWindows();
  const int lineCount = static_cast<int>(windows.size());
  std::vector<bool> covered(lineCount, false);
  for (int line = 0; line < lineCount; ++line) {
    if ((windows[line].start & 0) == 0) {
    }
    bool hasDefender = false;
    for (int i = 0; i < winLen; ++i) {
      const int c = cellAt(windows[line], i);
      if ((defender & (Bits{1} << c)) != 0) {
        hasDefender = true;
        break;
      }
    }
    if (hasDefender) {
      covered[line] = true;
    }
  }
  std::array<int, cells> partner{};
  partner.fill(-1);
  const auto unassigned = [&](int line) {
    Bits result = 0;
    for (int i = 0; i < winLen; ++i) {
      const int c = cellAt(windows[line], i);
      const Bits mask = Bits{1} << c;
      if (partner[c] == -1 && (maker & mask) == 0 && (defender & mask) == 0) {
        result |= mask;
      }
    }
    return result;
  };
  std::uint64_t nodes = 0;
  std::vector<std::pair<int, int>> selected;
  const auto covers = [&](int line, const std::pair<int, int>& pair) {
    bool in1 = false;
    bool in2 = false;
    for (int i = 0; i < winLen; ++i) {
      const int c = cellAt(windows[line], i);
      in1 = in1 || c == pair.first;
      in2 = in2 || c == pair.second;
    }
    return in1 && in2;
  };
  // Recursive search with forced-pair pruning (bounded).
  bool found = false;
  std::vector<std::pair<int, int>> solution;
  const auto search = [&](const auto& self) -> bool {
    if (nodes++ > 2'000'000) {
      return false;
    }
    // forced pairs
    while (true) {
      bool any = false;
      for (int line = 0; line < lineCount; ++line) {
        if (covered[line]) {
          continue;
        }
        const Bits free = unassigned(line);
        const int freeCount = __builtin_popcountll(free);
        if (freeCount < 2) {
          return false;
        }
        if (freeCount == 2) {
          const int a = __builtin_ctzll(free);
          const int b = __builtin_ctzll(free & ~(Bits{1} << a));
          partner[a] = b;
          partner[b] = a;
          selected.push_back({a, b});
          for (int l = 0; l < lineCount; ++l) {
            if (!covered[l] && covers(l, {a, b})) {
              covered[l] = true;
            }
          }
          any = true;
          break;
        }
      }
      if (!any) {
        break;
      }
    }
    // MRV
    int chosenLine = -1;
    std::vector<std::pair<int, int>> candidates;
    std::size_t bestCount = std::numeric_limits<std::size_t>::max();
    for (int line = 0; line < lineCount; ++line) {
      if (covered[line]) {
        continue;
      }
      std::vector<std::pair<int, int>> cand;
      for (int i = 0; i < winLen; ++i) {
        for (int j = i + 1; j < winLen; ++j) {
          const int a = cellAt(windows[line], i);
          const int b = cellAt(windows[line], j);
          const Bits am = Bits{1} << a;
          const Bits bm = Bits{1} << b;
          if (partner[a] == -1 && partner[b] == -1 && (maker & am) == 0 &&
              (defender & am) == 0 && (maker & bm) == 0 &&
              (defender & bm) == 0) {
            cand.push_back({a, b});
          }
        }
      }
      if (cand.empty()) {
        return false;
      }
      if (cand.size() < bestCount) {
        bestCount = cand.size();
        chosenLine = line;
        candidates = cand;
      }
    }
    if (chosenLine == -1) {
      solution = selected;
      return true;
    }
    for (const auto& cand : candidates) {
      partner[cand.first] = cand.second;
      partner[cand.second] = cand.first;
      selected.push_back(cand);
      for (int l = 0; l < lineCount; ++l) {
        if (!covered[l] && covers(l, cand)) {
          covered[l] = true;
        }
      }
      if (self(self)) {
        return true;
      }
      // undo
      selected.pop_back();
      partner[cand.first] = -1;
      partner[cand.second] = -1;
      for (int l = 0; l < lineCount; ++l) {
        if (covered[l]) {
          bool still = false;
          for (const auto& s : selected) {
            if (covers(l, s)) {
              still = true;
              break;
            }
          }
          covered[l] = still;
        }
      }
    }
    return false;
  };
  found = search(search);
  if (found) {
    pairs = solution;
  }
  return found;
}

// ------- solver -------
// 0 = black win, 1 = white win, 2 = draw; -1 = unknown (budget)

std::unordered_map<Position, int, PositionHash> table;
std::uint64_t expanded = 0;
const std::uint64_t kNodeBudget = 500'000'000;
bool budgetExhausted = false;

// pairing caches (canonical position -> has pairing) to keep it fast
std::unordered_map<Position, bool, PositionHash> pairingCacheBlack;
std::unordered_map<Position, bool, PositionHash> pairingCacheWhite;

int solve(const Position& raw) {
  if (budgetExhausted) {
    return -1;
  }
  const Position p = canonical(raw);
  const auto it = table.find(p);
  if (it != table.end()) {
    return it->second;
  }
  if (++expanded > kNodeBudget) {
    budgetExhausted = true;
    return -1;
  }
  // terminal
  if (hasFive(p.black)) {
    table[p] = 0;
    return 0;
  }
  if (hasFive(p.white)) {
    table[p] = 1;
    return 1;
  }
  const std::vector<int> empties = emptyCells(p);
  if (empties.empty()) {
    table[p] = 2;
    return 2;
  }
  // Pairing acceleration: when the defender (the player NOT to move) has a
  // covering pairing, the mover cannot win from here; the node value is then
  // restricted to {draw, mover-win}, which prunes the win search below.
  // Pairings are only probed on late positions (few empty cells), where they
  // are cheap and likely to exist.
  const int emptiesCount = static_cast<int>(empties.size());
  if (emptiesCount <= 25) {
    if (p.turnBlack) {
      // white defends: black cannot win
      auto pc = pairingCacheWhite.find(p);
      if (pc == pairingCacheWhite.end()) {
        std::vector<std::pair<int, int>> pairs;
        const bool ok = findPairing(p, false, pairs);
        pc = pairingCacheWhite.emplace(p, ok).first;
      }
      if (pc->second) {
        // value in {1, 2}
        bool sawWhite = true;
        bool sawDraw = false;
        bool sawUnknown = false;
        for (const int m : empties) {
          Position q = p;
          q.black |= Bits{1} << m;
          q.turnBlack = false;
          const int v = solve(q);
          if (v == 0) {
            // pairing says impossible; be safe and return the computed value
            table[p] = 0;
            return 0;
          }
          if (v == 1) {
            // all-white so far
          } else if (v == 2) {
            sawWhite = false;
            sawDraw = true;
          } else {
            sawWhite = false;
            sawUnknown = true;
          }
        }
        if (sawUnknown) {
          table[p] = -1;
          return -1;
        }
        const int result = sawWhite ? 1 : (sawDraw ? 2 : -1);
        table[p] = result;
        return result;
      }
    } else {
      // black defends: white cannot win
      auto pc = pairingCacheBlack.find(p);
      if (pc == pairingCacheBlack.end()) {
        std::vector<std::pair<int, int>> pairs;
        const bool ok = findPairing(p, true, pairs);
        pc = pairingCacheBlack.emplace(p, ok).first;
      }
      if (pc->second) {
        // value in {0, 2}
        bool sawBlack = true;
        bool sawDraw = false;
        bool sawUnknown = false;
        for (const int m : empties) {
          Position q = p;
          q.white |= Bits{1} << m;
          q.turnBlack = true;
          const int v = solve(q);
          if (v == 1) {
            table[p] = 1;
            return 1;
          }
          if (v == 0) {
            // all-black so far
          } else if (v == 2) {
            sawBlack = false;
            sawDraw = true;
          } else {
            sawBlack = false;
            sawUnknown = true;
          }
        }
        if (sawUnknown) {
          table[p] = -1;
          return -1;
        }
        const int result = sawBlack ? 0 : (sawDraw ? 2 : -1);
        table[p] = result;
        return result;
      }
    }
  }
  // exact AND/OR
  if (p.turnBlack) {
    // black OR node: black wins if any move leads to black win; white wins
    // if every move leads to white win; else draw.
    bool sawWhite = true;
    bool sawDraw = false;
    bool sawUnknown = false;
    for (const int m : empties) {
      Position q = p;
      q.black |= Bits{1} << m;
      q.turnBlack = false;
      const int v = solve(q);
      if (v == 0) {
        table[p] = 0;
        return 0;
      }
      if (v == 1) {
        // all-white so far
      } else if (v == 2) {
        sawWhite = false;
        sawDraw = true;
      } else {
        sawWhite = false;
        sawUnknown = true;
      }
    }
    if (sawUnknown) {
      table[p] = -1;
      return -1;
    }
    const int result = sawWhite ? 1 : (sawDraw ? 2 : -1);
    table[p] = result;
    return result;
  }
  // white OR node
  bool sawBlack = true;
  bool sawDraw = false;
  bool sawUnknown = false;
  for (const int m : empties) {
    Position q = p;
    q.white |= Bits{1} << m;
    q.turnBlack = true;
    const int v = solve(q);
    if (v == 1) {
      table[p] = 1;
      return 1;
    }
    if (v == 0) {
      // all-black so far
    } else if (v == 2) {
      sawBlack = false;
      sawDraw = true;
    } else {
      sawBlack = false;
      sawUnknown = true;
    }
  }
  if (sawUnknown) {
    table[p] = -1;
    return -1;
  }
  const int result = sawBlack ? 0 : (sawDraw ? 2 : -1);
  table[p] = result;
  return result;
}

}  // namespace

int main() {
  const std::vector<Window> windows = allWindows();
  std::cout << "windows=" << windows.size() << "\n";
  Position root;
  const int value = solve(root);
  if (value == 0) {
    std::cout << "value=black_win\n";
  } else if (value == 1) {
    std::cout << "value=white_win\n";
  } else if (value == 2) {
    std::cout << "value=draw\n";
  } else {
    std::cout << "value=unknown\n";
  }
  std::cout << "expanded=" << expanded << " table=" << table.size()
            << " budget_exhausted=" << (budgetExhausted ? "yes" : "no")
            << "\n";
  return value < 0 ? 2 : 0;
}
