// threat_sim.cpp — feasibility check: can a simple threat-response White
// defense hold on 7x7 against a greedy attacking Black?
//
// This is an UNTRUSTED direction probe only.  If White always holds, a
// formal threat-response strategy is the remaining route to
// WhiteCanPreventBlackWin; if Black always breaks through, the game may
// be a Black win and the whole target changes.
//
// Black: greedy attack (win > double threat > single threat > center-ish).
// White: must answer every immediate four (win point) and every open three;
//        if two unanswerable threats exist at once, White loses.

#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

namespace {

constexpr int size = 7;
constexpr int winLen = 5;

struct Coord {
  int x = 0;
  int y = 0;
  friend bool operator==(Coord lhs, Coord rhs) {
    return lhs.x == rhs.x && lhs.y == rhs.y;
  }
};

struct Board {
  std::array<std::uint64_t, 4> black{};
  std::array<std::uint64_t, 4> white{};

  int idx(Coord c) const {
    return c.y * size + c.x;
  }
  bool has(Coord c, bool isBlack) const {
    const std::uint64_t mask = 1ULL << idx(c);
    return ((isBlack ? black : white)[idx(c) / 64] & mask) != 0;
  }
  void set(Coord c, bool isBlack) {
    const int i = idx(c);
    (isBlack ? black : white)[i / 64] |= 1ULL << (i % 64);
  }
  bool empty(Coord c) const {
    const int i = idx(c);
    const std::uint64_t mask = 1ULL << (i % 64);
    const int w = i / 64;
    return ((black[w] | white[w]) & mask) == 0;
  }
  bool inside(Coord c) const {
    return c.x >= 0 && c.x < size && c.y >= 0 && c.y < size;
  }
  std::vector<Coord> empties() const {
    std::vector<Coord> result;
    for (int y = 0; y < size; ++y) {
      for (int x = 0; x < size; ++x) {
        if (empty({x, y})) {
          result.push_back({x, y});
        }
      }
    }
    return result;
  }
  bool wins(Coord c, bool isBlack) const {
    // does placing isBlack at c complete five?
    constexpr std::array<Coord, 4> dirs{{{1, 0}, {0, 1}, {1, 1}, {1, -1}}};
    for (const Coord d : dirs) {
      int len = 1;
      for (int sign : {-1, 1}) {
        Coord cur{c.x + sign * d.x, c.y + sign * d.y};
        while (inside(cur) && has(cur, isBlack)) {
          ++len;
          cur.x += sign * d.x;
          cur.y += sign * d.y;
        }
      }
      if (len >= winLen) {
        return true;
      }
    }
    return false;
  }
  bool hasFive(bool isBlack) const {
    for (int y = 0; y < size; ++y) {
      for (int x = 0; x < size; ++x) {
        const Coord c{x, y};
        if (has(c, isBlack) && wins(c, isBlack)) {
          return true;
        }
      }
    }
    return false;
  }
};

// An "open three": three in a row with both ends empty (can become an open
// four next move -> unanswerable).  A "four": four in a row with one empty
// end (or gap) — must be blocked immediately.
struct Threat {
  Coord point;      // the cell White must take (or one of them)
  int kind = 0;     // 2 = double threat point (win on next move either way)
                    // 1 = four (must block)
                    // 0 = open three (should block)
};

// Find all Black threats.  For each 5-window, count black stones and empty
// cells: 4 black + 1 empty -> the empty is a four point; 3 black + 2 empty
// with both empties as ends -> open three points.
std::vector<Threat> blackThreats(const Board& b) {
  std::vector<Threat> result;
  constexpr std::array<Coord, 4> dirs{{{1, 0}, {0, 1}, {1, 1}, {1, -1}}};
  for (int y = 0; y < size; ++y) {
    for (int x = 0; x < size; ++x) {
      const Coord start{x, y};
      for (const Coord d : dirs) {
        std::vector<Coord> cells;
        std::vector<Coord> empties;
        bool broken = false;
        for (int i = 0; i < winLen; ++i) {
          const Coord c{start.x + i * d.x, start.y + i * d.y};
          if (!b.inside(c)) {
            broken = true;
            break;
          }
          cells.push_back(c);
          if (b.empty(c)) {
            empties.push_back(c);
          } else if (!b.has(c, true)) {
            broken = true;  // white stone inside the window
            break;
          }
        }
        if (broken) {
          continue;
        }
        const int blacks = winLen - static_cast<int>(empties.size());
        if (blacks == 4 && empties.size() == 1) {
          result.push_back({empties[0], 1});
        } else if (blacks == 3 && empties.size() == 2) {
          // open three: both ends empty and the three are consecutive
          result.push_back({empties[0], 0});
          result.push_back({empties[1], 0});
        }
      }
    }
  }
  // Deduplicate by (point, kind) keeping the max kind.
  std::vector<Threat> merged;
  for (const Threat& t : result) {
    bool found = false;
    for (Threat& m : merged) {
      if (m.point == t.point) {
        m.kind = std::max(m.kind, t.kind);
        found = true;
        break;
      }
    }
    if (!found) {
      merged.push_back(t);
    }
  }
  return merged;
}

// Black move: pick the best greedy attacking move.
Coord blackMove(const Board& b) {
  const std::vector<Coord> moves = b.empties();
  Coord best = moves.front();
  int bestScore = -1;
  for (const Coord m : moves) {
    int score = 0;
    if (b.wins(m, true)) {
      score = 100000;
    } else {
      Board nb = b;
      nb.set(m, true);
      const std::vector<Threat> threats = blackThreats(nb);
      int fours = 0;
      int openThrees = 0;
      for (const Threat& t : threats) {
        if (t.kind >= 1) {
          ++fours;
        } else {
          ++openThrees;
        }
      }
      score = 10000 * fours + 1000 * openThrees;
    }
    // center preference
    score += 50 - 5 * ((m.x - 3) * (m.x - 3) + (m.y - 3) * (m.y - 3));
    if (score > bestScore) {
      bestScore = score;
      best = m;
    }
  }
  return best;
}

// White move: respond to the strongest Black threat; if two distinct
// unanswerable threats exist, return false (White lost).
bool whiteMove(Board& b) {
  const std::vector<Threat> threats = blackThreats(b);
  int fours = 0;
  int openThrees = 0;
  Coord fourPoint{};
  Coord threePoint{};
  for (const Threat& t : threats) {
    if (t.kind >= 1) {
      ++fours;
      fourPoint = t.point;
    } else {
      ++openThrees;
      threePoint = t.point;
    }
  }
  if (fours >= 2) {
    return false;  // two fours cannot both be blocked
  }
  if (fours == 1) {
    b.set(fourPoint, false);
    return true;
  }
  // open-three threats: if Black has an open three, White must block one end
  // (blocking an open three end is enough if it is the only one; two open
  // threes is a double threat -> White must block both, impossible)
  if (openThrees >= 2) {
    // Two distinct open threes: block one end of each if possible via one
    // move only if they share the point; otherwise White loses here unless
    // the moves overlap.
    int distinct = 0;
    Coord first{};
    for (const Threat& t : threats) {
      if (t.kind == 0 && (distinct == 0 || !(t.point == first))) {
        if (distinct == 1) {
          return false;  // two distinct open three ends
        }
        first = t.point;
        ++distinct;
      }
    }
  }
  if (openThrees == 1) {
    b.set(threePoint, false);
    return true;
  }
  // no threats: play center-ish
  const std::vector<Coord> moves = b.empties();
  Coord best = moves.front();
  int bestScore = -1;
  for (const Coord m : moves) {
    const int score =
        50 - 5 * ((m.x - 3) * (m.x - 3) + (m.y - 3) * (m.y - 3));
    if (score > bestScore) {
      bestScore = score;
      best = m;
    }
  }
  b.set(best, false);
  return true;
}

int simulate(bool verbose) {
  Board b;
  // Black first at center, then alternate.
  b.set({3, 3}, true);
  for (int ply = 1; ply < size * size; ++ply) {
    if (b.hasFive(true)) {
      if (verbose) {
        std::cout << "BLACK WINS at ply " << ply << "\n";
      }
      return 1;
    }
    if (ply % 2 == 1) {
      // White's turn
      if (!whiteMove(b)) {
        if (verbose) {
          std::cout << "WHITE CANNOT DEFEND at ply " << ply << "\n";
        }
        return 1;
      }
      if (b.hasFive(false)) {
        if (verbose) {
          std::cout << "WHITE WINS at ply " << ply << "\n";
        }
        return 0;
      }
    } else {
      const Coord m = blackMove(b);
      b.set(m, true);
    }
    if (b.empties().empty()) {
      if (verbose) {
        std::cout << "DRAW at ply " << ply << "\n";
      }
      return 0;
    }
  }
  if (verbose) {
    std::cout << "DRAW\n";
  }
  return 0;
}

}  // namespace

int main(int argc, char** argv) {
  bool verbose = argc > 1 && std::string(argv[1]) == "-v";
  // Try several first-move variations to get a broader picture.
  int blackWins = 0;
  int whiteHolds = 0;
  const std::array<Coord, 3> openings{{{3, 3}, {2, 2}, {3, 2}}};
  for (const Coord& open : openings) {
    Board b;
    b.set(open, true);
    int result = 0;  // 0 = hold/draw, 1 = black wins
    for (int ply = 1; ply < size * size; ++ply) {
      if (b.hasFive(true)) {
        result = 1;
        break;
      }
      if (ply % 2 == 1) {
        if (!whiteMove(b)) {
          result = 1;
          break;
        }
        if (b.hasFive(false)) {
          break;
        }
      } else {
        b.set(blackMove(b), true);
      }
      if (b.empties().empty()) {
        break;
      }
    }
    if (result == 1) {
      ++blackWins;
      if (verbose) {
        std::cout << "opening (" << open.x << "," << open.y
                  << "): BLACK WINS\n";
      }
    } else {
      ++whiteHolds;
      if (verbose) {
        std::cout << "opening (" << open.x << "," << open.y
                  << "): White holds\n";
      }
    }
  }
  std::cout << "black_wins=" << blackWins << " white_holds=" << whiteHolds
            << "\n";
  return 0;
}
