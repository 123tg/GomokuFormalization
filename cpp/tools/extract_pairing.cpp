// extract_pairing.cpp — print the covering pairing for a fixed 7x7 position
// with occupied cells (maker = black stones, breaker = white stones).
// Usage: extract_pairing mx my ...  (pairs of x y: black stones first, then white)
#include <array>
#include <cstdint>
#include <iostream>
#include <limits>
#include <string>
#include <vector>

namespace {

using Bits = std::uint64_t;
constexpr int size = 7;

struct Coord {
  int x;
  int y;
};

int idx(int x, int y) { return y * size + x; }

struct Window {
  int start;
  int dx;
  int dy;
};

std::vector<Window> allWindows() {
  std::vector<Window> windows;
  for (int y = 0; y < size; ++y)
    for (int x = 0; x <= size - 5; ++x) windows.push_back({idx(x, y), 1, 0});
  for (int x = 0; x < size; ++x)
    for (int y = 0; y <= size - 5; ++y) windows.push_back({idx(x, y), 0, 1});
  for (int y = 0; y <= size - 5; ++y)
    for (int x = 0; x <= size - 5; ++x) windows.push_back({idx(x, y), 1, 1});
  for (int y = 4; y < size; ++y)
    for (int x = 0; x <= size - 5; ++x) windows.push_back({idx(x, y), 1, -1});
  return windows;
}

int cellAt(const Window& w, int i) {
  return idx((w.start % size) + i * w.dx, (w.start / size) + i * w.dy);
}

// Minimal covering-pairing search: pairs of free cells such that every window
// without a white stone contains a full pair.
bool findPairing(Bits maker, Bits breaker, std::vector<std::pair<int, int>>& pairs) {
  const std::vector<Window> windows = allWindows();
  const int lineCount = static_cast<int>(windows.size());
  std::vector<bool> covered(lineCount, false);
  for (int line = 0; line < lineCount; ++line) {
    bool hasDefender = false;
    for (int i = 0; i < 5; ++i) {
      if ((breaker & (Bits{1} << cellAt(windows[line], i))) != 0) {
        hasDefender = true;
        break;
      }
    }
    if (hasDefender) covered[line] = true;
  }
  std::array<int, 49> partner{};
  partner.fill(-1);
  const auto freeCell = [&](int c) {
    return partner[c] == -1 && (maker & (Bits{1} << c)) == 0 &&
           (breaker & (Bits{1} << c)) == 0;
  };
  const auto unassigned = [&](int line) {
    Bits result = 0;
    for (int i = 0; i < 5; ++i) {
      const int c = cellAt(windows[line], i);
      if (freeCell(c)) result |= Bits{1} << c;
    }
    return result;
  };
  const auto covers = [&](int line, const std::pair<int, int>& pair) {
    bool in1 = false;
    bool in2 = false;
    for (int i = 0; i < 5; ++i) {
      const int c = cellAt(windows[line], i);
      in1 = in1 || c == pair.first;
      in2 = in2 || c == pair.second;
    }
    return in1 && in2;
  };
  std::uint64_t nodes = 0;
  std::vector<std::pair<int, int>> selected;
  bool found = false;
  std::vector<std::pair<int, int>> solution;
  const auto search = [&](const auto& self) -> bool {
    if (nodes++ > 2'000'000) return false;
    while (true) {
      bool any = false;
      for (int line = 0; line < lineCount; ++line) {
        if (covered[line]) continue;
        const Bits free = unassigned(line);
        const int freeCount = __builtin_popcountll(free);
        if (freeCount < 2) return false;
        if (freeCount == 2) {
          const int a = __builtin_ctzll(free);
          const int b = __builtin_ctzll(free & ~(Bits{1} << a));
          partner[a] = b;
          partner[b] = a;
          selected.push_back({a, b});
          for (int l = 0; l < lineCount; ++l)
            if (!covered[l] && covers(l, {a, b})) covered[l] = true;
          any = true;
          break;
        }
      }
      if (!any) break;
    }
    int chosenLine = -1;
    std::vector<std::pair<int, int>> candidates;
    std::size_t bestCount = std::numeric_limits<std::size_t>::max();
    for (int line = 0; line < lineCount; ++line) {
      if (covered[line]) continue;
      std::vector<std::pair<int, int>> cand;
      for (int i = 0; i < 5; ++i) {
        for (int j = i + 1; j < 5; ++j) {
          const int a = cellAt(windows[line], i);
          const int b = cellAt(windows[line], j);
          if (freeCell(a) && freeCell(b)) cand.push_back({a, b});
        }
      }
      if (cand.empty()) return false;
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
      for (int l = 0; l < lineCount; ++l)
        if (!covered[l] && covers(l, cand)) covered[l] = true;
      if (self(self)) return true;
      selected.pop_back();
      partner[cand.first] = -1;
      partner[cand.second] = -1;
      for (int l = 0; l < lineCount; ++l) {
        if (covered[l]) {
          bool still = false;
          for (const auto& s : selected)
            if (covers(l, s)) {
              still = true;
              break;
            }
          covered[l] = still;
        }
      }
    }
    return false;
  };
  found = search(search);
  if (found) pairs = solution;
  return found;
}

}  // namespace

int main(int argc, char** argv) {
  if (argc < 5 || (argc - 1) % 4 != 0) {
    std::cerr << "usage: extract_pairing bx0 by0 bx1 by1 ... wx0 wy0 ...\n";
    return 1;
  }
  Bits maker = 0;
  Bits breaker = 0;
  int n = (argc - 1) / 4;  // number of black stones (= number of white stones)
  for (int i = 0; i < n; ++i) {
    const int x = std::stoi(argv[1 + 2 * i]);
    const int y = std::stoi(argv[2 + 2 * i]);
    maker |= Bits{1} << idx(x, y);
  }
  for (int i = 0; i < n; ++i) {
    const int x = std::stoi(argv[1 + 2 * (i + n)]);
    const int y = std::stoi(argv[2 + 2 * (i + n)]);
    breaker |= Bits{1} << idx(x, y);
  }
  std::vector<std::pair<int, int>> pairs;
  if (!findPairing(maker, breaker, pairs)) {
    std::cerr << "no pairing\n";
    return 1;
  }
  std::cout << "pairs=" << pairs.size() << "\n";
  for (const auto& pr : pairs) {
    std::cout << pr.first % size << " " << pr.first / size << " " << pr.second % size
              << " " << pr.second / size << "\n";
  }
  return 0;
}
