// find_pairing.cpp — find a pairing strategy for the 7x7 empty board.
//
// A "pairing" is a set of disjoint cell pairs such that every length-5
// winning window (all four directions) contains at least one complete pair.
// If such a pairing exists, the second player can answer every first-player
// move inside a pair by taking the partner cell; the first player can then
// never occupy both cells of any pair, hence never completes a five.
//
// Algorithm (ported from the project's earlier pairing search): greedy
// forced pairs (a line with exactly two unassigned cells forces that pair),
// the equal-free-edge heuristic, and minimum-remaining-values branching.
// The search is complete; limits here only bound the effort, never the
// meaning of a found solution.
//
// This tool only SEARCHES for the pairing.  The Lean side re-verifies the
// exported pairing with its own decidable checker and proves the strategy
// sound; this tool is untrusted.
//
// Usage: find_pairing [boardSize]   (default 7)
// Output format (one pair per line):  x1 y1 x2 y2

#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <limits>
#include <optional>
#include <string>
#include <vector>

namespace {

constexpr int winLength = 5;
using Bits = std::uint64_t;

struct Coord {
  int x = 0;
  int y = 0;
  friend bool operator==(Coord lhs, Coord rhs) {
    return lhs.x == rhs.x && lhs.y == rhs.y;
  }
};

struct Pair {
  int first = 0;
  int second = 0;
};

struct Window {
  Coord start;
  int dx = 0;
  int dy = 0;
};

std::vector<Window> allWindows(int size) {
  std::vector<Window> windows;
  for (int y = 0; y < size; ++y) {
    for (int x = 0; x <= size - winLength; ++x) {
      windows.push_back({{x, y}, 1, 0});
    }
  }
  for (int x = 0; x < size; ++x) {
    for (int y = 0; y <= size - winLength; ++y) {
      windows.push_back({{x, y}, 0, 1});
    }
  }
  for (int y = 0; y <= size - winLength; ++y) {
    for (int x = 0; x <= size - winLength; ++x) {
      windows.push_back({{x, y}, 1, 1});
    }
  }
  for (int y = winLength - 1; y < size; ++y) {
    for (int x = 0; x <= size - winLength; ++x) {
      windows.push_back({{x, y}, 1, -1});
    }
  }
  return windows;
}

class PairingSolver {
 public:
  explicit PairingSolver(int size, Bits maker = 0, Bits breaker = 0)
      : size_(size), cellCount_(size * size), windows_(allWindows(size)),
        maker_(maker), breaker_(breaker) {
    lineCount_ = static_cast<int>(windows_.size());
    std::fill(covered_.begin(), covered_.end(), false);
    std::fill(partner_.begin(), partner_.end(), -1);
    for (int line = 0; line < lineCount_; ++line) {
      activeLines_.push_back(line);
    }
    for (int line = 0; line < lineCount_; ++line) {
      for (int i = 0; i < winLength; ++i) {
        const Coord c = step(windows_[line], i);
        linesByCell_[indexOf(c)].push_back(line);
      }
    }
  }

  bool solve() {
    selected_.clear();
    std::fill(covered_.begin(), covered_.end(), false);
    std::fill(partner_.begin(), partner_.end(), -1);
    // 已含白棋（breaker）的窗口无需覆盖（黑棋永远无法成五）。
    for (int line = 0; line < lineCount_; ++line) {
      if ((windowMask(line) & breaker_) != 0) {
        covered_[line] = true;
      }
    }
    return search(0);
  }

  const std::vector<Pair>& solution() const {
    return selected_;
  }

  std::uint64_t nodesUsed() const {
    return statsNodes;
  }

  static int cellOf(int x, int y, int size) {
    return y * size + x;
  }

 private:
  struct Candidate {
    int first = 0;
    int second = 0;
    int coverage = 0;
  };

  bool search(std::uint64_t nodes) {
    ++statsNodes;
    if (nodes > 500'000'000) {
      return false;
    }
    // Greedy forced pairs: a line with exactly two unassigned cells forces
    // that pair; a line with fewer than two is impossible.
    while (true) {
      std::optional<Pair> forced;
      for (const int line : activeLines_) {
        if (covered_[line]) {
          continue;
        }
        const Bits freeCells = unassignedCells(line);
        const int freeCount = __builtin_popcountll(freeCells);
        if (freeCount < 2) {
          return false;
        }
        if (freeCount == 2) {
          const int first = __builtin_ctzll(freeCells);
          const int second = __builtin_ctzll(
              freeCells & ~(Bits{1} << first));
          forced = Pair{first, second};
          break;
        }
      }
      if (!forced.has_value()) {
        forced = equalFreeEdgePair();
      }
      if (!forced.has_value()) {
        break;
      }
      assignPair(*forced);
    }

    // Minimum remaining values: branch on the uncovered line with the fewest
    // candidate pairs.
    int chosenLine = -1;
    std::vector<Candidate> chosenCandidates;
    std::size_t smallestCount = std::numeric_limits<std::size_t>::max();
    for (const int line : activeLines_) {
      if (covered_[line]) {
        continue;
      }
      const std::vector<Candidate> candidates = candidatesFor(line);
      if (candidates.empty()) {
        return false;
      }
      if (candidates.size() < smallestCount) {
        smallestCount = candidates.size();
        chosenLine = line;
        chosenCandidates = candidates;
        if (smallestCount == 1) {
          break;
        }
      }
    }
    if (chosenLine == -1) {
      return true;  // every line is covered
    }

    std::stable_sort(chosenCandidates.begin(), chosenCandidates.end(),
        [](const Candidate& left, const Candidate& right) {
          return left.coverage > right.coverage;
        });
    for (const Candidate& candidate : chosenCandidates) {
      assignPair({candidate.first, candidate.second});
      if (search(nodes + 1)) {
        return true;
      }
      undoPair();
    }
    return false;
  }

  int indexOf(Coord c) const {
    return c.y * size_ + c.x;
  }

  Coord step(const Window& window, int index) const {
    return {window.start.x + index * window.dx,
            window.start.y + index * window.dy};
  }

  // Cells of `line` that are free (not occupied, not yet in any pair).
  Bits unassignedCells(int line) const {
    Bits result = 0;
    for (int i = 0; i < winLength; ++i) {
      const int cell = indexOf(step(windows_[line], i));
      const Bits mask = Bits{1} << cell;
      if (partner_[cell] == -1 && (maker_ & mask) == 0 &&
          (breaker_ & mask) == 0) {
        result |= mask;
      }
    }
    return result;
  }

  // Lines through `cell` that are still uncovered.
  std::vector<int> freeEdgesAt(int cell) const {
    std::vector<int> result;
    for (const int line : linesByCell_[cell]) {
      if (!covered_[line]) {
        result.push_back(line);
      }
    }
    return result;
  }

  // Pair two free cells that see exactly the same set of uncovered lines.
  std::optional<Pair> equalFreeEdgePair() const {
    for (int first = 0; first < cellCount_; ++first) {
      const Bits fmask = Bits{1} << first;
      if (partner_[first] != -1 || (maker_ & fmask) != 0 ||
          (breaker_ & fmask) != 0) {
        continue;
      }
      const std::vector<int> firstEdges = freeEdgesAt(first);
      if (firstEdges.empty()) {
        continue;
      }
      for (int second = first + 1; second < cellCount_; ++second) {
        const Bits smask = Bits{1} << second;
        if (partner_[second] != -1 || (maker_ & smask) != 0 ||
            (breaker_ & smask) != 0) {
          continue;
        }
        if (firstEdges == freeEdgesAt(second)) {
          return Pair{first, second};
        }
      }
    }
    return std::nullopt;
  }

  std::vector<Candidate> candidatesFor(int line) const {
    std::vector<Candidate> result;
    for (int i = 0; i < winLength; ++i) {
      for (int j = i + 1; j < winLength; ++j) {
        const int first = indexOf(step(windows_[line], i));
        const int second = indexOf(step(windows_[line], j));
        const Bits fmask = Bits{1} << first;
        const Bits smask = Bits{1} << second;
        if (partner_[first] == -1 && partner_[second] == -1 &&
            (maker_ & fmask) == 0 && (breaker_ & fmask) == 0 &&
            (maker_ & smask) == 0 && (breaker_ & smask) == 0) {
          int coverage = 0;
          for (const int other : activeLines_) {
            if (covered_[other]) {
              continue;
            }
            bool firstInside = false;
            bool secondInside = false;
            for (int k = 0; k < winLength; ++k) {
              const int cell = indexOf(step(windows_[other], k));
              firstInside = firstInside || cell == first;
              secondInside = secondInside || cell == second;
            }
            if (firstInside && secondInside) {
              ++coverage;
            }
          }
          result.push_back(Candidate{first, second, coverage});
        }
      }
    }
    return result;
  }

  void assignPair(Pair pair) {
    partner_[pair.first] = pair.second;
    partner_[pair.second] = pair.first;
    selected_.push_back(pair);
    const Bits pairMask = (Bits{1} << pair.first) | (Bits{1} << pair.second);
    for (const int line : activeLines_) {
      if (!covered_[line] &&
          (windowMask(line) & pairMask) == pairMask) {
        covered_[line] = true;
      }
    }
  }

  void undoPair() {
    const Pair pair = selected_.back();
    selected_.pop_back();
    partner_[pair.first] = -1;
    partner_[pair.second] = -1;
    for (const int line : activeLines_) {
      if (covered_[line]) {
        // Recompute: a line stays covered only if some OTHER pair covers it.
        bool stillCovered = false;
        for (const Pair& other : selected_) {
          const Bits pairMask =
              (Bits{1} << other.first) | (Bits{1} << other.second);
          if ((windowMask(line) & pairMask) == pairMask) {
            stillCovered = true;
            break;
          }
        }
        covered_[line] = stillCovered;
      }
    }
  }

  Bits windowMask(int line) const {
    Bits mask = 0;
    for (int i = 0; i < winLength; ++i) {
      mask |= Bits{1} << indexOf(step(windows_[line], i));
    }
    return mask;
  }

  int size_ = 7;
  int cellCount_ = 49;
  int lineCount_ = 0;
  std::uint64_t statsNodes = 0;
  Bits maker_ = 0;
  Bits breaker_ = 0;
  std::vector<Window> windows_;
  std::vector<int> activeLines_;
  std::array<std::vector<int>, 64> linesByCell_{};
  std::array<bool, 64> covered_{};
  std::array<int, 64> partner_{};
  std::vector<Pair> selected_;
};

}  // namespace

// Sweep mode: for every black first move m, find a white response r such that
// the remaining board (with black m, white r) admits a covering pairing.
// Prints m r and the pairs; exits non-zero if any m has no solution.
int sweep(int size) {
  const int cells = size * size;
  for (int m = 0; m < cells; ++m) {
    bool solved = false;
    // Try white responses in a useful order: center first, then by distance.
    std::vector<int> order;
    const int cy = size / 2;
    const int cx = size / 2;
    for (int r = 0; r < cells; ++r) {
      order.push_back(r);
    }
    std::stable_sort(order.begin(), order.end(), [&](int lhs, int rhs) {
      const int lx = lhs % size;
      const int ly = lhs / size;
      const int rx = rhs % size;
      const int ry = rhs / size;
      const int ld = (lx - cx) * (lx - cx) + (ly - cy) * (ly - cy);
      const int rd = (rx - cx) * (rx - cx) + (ry - cy) * (ry - cy);
      if (ld != rd) {
        return ld < rd;
      }
      return lhs < rhs;
    });
    for (const int r : order) {
      if (r == m) {
        continue;
      }
      PairingSolver solver(size, Bits{1} << m, Bits{1} << r);
      if (solver.solve()) {
        const std::vector<Pair>& solution = solver.solution();
        const Coord a{m % size, m / size};
        const Coord b{r % size, r / size};
        std::cout << "m=" << a.x << " " << a.y << " r=" << b.x << " " << b.y
                  << " pairs=" << solution.size() << "\n";
        for (const Pair& pair : solution) {
          const Coord p1{pair.first % size, pair.first / size};
          const Coord p2{pair.second % size, pair.second / size};
          std::cout << "  " << p1.x << " " << p1.y << " " << p2.x << " "
                    << p2.y << "\n";
        }
        solved = true;
        break;
      }
    }
    if (!solved) {
      const Coord a{m % size, m / size};
      std::cerr << "no solution for black first move " << a.x << " " << a.y
                << "\n";
      return 1;
    }
  }
  return 0;
}

// Single-first-move test mode: for black first move (mx, my), try every
// white response and report which ones admit a covering pairing (depth-2
// layered pairing feasibility).
int testFirstMove(int size, int mx, int my) {
  const int m = my * size + mx;
  int successes = 0;
  for (int r = 0; r < size * size; ++r) {
    if (r == m) {
      continue;
    }
    PairingSolver solver(size, Bits{1} << m, Bits{1} << r);
    const bool ok = solver.solve();
    const Coord b{r % size, r / size};
    std::cout << "r=" << b.x << " " << b.y << " ok=" << (ok ? "yes" : "no")
              << " nodes=" << solver.nodesUsed()
              << " pairs=" << (ok ? solver.solution().size() : 0) << "\n";
    if (ok) {
      ++successes;
      const std::vector<Pair>& solution = solver.solution();
      for (const Pair& pair : solution) {
        const Coord p1{pair.first % size, pair.first / size};
        const Coord p2{pair.second % size, pair.second / size};
        std::cout << "  " << p1.x << " " << p1.y << " " << p2.x << " "
                  << p2.y << "\n";
      }
      break;  // 只报告第一个成功回应及其配对
    }
  }
  std::cout << "successes=" << successes << "\n";
  return successes > 0 ? 0 : 1;
}

int main(int argc, char** argv) {
  int size = 7;
  bool sweepMode = false;
  bool testMode = false;
  int mx = 3;
  int my = 3;
  for (int i = 1; i < argc; ++i) {
    const std::string arg = argv[i];
    if (arg == "--sweep") {
      sweepMode = true;
    } else if (arg == "--test") {
      testMode = true;
      if (i + 2 < argc) {
        mx = std::stoi(argv[++i]);
        my = std::stoi(argv[++i]);
      }
    } else {
      size = std::stoi(arg);
    }
  }
  if (sweepMode) {
    return sweep(size);
  }
  if (testMode) {
    return testFirstMove(size, mx, my);
  }
  PairingSolver solver(size);
  if (!solver.solve()) {
    std::cerr << "no pairing found for board " << size << "\n";
    return 1;
  }
  const std::vector<Pair>& solution = solver.solution();
  std::cout << "pairs=" << solution.size() << "\n";
  for (const Pair& pair : solution) {
    const Coord a{pair.first % size, pair.first / size};
    const Coord b{pair.second % size, pair.second / size};
    std::cout << a.x << " " << a.y << " " << b.x << " " << b.y << "\n";
  }
  return 0;
}
