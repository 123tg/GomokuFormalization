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
  explicit PairingSolver(int size)
      : size_(size), cellCount_(size * size), windows_(allWindows(size)) {
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
    return search(0);
  }

  const std::vector<Pair>& solution() const {
    return selected_;
  }

 private:
  struct Candidate {
    int first = 0;
    int second = 0;
    int coverage = 0;
  };

  bool search(std::uint64_t nodes) {
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

  // Cells of `line` that are not yet in any pair.
  Bits unassignedCells(int line) const {
    Bits result = 0;
    for (int i = 0; i < winLength; ++i) {
      const int cell = indexOf(step(windows_[line], i));
      if (partner_[cell] == -1) {
        result |= Bits{1} << cell;
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

  // Pair two cells that see exactly the same set of uncovered lines.
  std::optional<Pair> equalFreeEdgePair() const {
    for (int first = 0; first < cellCount_; ++first) {
      if (partner_[first] != -1) {
        continue;
      }
      const std::vector<int> firstEdges = freeEdgesAt(first);
      if (firstEdges.empty()) {
        continue;
      }
      for (int second = first + 1; second < cellCount_; ++second) {
        if (partner_[second] != -1) {
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
        if (partner_[first] == -1 && partner_[second] == -1) {
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
  std::vector<Window> windows_;
  std::vector<int> activeLines_;
  std::array<std::vector<int>, 64> linesByCell_{};
  std::array<bool, 64> covered_{};
  std::array<int, 64> partner_{};
  std::vector<Pair> selected_;
};

}  // namespace

int main(int argc, char** argv) {
  int size = 7;
  if (argc > 1) {
    size = std::stoi(argv[1]);
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
