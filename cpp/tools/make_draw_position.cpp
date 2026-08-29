// make_draw_position.cpp — build reachable 7x7 positions with 21 black +
// 21 white stones (black to move, 7 empty cells) where EVERY length-5
// window contains at least one black AND at least one white stone.  Such
// positions are forced draws: neither player can ever complete a window, so
// both defense searches trivially succeed and `standardDraw_of_mutualDefense`
// applies in Lean.
//
// Usage: make_draw_position [--seed N] [--count K] [--out FILE]
//   --seed N   shuffle removal order with this seed (default 1)
//   --count K  emit K distinct positions (seeds N..N+K-1)
//   --out FILE write the LAST position in solver text format to FILE
//
// Start from the period-4 pattern (black iff (x + 2y) mod 4 in {0,1}), which
// has max run 2 in every row/column/diagonal, then greedily remove stones
// (4 black + 3 white) while preserving the both-colors property.
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <string>
#include <vector>

namespace {

constexpr int size = 7;

struct Window {
  int start;
  int dx;
  int dy;
};

std::vector<Window> allWindows() {
  std::vector<Window> windows;
  for (int y = 0; y < size; ++y)
    for (int x = 0; x <= size - 5; ++x) windows.push_back({y * size + x, 1, 0});
  for (int x = 0; x < size; ++x)
    for (int y = 0; y <= size - 5; ++y) windows.push_back({y * size + x, 0, 1});
  for (int y = 0; y <= size - 5; ++y)
    for (int x = 0; x <= size - 5; ++x) windows.push_back({y * size + x, 1, 1});
  for (int y = 4; y < size; ++y)
    for (int x = 0; x <= size - 5; ++x) windows.push_back({y * size + x, 1, -1});
  return windows;
}

int cellAt(const Window& w, int i) {
  return (w.start % size) + i * w.dx + ((w.start / size) + i * w.dy) * size;
}

// True iff every window contains at least one black and at least one white.
bool bothColorsInEveryWindow(const std::vector<Window>& windows,
                             const std::vector<bool>& black,
                             const std::vector<bool>& white) {
  for (const Window& w : windows) {
    bool hasBlack = false;
    bool hasWhite = false;
    for (int i = 0; i < 5; ++i) {
      const int c = cellAt(w, i);
      hasBlack = hasBlack || black[c];
      hasWhite = hasWhite || white[c];
    }
    if (!hasBlack || !hasWhite) return false;
  }
  return true;
}

struct Position {
  std::vector<bool> black;
  std::vector<bool> white;
};

Position makePosition(std::uint64_t seed) {
  const std::vector<Window> windows = allWindows();
  Position pos;
  pos.black.assign(size * size, false);
  pos.white.assign(size * size, false);
  for (int y = 0; y < size; ++y) {
    for (int x = 0; x < size; ++x) {
      const int c = y * size + x;
      const int v = (x + 2 * y) % 4;
      if (v == 0 || v == 1) pos.black[c] = true;
      else pos.white[c] = true;
    }
  }
  std::vector<int> order(size * size);
  for (int c = 0; c < size * size; ++c) order[c] = c;
  std::mt19937 rng(static_cast<std::uint32_t>(seed));
  std::shuffle(order.begin(), order.end(), rng);

  // Greedily remove black stones down to 21, preserving both-colors.
  int removedBlack = 0;
  for (const int c : order) {
    if (removedBlack == 4) break;
    if (!pos.black[c]) continue;
    pos.black[c] = false;
    if (bothColorsInEveryWindow(windows, pos.black, pos.white)) {
      ++removedBlack;
    } else {
      pos.black[c] = true;
    }
  }
  // Greedily remove white stones down to 21, preserving both-colors.
  int removedWhite = 0;
  for (const int c : order) {
    if (removedWhite == 3) break;
    if (!pos.white[c]) continue;
    pos.white[c] = false;
    if (bothColorsInEveryWindow(windows, pos.black, pos.white)) {
      ++removedWhite;
    } else {
      pos.white[c] = true;
    }
  }
  if (removedBlack != 4 || removedWhite != 3 ||
      !bothColorsInEveryWindow(windows, pos.black, pos.white)) {
    std::cerr << "seed " << seed << ": failed to build position (b="
              << removedBlack << " w=" << removedWhite << ")\n";
    return {};
  }
  return pos;
}

void printBoard(std::ostream& out, const Position& pos) {
  for (int y = 0; y < size; ++y) {
    for (int x = 0; x < size; ++x) {
      const int c = y * size + x;
      out << (pos.black[c] ? 'B' : (pos.white[c] ? 'W' : '.'));
    }
    out << "\n";
  }
}

}  // namespace

int main(int argc, char** argv) {
  std::uint64_t seed = 1;
  int count = 1;
  std::string outPath;
  for (int i = 1; i < argc; ++i) {
    const std::string arg = argv[i];
    if (arg == "--seed" && i + 1 < argc) {
      seed = std::stoull(argv[++i]);
    } else if (arg == "--count" && i + 1 < argc) {
      count = std::stoi(argv[++i]);
    } else if (arg == "--out" && i + 1 < argc) {
      outPath = argv[++i];
    } else {
      std::cerr << "usage: make_draw_position [--seed N] [--count K] [--out FILE]\n";
      return 1;
    }
  }
  Position last;
  for (int k = 0; k < count; ++k) {
    last = makePosition(seed + static_cast<std::uint64_t>(k));
    if (last.black.empty()) return 1;
    std::cout << "=== seed " << (seed + k) << " ===" << "\n";
    printBoard(std::cout, last);
  }
  if (!outPath.empty()) {
    std::ofstream out(outPath);
    if (!out) {
      std::cerr << "cannot write " << outPath << "\n";
      return 1;
    }
    out << "turn black\n";
    out << "target black\n";
    printBoard(out, last);
    std::cout << "wrote " << outPath << "\n";
  }
  return 0;
}
