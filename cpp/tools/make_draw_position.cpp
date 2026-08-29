// make_draw_position.cpp — build a reachable 7x7 position with 21 black +
// 21 white stones (black to move) where EVERY length-5 window contains at
// least one black AND at least one white stone.  Such a position is a forced
// draw: neither player can ever complete a window, so both defense searches
// trivially succeed and `standardDraw_of_mutualDefense` applies in Lean.
//
// Start from the full checkerboard (rows BWBWBWB; no five anywhere), then
// greedily remove black cells while preserving the both-colors property.
#include <algorithm>
#include <cstdint>
#include <iostream>
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

}  // namespace

int main() {
  const std::vector<Window> windows = allWindows();
  std::vector<bool> black(size * size, false);
  std::vector<bool> white(size * size, false);
  // Pattern: black iff ((x + 2y) mod 4) in {0,1}.  Rows, columns and both
  // diagonals then have max run 2, so every length-5 window contains both
  // colors (verified below).
  for (int y = 0; y < size; ++y) {
    for (int x = 0; x < size; ++x) {
      const int c = y * size + x;
      const int v = (x + 2 * y) % 4;
      if (v == 0 || v == 1) black[c] = true;
      else white[c] = true;
    }
  }
  const auto countBlack = [&](const std::vector<bool>& b) {
    return std::count(b.begin(), b.end(), true);
  };
  std::cout << "initial: black=" << countBlack(black)
            << " white=" << std::count(white.begin(), white.end(), true)
            << " bothColors="
            << (bothColorsInEveryWindow(windows, black, white) ? "yes" : "no")
            << "\n";

  // Greedily remove stones (target 21 black + 21 white, i.e. 4 black and
  // 3 white removals) while preserving the both-colors property.
  int targetBlack = 21;
  int targetWhite = 21;
  int guard = 0;
  while (countBlack(black) > targetBlack && guard++ < 100) {
    bool removed = false;
    for (int c = 0; c < size * size; ++c) {
      if (!black[c]) continue;
      black[c] = false;
      if (bothColorsInEveryWindow(windows, black, white)) {
        std::cout << "removed B (" << c % size << "," << c / size << ")\n";
        removed = true;
        break;
      }
      black[c] = true;
    }
    if (!removed) {
      std::cout << "stuck removing black\n";
      break;
    }
  }
  guard = 0;
  while (std::count(white.begin(), white.end(), true) > targetWhite &&
         guard++ < 100) {
    bool removed = false;
    for (int c = 0; c < size * size; ++c) {
      if (!white[c]) continue;
      white[c] = false;
      if (bothColorsInEveryWindow(windows, black, white)) {
        std::cout << "removed W (" << c % size << "," << c / size << ")\n";
        removed = true;
        break;
      }
      white[c] = true;
    }
    if (!removed) {
      std::cout << "stuck removing white\n";
      break;
    }
  }
  std::cout << "final: black=" << countBlack(black)
            << " white=" << std::count(white.begin(), white.end(), true)
            << " bothColors="
            << (bothColorsInEveryWindow(windows, black, white) ? "yes" : "no")
            << "\n";
  for (int y = 0; y < size; ++y) {
    for (int x = 0; x < size; ++x) {
      const int c = y * size + x;
      std::cout << (black[c] ? 'B' : (white[c] ? 'W' : '.'));
    }
    std::cout << "\n";
  }
  return 0;
}
