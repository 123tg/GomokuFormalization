#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <string_view>
#include <vector>

namespace {

using Bits = std::uint32_t;

constexpr int boardSize = 5;
constexpr int cellCount = boardSize * boardSize;
constexpr Bits fullBoard = (Bits{1} << cellCount) - 1;

constexpr int indexOf(int x, int y) { return y * boardSize + x; }
constexpr Bits bitAt(int x, int y) { return Bits{1} << indexOf(x, y); }

constexpr std::array<Bits, 12> makeWinningMasks() {
  std::array<Bits, 12> masks{};
  int next = 0;
  for (int y = 0; y < boardSize; ++y) {
    Bits row = 0;
    for (int x = 0; x < boardSize; ++x) {
      row |= bitAt(x, y);
    }
    masks[next++] = row;
  }
  for (int x = 0; x < boardSize; ++x) {
    Bits column = 0;
    for (int y = 0; y < boardSize; ++y) {
      column |= bitAt(x, y);
    }
    masks[next++] = column;
  }
  Bits diagonalDown = 0;
  Bits diagonalUp = 0;
  for (int i = 0; i < boardSize; ++i) {
    diagonalDown |= bitAt(i, i);
    diagonalUp |= bitAt(i, boardSize - 1 - i);
  }
  masks[next++] = diagonalDown;
  masks[next++] = diagonalUp;
  return masks;
}

constexpr auto winningMasks = makeWinningMasks();

enum class Outcome : std::int8_t {
  loss = -1,
  draw = 0,
  win = 1,
};

constexpr std::string_view outcomeName(Outcome outcome) {
  switch (outcome) {
    case Outcome::loss:
      return "loss";
    case Outcome::draw:
      return "draw";
    case Outcome::win:
      return "win";
  }
  return "invalid";
}

constexpr bool hasWin(Bits stones) {
  for (Bits mask : winningMasks) {
    if ((stones & mask) == mask) {
      return true;
    }
  }
  return false;
}

constexpr Bits immediateWinningMoves(Bits stones, Bits opponent) {
  Bits result = 0;
  for (Bits mask : winningMasks) {
    if ((mask & opponent) == 0 && std::popcount(stones & mask) == 4) {
      result |= mask & ~(stones | opponent);
    }
  }
  return result;
}

constexpr int transformIndex(int index, int transform) {
  const int x = index % boardSize;
  const int y = index / boardSize;
  int tx = x;
  int ty = y;
  switch (transform) {
    case 0:
      break;
    case 1:
      tx = boardSize - 1 - y;
      ty = x;
      break;
    case 2:
      tx = boardSize - 1 - x;
      ty = boardSize - 1 - y;
      break;
    case 3:
      tx = y;
      ty = boardSize - 1 - x;
      break;
    case 4:
      tx = boardSize - 1 - x;
      break;
    case 5:
      tx = x;
      ty = boardSize - 1 - y;
      break;
    case 6:
      tx = y;
      ty = x;
      break;
    case 7:
      tx = boardSize - 1 - y;
      ty = boardSize - 1 - x;
      break;
    default:
      std::abort();
  }
  return indexOf(tx, ty);
}

constexpr Bits transformBits(Bits bits, int transform) {
  Bits transformed = 0;
  for (int index = 0; index < cellCount; ++index) {
    if ((bits & (Bits{1} << index)) != 0) {
      transformed |= Bits{1} << transformIndex(index, transform);
    }
  }
  return transformed;
}

constexpr std::uint64_t packState(Bits black, Bits white, bool blackToMove) {
  return static_cast<std::uint64_t>(black) |
         (static_cast<std::uint64_t>(white) << cellCount) |
         (static_cast<std::uint64_t>(blackToMove) << (2 * cellCount));
}

constexpr std::uint64_t canonicalState(Bits black, Bits white,
                                       bool blackToMove) {
  std::uint64_t best = std::numeric_limits<std::uint64_t>::max();
  for (int transform = 0; transform < 8; ++transform) {
    best = std::min(best, packState(transformBits(black, transform),
                                    transformBits(white, transform),
                                    blackToMove));
  }
  return best;
}

struct Stats {
  std::uint64_t nodes = 0;
  std::uint64_t tableHits = 0;
  std::uint64_t immediateWins = 0;
  std::uint64_t doubleThreatLosses = 0;
  std::uint64_t forcedBlocks = 0;
  std::uint64_t symmetryCollapses = 0;
  std::uint64_t alphaBetaCutoffs = 0;
  std::uint64_t exactStores = 0;
  std::uint64_t lowerBoundStores = 0;
  std::uint64_t upperBoundStores = 0;
  std::uint64_t tableReplacements = 0;
  std::uint64_t maxDepth = 0;
};

enum class Bound : std::uint8_t {
  exact,
  lower,
  upper,
};

struct TableEntry {
  std::int8_t value;
  Bound bound;
};

class FlatTable {
 public:
  explicit FlatTable(unsigned power)
      : slots_(std::size_t{1} << power), mask_(slots_.size() - 1) {}

  bool find(std::uint64_t key, TableEntry& entry) const {
    const std::uint64_t packed = slots_[index(key)];
    if (packed == 0 || (packed >> 4) != key) {
      return false;
    }
    const unsigned code = static_cast<unsigned>((packed & 0xF) - 1);
    entry.value = static_cast<std::int8_t>(code % 3) - 1;
    entry.bound = static_cast<Bound>(code / 3);
    return true;
  }

  bool store(std::uint64_t key, TableEntry entry) {
    std::uint64_t& slot = slots_[index(key)];
    const bool replacement = slot != 0 && (slot >> 4) != key;
    if (slot == 0) {
      ++entries_;
    }
    const unsigned code = static_cast<unsigned>(entry.bound) * 3 +
                          static_cast<unsigned>(entry.value + 1);
    slot = (key << 4) | static_cast<std::uint64_t>(code + 1);
    return replacement;
  }

  std::size_t size() const { return entries_; }
  std::size_t capacity() const { return slots_.size(); }

 private:
  static constexpr std::uint64_t mix(std::uint64_t value) {
    value ^= value >> 30;
    value *= 0xBF58476D1CE4E5B9ULL;
    value ^= value >> 27;
    value *= 0x94D049BB133111EBULL;
    value ^= value >> 31;
    return value;
  }

  std::size_t index(std::uint64_t key) const {
    return static_cast<std::size_t>(mix(key)) & mask_;
  }

  std::vector<std::uint64_t> slots_;
  std::size_t mask_;
  std::size_t entries_ = 0;
};

class Solver {
 public:
  explicit Solver(unsigned tablePower)
      : table_(tablePower), started_(Clock::now()) {}

  Outcome solve(Bits black, Bits white, bool blackToMove, int alpha = -2,
                int beta = 2, int depth = 0) {
    ++stats_.nodes;
    stats_.maxDepth = std::max(stats_.maxDepth,
                               static_cast<std::uint64_t>(depth));
    reportProgress();

    const Bits current = blackToMove ? black : white;
    const Bits opponent = blackToMove ? white : black;
    if (hasWin(opponent)) {
      return Outcome::loss;
    }

    const Bits occupied = black | white;
    if (occupied == fullBoard) {
      return Outcome::draw;
    }

    const std::uint64_t rawKey = packState(black, white, blackToMove);
    const std::uint64_t key = canonicalState(black, white, blackToMove);
    if (key != rawKey) {
      ++stats_.symmetryCollapses;
    }
    const int originalAlpha = alpha;
    const int originalBeta = beta;
    TableEntry found{};
    if (table_.find(key, found)) {
      ++stats_.tableHits;
      const int value = found.value;
      switch (found.bound) {
        case Bound::exact:
          return static_cast<Outcome>(value);
        case Bound::lower:
          alpha = std::max(alpha, value);
          break;
        case Bound::upper:
          beta = std::min(beta, value);
          break;
      }
      if (alpha >= beta) {
        return static_cast<Outcome>(value);
      }
    }

    const Bits winningMoves = immediateWinningMoves(current, opponent);
    if (winningMoves != 0) {
      ++stats_.immediateWins;
      store(key, static_cast<int>(Outcome::win), Bound::exact);
      return Outcome::win;
    }

    const Bits opponentWinningMoves =
        immediateWinningMoves(opponent, current);
    if (std::popcount(opponentWinningMoves) >= 2) {
      ++stats_.doubleThreatLosses;
      store(key, static_cast<int>(Outcome::loss), Bound::exact);
      return Outcome::loss;
    }

    Bits moves = fullBoard & ~occupied;
    if (opponentWinningMoves != 0) {
      ++stats_.forcedBlocks;
      moves = opponentWinningMoves;
    }

    std::vector<int> orderedMoves;
    orderedMoves.reserve(std::popcount(moves));
    while (moves != 0) {
      const int move = std::countr_zero(moves);
      moves &= moves - 1;
      orderedMoves.push_back(move);
    }
    std::ranges::stable_sort(orderedMoves, [&](int left, int right) {
      return moveScore(left, current, opponent) >
             moveScore(right, current, opponent);
    });

    int best = static_cast<int>(Outcome::loss);
    for (int move : orderedMoves) {
      const Bits moveBit = Bits{1} << move;
      const Bits nextBlack = blackToMove ? black | moveBit : black;
      const Bits nextWhite = blackToMove ? white : white | moveBit;
      const int result = -static_cast<int>(solve(
          nextBlack, nextWhite, !blackToMove, -beta, -alpha, depth + 1));
      best = std::max(best, result);
      alpha = std::max(alpha, result);
      if (alpha >= beta) {
        ++stats_.alphaBetaCutoffs;
        break;
      }
    }

    Bound bound = Bound::exact;
    if (best <= originalAlpha) {
      bound = Bound::upper;
    } else if (best >= originalBeta) {
      bound = Bound::lower;
    }
    store(key, best, bound);
    return static_cast<Outcome>(best);
  }

  const Stats& stats() const { return stats_; }
  std::size_t tableSize() const { return table_.size(); }
  std::size_t tableCapacity() const { return table_.capacity(); }

  double elapsedSeconds() const {
    return std::chrono::duration<double>(Clock::now() - started_).count();
  }

 private:
  using Clock = std::chrono::steady_clock;

  static int moveScore(int move, Bits current, Bits opponent) {
    const Bits moveBit = Bits{1} << move;
    int score = 0;
    for (Bits mask : winningMasks) {
      if ((mask & moveBit) == 0) {
        continue;
      }
      if ((mask & opponent) == 0) {
        const int ownCount = std::popcount(mask & current);
        score += 8 + ownCount * ownCount * 4;
      }
      if ((mask & current) == 0) {
        const int opponentCount = std::popcount(mask & opponent);
        score += 6 + opponentCount * opponentCount * 3;
      }
    }
    const int x = move % boardSize;
    const int y = move / boardSize;
    score -= std::abs(x - 2) + std::abs(y - 2);
    return score;
  }

  void reportProgress() {
    constexpr std::uint64_t interval = 5'000'000;
    if (stats_.nodes % interval != 0) {
      return;
    }
    std::cerr << "progress nodes=" << stats_.nodes
              << " table=" << table_.size()
              << " hits=" << stats_.tableHits
              << " elapsed_s=" << elapsedSeconds() << '\n';
  }

  void store(std::uint64_t key, int value, Bound bound) {
    if (table_.store(
            key, TableEntry{static_cast<std::int8_t>(value), bound})) {
      ++stats_.tableReplacements;
    }
    switch (bound) {
      case Bound::exact:
        ++stats_.exactStores;
        break;
      case Bound::lower:
        ++stats_.lowerBoundStores;
        break;
      case Bound::upper:
        ++stats_.upperBoundStores;
        break;
    }
  }

  FlatTable table_;
  Stats stats_;
  Clock::time_point started_;
};

bool runSelfChecks() {
  if (winningMasks.size() != 12) {
    return false;
  }
  for (Bits mask : winningMasks) {
    if (std::popcount(mask) != 5) {
      return false;
    }
  }
  const Bits horizontalFour =
      bitAt(0, 0) | bitAt(1, 0) | bitAt(2, 0) | bitAt(3, 0);
  if (immediateWinningMoves(horizontalFour, 0) != bitAt(4, 0)) {
    return false;
  }
  const Bits fork = horizontalFour |
                    bitAt(0, 1) | bitAt(0, 2) | bitAt(0, 3);
  if (immediateWinningMoves(fork, 0) != (bitAt(4, 0) | bitAt(0, 4))) {
    return false;
  }
  for (int transform = 0; transform < 8; ++transform) {
    if (std::popcount(transformBits(fork, transform)) !=
        std::popcount(fork)) {
      return false;
    }
  }
  return true;
}

}  // namespace

int main() {
  if (!runSelfChecks()) {
    std::cerr << "self_check=failed\n";
    return 2;
  }

  constexpr unsigned tablePower = 27;
  Solver solver(tablePower);
  const Outcome result = solver.solve(0, 0, true);
  const Stats& stats = solver.stats();

  std::cout << "self_check=passed\n";
  std::cout << "board=5x5\n";
  std::cout << "win_length=5\n";
  std::cout << "root_turn=black\n";
  std::cout << "result_for_black=" << outcomeName(result) << '\n';
  std::cout << "nodes=" << stats.nodes << '\n';
  std::cout << "table_entries=" << solver.tableSize() << '\n';
  std::cout << "table_capacity=" << solver.tableCapacity() << '\n';
  std::cout << "table_hits=" << stats.tableHits << '\n';
  std::cout << "immediate_wins=" << stats.immediateWins << '\n';
  std::cout << "double_threat_losses=" << stats.doubleThreatLosses << '\n';
  std::cout << "forced_blocks=" << stats.forcedBlocks << '\n';
  std::cout << "symmetry_collapses=" << stats.symmetryCollapses << '\n';
  std::cout << "alpha_beta_cutoffs=" << stats.alphaBetaCutoffs << '\n';
  std::cout << "exact_stores=" << stats.exactStores << '\n';
  std::cout << "lower_bound_stores=" << stats.lowerBoundStores << '\n';
  std::cout << "upper_bound_stores=" << stats.upperBoundStores << '\n';
  std::cout << "table_replacements=" << stats.tableReplacements << '\n';
  std::cout << "max_depth=" << stats.maxDepth << '\n';
  std::cout << "elapsed_s=" << solver.elapsedSeconds() << '\n';
  return 0;
}
