#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <numeric>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace {

using Bits = std::uint64_t;

struct Pair {
  int first = 0;
  int second = 0;
};

struct BoardSpec {
  int boardSize = 5;
  int winLength = 5;
  int cellCount = 25;
  Bits fullBoard = 0;
  std::vector<Bits> winningMasks;
  std::vector<std::vector<int>> linesByCell;

  explicit BoardSpec(int requestedBoardSize)
      : boardSize(requestedBoardSize),
        cellCount(requestedBoardSize * requestedBoardSize),
        fullBoard(cellCount == 64 ? ~Bits{0}
                                  : (Bits{1} << cellCount) - 1),
        linesByCell(static_cast<std::size_t>(cellCount)) {
    if (boardSize < winLength || boardSize > 8) {
      throw std::invalid_argument("board size must be between 5 and 8");
    }
    addLines(1, 0);
    addLines(0, 1);
    addLines(1, 1);
    addLines(-1, 1);
    for (std::size_t line = 0; line < winningMasks.size(); ++line) {
      Bits cells = winningMasks[line];
      while (cells != 0) {
        const int cell = std::countr_zero(cells);
        cells &= cells - 1;
        linesByCell[static_cast<std::size_t>(cell)].push_back(
            static_cast<int>(line));
      }
    }
  }

  int indexOf(int x, int y) const { return y * boardSize + x; }

  Bits bitAt(int x, int y) const { return Bits{1} << indexOf(x, y); }

  std::pair<int, int> coordOf(int index) const {
    return {index % boardSize, index / boardSize};
  }

  bool inside(int x, int y) const {
    return x >= 0 && x < boardSize && y >= 0 && y < boardSize;
  }

  void addLines(int dx, int dy) {
    for (int y = 0; y < boardSize; ++y) {
      for (int x = 0; x < boardSize; ++x) {
        const int endX = x + (winLength - 1) * dx;
        const int endY = y + (winLength - 1) * dy;
        if (!inside(endX, endY)) {
          continue;
        }
        const int beforeX = x - dx;
        const int beforeY = y - dy;
        if (inside(beforeX, beforeY)) {
          continue;
        }
        for (int offset = 0; offset + winLength <= boardSize; ++offset) {
          const int startX = x + offset * dx;
          const int startY = y + offset * dy;
          const int windowEndX = startX + (winLength - 1) * dx;
          const int windowEndY = startY + (winLength - 1) * dy;
          if (!inside(windowEndX, windowEndY)) {
            break;
          }
          Bits mask = 0;
          for (int step = 0; step < winLength; ++step) {
            mask |= bitAt(startX + step * dx, startY + step * dy);
          }
          winningMasks.push_back(mask);
        }
      }
    }
    std::ranges::sort(winningMasks);
    const auto duplicate = std::ranges::unique(winningMasks);
    winningMasks.erase(duplicate.begin(), duplicate.end());
  }

  int transformIndex(int index, int transform) const {
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

  std::vector<int> openingRepresentatives() const {
    std::vector<int> result;
    for (int cell = 0; cell < cellCount; ++cell) {
      int canonical = cell;
      for (int transform = 1; transform < 8; ++transform) {
        canonical = std::min(canonical, transformIndex(cell, transform));
      }
      if (canonical == cell) {
        result.push_back(cell);
      }
    }
    return result;
  }
};

enum class PairingStatus {
  found,
  impossible,
  nodeLimit,
};

const char* pairingStatusName(PairingStatus status) {
  switch (status) {
    case PairingStatus::found:
      return "found";
    case PairingStatus::impossible:
      return "impossible";
    case PairingStatus::nodeLimit:
      return "node_limit";
  }
  return "invalid";
}

struct PairingResult {
  PairingStatus status = PairingStatus::impossible;
  std::vector<Pair> pairs;
  std::uint64_t nodes = 0;
};

class PairingSolver {
 public:
  PairingSolver(const BoardSpec& spec, std::uint64_t maxNodes,
                std::size_t maxBranches)
      : spec_(spec),
        maxNodes_(maxNodes),
        maxBranches_(maxBranches),
        active_(spec.winningMasks.size(), false),
        covered_(spec.winningMasks.size(), false),
        partner_(static_cast<std::size_t>(spec.cellCount), -1) {
    if (spec_.winningMasks.size() > 128) {
      throw std::invalid_argument("pairing solver supports at most 128 lines");
    }
    activeLines_.reserve(spec_.winningMasks.size());
    selected_.reserve(static_cast<std::size_t>(spec_.cellCount / 2));
    solution_.reserve(static_cast<std::size_t>(spec_.cellCount / 2));
  }

  PairingResult solve(Bits maker, Bits breaker) {
    maker_ = maker;
    breaker_ = breaker;
    nodes_ = 0;
    selected_.clear();
    solution_.clear();
    std::ranges::fill(partner_, -1);
    activeLines_.clear();
    std::fill(active_.begin(), active_.end(), false);
    std::fill(covered_.begin(), covered_.end(), false);

    for (std::size_t line = 0; line < spec_.winningMasks.size(); ++line) {
      const Bits mask = spec_.winningMasks[line];
      if ((mask & breaker_) == 0) {
        if ((mask & maker_) == mask) {
          return {PairingStatus::impossible, {}, nodes_};
        }
        activeLines_.push_back(static_cast<int>(line));
        active_[line] = true;
      }
    }

    const PairingStatus status = search();
    if (status == PairingStatus::found) {
      return {PairingStatus::found, solution_, nodes_};
    }
    return {status, {}, nodes_};
  }

  bool verify(Bits maker, Bits breaker, const std::vector<Pair>& pairs) const {
    Bits used = 0;
    for (const Pair pair : pairs) {
      if (pair.first < 0 || pair.first >= spec_.cellCount ||
          pair.second < 0 || pair.second >= spec_.cellCount ||
          pair.first == pair.second) {
        return false;
      }
      const Bits pairMask = (Bits{1} << pair.first) | (Bits{1} << pair.second);
      if ((pairMask & (maker | breaker | used)) != 0) {
        return false;
      }
      used |= pairMask;
    }
    for (Bits line : spec_.winningMasks) {
      if ((line & breaker) != 0) {
        continue;
      }
      bool lineCovered = false;
      for (const Pair pair : pairs) {
        const Bits pairMask =
            (Bits{1} << pair.first) | (Bits{1} << pair.second);
        if ((line & pairMask) == pairMask) {
          lineCovered = true;
          break;
        }
      }
      if (!lineCovered) {
        return false;
      }
    }
    return true;
  }

 private:
  struct Candidate {
    int first = 0;
    int second = 0;
    int coverage = 0;
    int score = 0;
  };

  struct CandidateList {
    std::array<Candidate, 10> values{};
    std::size_t size = 0;
  };

  struct LineSet {
    Bits low = 0;
    Bits high = 0;

    void add(int line) {
      if (line < 64) {
        low |= Bits{1} << line;
      } else {
        high |= Bits{1} << (line - 64);
      }
    }

    void merge(const LineSet& other) {
      low |= other.low;
      high |= other.high;
    }

    bool operator==(const LineSet&) const = default;
  };

  PairingStatus search() {
    if (nodes_ >= maxNodes_) {
      return PairingStatus::nodeLimit;
    }
    ++nodes_;

    const std::size_t greedyStart = selected_.size();
    LineSet greedilyCovered;
    while (true) {
      std::optional<Pair> forced;
      for (const int line : activeLines_) {
        if (covered_[static_cast<std::size_t>(line)]) {
          continue;
        }
        const Bits freeCells = unassignedCells(line);
        const int freeCount = std::popcount(freeCells);
        if (freeCount < 2) {
          undoTo(greedyStart, greedilyCovered);
          return PairingStatus::impossible;
        }
        if (freeCount == 2) {
          const int first = std::countr_zero(freeCells);
          const int second = std::countr_zero(
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
      assignPair(*forced, greedilyCovered);
    }

    int chosenLine = -1;
    CandidateList chosenCandidates;
    std::size_t smallestCount = std::numeric_limits<std::size_t>::max();
    for (const int line : activeLines_) {
      if (covered_[static_cast<std::size_t>(line)]) {
        continue;
      }
      const CandidateList candidates = candidatesFor(line);
      if (candidates.size == 0) {
        undoTo(greedyStart, greedilyCovered);
        return PairingStatus::impossible;
      }
      if (candidates.size < smallestCount) {
        smallestCount = candidates.size;
        chosenLine = line;
        chosenCandidates = candidates;
        if (smallestCount == 1) {
          break;
        }
      }
    }

    if (chosenLine == -1) {
      solution_ = selected_;
      return PairingStatus::found;
    }

    std::sort(chosenCandidates.values.begin(),
              chosenCandidates.values.begin() + chosenCandidates.size,
              [](const Candidate& left, const Candidate& right) {
      if (left.score != right.score) {
        return left.score > right.score;
      }
      if (left.first != right.first) {
        return left.first < right.first;
      }
      return left.second < right.second;
              });

    const std::size_t branchLimit = maxBranches_ == 0
        ? chosenCandidates.size
        : std::min(maxBranches_, chosenCandidates.size);
    bool sawUnknown = branchLimit < chosenCandidates.size;
    for (std::size_t branch = 0; branch < branchLimit; ++branch) {
      const Candidate candidate = chosenCandidates.values[branch];
      LineSet newlyCovered;
      assignPair({candidate.first, candidate.second}, newlyCovered);

      const PairingStatus child = search();
      if (child == PairingStatus::found) {
        return PairingStatus::found;
      }
      sawUnknown = sawUnknown || child == PairingStatus::nodeLimit;

      undoTo(selected_.size() - 1, newlyCovered);
      if (nodes_ >= maxNodes_) {
        sawUnknown = true;
        break;
      }
    }
    undoTo(greedyStart, greedilyCovered);
    return sawUnknown ? PairingStatus::nodeLimit
                      : PairingStatus::impossible;
  }

  Bits unassignedCells(int line) const {
    Bits result = 0;
    Bits cells = spec_.winningMasks[static_cast<std::size_t>(line)] &
                 ~(maker_ | breaker_);
    while (cells != 0) {
      const int cell = std::countr_zero(cells);
      cells &= cells - 1;
      if (partner_[static_cast<std::size_t>(cell)] == -1) {
        result |= Bits{1} << cell;
      }
    }
    return result;
  }

  LineSet freeEdgesAt(int cell) const {
    LineSet result;
    for (const int line :
         spec_.linesByCell[static_cast<std::size_t>(cell)]) {
      if (active_[static_cast<std::size_t>(line)] &&
          !covered_[static_cast<std::size_t>(line)]) {
        result.add(line);
      }
    }
    return result;
  }

  std::optional<Pair> equalFreeEdgePair() const {
    const Bits empty = spec_.fullBoard & ~(maker_ | breaker_);
    for (int first = 0; first < spec_.cellCount; ++first) {
      if ((empty & (Bits{1} << first)) == 0 ||
          partner_[static_cast<std::size_t>(first)] != -1) {
        continue;
      }
      const LineSet firstEdges = freeEdgesAt(first);
      if (firstEdges == LineSet{}) {
        continue;
      }
      for (int second = first + 1; second < spec_.cellCount; ++second) {
        if ((empty & (Bits{1} << second)) == 0 ||
            partner_[static_cast<std::size_t>(second)] != -1) {
          continue;
        }
        if (firstEdges == freeEdgesAt(second)) {
          return Pair{first, second};
        }
      }
    }
    return std::nullopt;
  }

  void assignPair(Pair pair, LineSet& newlyCovered) {
    partner_[static_cast<std::size_t>(pair.first)] = pair.second;
    partner_[static_cast<std::size_t>(pair.second)] = pair.first;
    selected_.push_back(pair);
    const Bits pairMask =
        (Bits{1} << pair.first) | (Bits{1} << pair.second);
    for (const int line : activeLines_) {
      if (!covered_[static_cast<std::size_t>(line)] &&
          (spec_.winningMasks[static_cast<std::size_t>(line)] & pairMask) ==
              pairMask) {
        covered_[static_cast<std::size_t>(line)] = true;
        newlyCovered.add(line);
      }
    }
  }

  void undoTo(std::size_t selectedSize, LineSet newlyCovered) {
    while (newlyCovered.low != 0) {
      const int line = std::countr_zero(newlyCovered.low);
      newlyCovered.low &= newlyCovered.low - 1;
      covered_[static_cast<std::size_t>(line)] = false;
    }
    while (newlyCovered.high != 0) {
      const int line = std::countr_zero(newlyCovered.high) + 64;
      newlyCovered.high &= newlyCovered.high - 1;
      covered_[static_cast<std::size_t>(line)] = false;
    }
    while (selected_.size() > selectedSize) {
      const Pair pair = selected_.back();
      selected_.pop_back();
      partner_[static_cast<std::size_t>(pair.first)] = -1;
      partner_[static_cast<std::size_t>(pair.second)] = -1;
    }
  }

  CandidateList candidatesFor(int line) const {
    std::array<int, 5> freeCells{};
    std::size_t freeCount = 0;
    Bits cells = spec_.winningMasks[static_cast<std::size_t>(line)] &
                 ~(maker_ | breaker_);
    while (cells != 0) {
      const int cell = std::countr_zero(cells);
      cells &= cells - 1;
      if (partner_[static_cast<std::size_t>(cell)] == -1) {
        freeCells[freeCount++] = cell;
      }
    }

    CandidateList result;
    for (std::size_t left = 0; left < freeCount; ++left) {
      for (std::size_t right = left + 1; right < freeCount; ++right) {
        const int first = freeCells[left];
        const int second = freeCells[right];
        int coverage = 0;
        int firstOnly = 0;
        int secondOnly = 0;
        for (const int candidateLine : activeLines_) {
          if (covered_[static_cast<std::size_t>(candidateLine)]) {
            continue;
          }
          const Bits candidateMask =
              spec_.winningMasks[static_cast<std::size_t>(candidateLine)];
          const bool hasFirst = (candidateMask & (Bits{1} << first)) != 0;
          const bool hasSecond = (candidateMask & (Bits{1} << second)) != 0;
          if (hasFirst && hasSecond) {
            ++coverage;
          } else if (hasFirst) {
            ++firstOnly;
          } else if (hasSecond) {
            ++secondOnly;
          }
        }
        const int score = coverage * 2 - firstOnly - secondOnly;
        result.values[result.size++] =
            {first, second, coverage, score};
      }
    }
    return result;
  }

  const BoardSpec& spec_;
  std::uint64_t maxNodes_;
  std::size_t maxBranches_;
  Bits maker_ = 0;
  Bits breaker_ = 0;
  std::uint64_t nodes_ = 0;
  std::vector<int> activeLines_;
  std::vector<bool> active_;
  std::vector<bool> covered_;
  std::vector<int> partner_;
  std::vector<Pair> selected_;
  std::vector<Pair> solution_;
};

struct ReplyProof {
  int makerMove = -1;
  int breakerMove = -1;
  std::vector<Pair> pairs;
};

struct ReplySearchResult {
  PairingStatus status = PairingStatus::impossible;
  std::vector<ReplyProof> proofs;
  std::uint64_t pairingCalls = 0;
  std::uint64_t pairingNodes = 0;
};

enum class GameValue : std::uint8_t {
  unknown,
  breakerWin,
  makerWin,
};

struct SearchResult {
  GameValue value = GameValue::unknown;
  Bits rzone = 0;
};

struct MoveGroup {
  int move = -1;
  std::vector<std::pair<int, int>> equivalents;
};

const char* gameValueName(GameValue value) {
  switch (value) {
    case GameValue::unknown:
      return "unknown";
    case GameValue::breakerWin:
      return "breaker_win";
    case GameValue::makerWin:
      return "maker_win";
  }
  return "invalid";
}

struct StateKey {
  Bits maker = 0;
  Bits breaker = 0;

  friend bool operator==(StateKey left, StateKey right) {
    return left.maker == right.maker && left.breaker == right.breaker;
  }

  friend bool operator<(StateKey left, StateKey right) {
    return left.maker < right.maker ||
           (left.maker == right.maker && left.breaker < right.breaker);
  }
};

class CompactTable {
 public:
  explicit CompactTable(unsigned power)
      : makerKeys_(std::size_t{1} << power),
        breakerKeys_(std::size_t{1} << power),
        rzones_(std::size_t{1} << power),
        values_(std::size_t{1} << power),
        replacementCursor_(values_.size() / ways),
        setMask_(replacementCursor_.size() - 1) {
    if (power < 2) {
      throw std::invalid_argument("table power must be at least 2");
    }
  }

  std::optional<SearchResult> find(StateKey key) const {
    const std::size_t firstSlot = index(key);
    for (std::size_t offset = 0; offset < ways; ++offset) {
      const std::size_t slot = firstSlot + offset;
      if (values_[slot] != 0 && makerKeys_[slot] == key.maker &&
          breakerKeys_[slot] == key.breaker) {
        return SearchResult{
            values_[slot] == 1 ? GameValue::breakerWin
                               : GameValue::makerWin,
            rzones_[slot]};
      }
    }
    return std::nullopt;
  }

  bool store(StateKey key, GameValue value, Bits rzone) {
    const std::size_t firstSlot = index(key);
    std::size_t slot = firstSlot;
    bool replacement = true;
    for (std::size_t offset = 0; offset < ways; ++offset) {
      const std::size_t candidate = firstSlot + offset;
      if (values_[candidate] != 0 && makerKeys_[candidate] == key.maker &&
          breakerKeys_[candidate] == key.breaker) {
        slot = candidate;
        replacement = false;
        break;
      }
      if (values_[candidate] == 0) {
        slot = candidate;
        replacement = false;
        ++entries_;
        break;
      }
    }
    if (replacement) {
      const std::size_t set = firstSlot / ways;
      slot = firstSlot + replacementCursor_[set];
      replacementCursor_[set] =
          static_cast<std::uint8_t>((replacementCursor_[set] + 1) % ways);
    }
    makerKeys_[slot] = key.maker;
    breakerKeys_[slot] = key.breaker;
    rzones_[slot] = rzone;
    values_[slot] = value == GameValue::breakerWin ? 1 : 2;
    return replacement;
  }

  std::size_t size() const { return entries_; }
  std::size_t capacity() const { return values_.size(); }
  std::size_t bytes() const {
    return makerKeys_.size() * sizeof(Bits) +
           breakerKeys_.size() * sizeof(Bits) +
           rzones_.size() * sizeof(Bits) +
           values_.size() * sizeof(std::uint8_t) +
           replacementCursor_.size() * sizeof(std::uint8_t);
  }

 private:
  static std::uint64_t mix(std::uint64_t value) {
    value ^= value >> 30;
    value *= 0xBF58476D1CE4E5B9ULL;
    value ^= value >> 27;
    value *= 0x94D049BB133111EBULL;
    value ^= value >> 31;
    return value;
  }

  std::size_t index(StateKey key) const {
    const std::uint64_t combined =
        mix(key.maker) ^ std::rotl(mix(key.breaker), 29);
    return (static_cast<std::size_t>(mix(combined)) & setMask_) * ways;
  }

  static constexpr std::size_t ways = 4;

  std::vector<Bits> makerKeys_;
  std::vector<Bits> breakerKeys_;
  std::vector<Bits> rzones_;
  std::vector<std::uint8_t> values_;
  std::vector<std::uint8_t> replacementCursor_;
  std::size_t setMask_ = 0;
  std::size_t entries_ = 0;
};

struct PairingLookup {
  bool found = false;
  Bits rzone = 0;
};

class PairingTable {
 public:
  explicit PairingTable(unsigned power)
      : makerKeys_(std::size_t{1} << power),
        breakerKeys_(std::size_t{1} << power),
        rzones_(std::size_t{1} << power),
        values_(std::size_t{1} << power),
        mask_(values_.size() - 1) {}

  std::optional<PairingLookup> find(StateKey key) const {
    const std::size_t slot = index(key);
    if (values_[slot] == 0 || makerKeys_[slot] != key.maker ||
        breakerKeys_[slot] != key.breaker) {
      return std::nullopt;
    }
    return PairingLookup{values_[slot] == 2, rzones_[slot]};
  }

  void store(StateKey key, PairingLookup result) {
    const std::size_t slot = index(key);
    makerKeys_[slot] = key.maker;
    breakerKeys_[slot] = key.breaker;
    rzones_[slot] = result.rzone;
    values_[slot] = result.found ? 2 : 1;
  }

  std::size_t capacity() const { return values_.size(); }
  std::size_t bytes() const {
    return makerKeys_.size() * sizeof(Bits) +
           breakerKeys_.size() * sizeof(Bits) +
           rzones_.size() * sizeof(Bits) +
           values_.size() * sizeof(std::uint8_t);
  }

 private:
  static std::uint64_t mix(std::uint64_t value) {
    value ^= value >> 30;
    value *= 0xBF58476D1CE4E5B9ULL;
    value ^= value >> 27;
    value *= 0x94D049BB133111EBULL;
    value ^= value >> 31;
    return value;
  }

  std::size_t index(StateKey key) const {
    const std::uint64_t combined =
        mix(key.maker) ^ std::rotl(mix(key.breaker), 29);
    return static_cast<std::size_t>(mix(combined)) & mask_;
  }

  std::vector<Bits> makerKeys_;
  std::vector<Bits> breakerKeys_;
  std::vector<Bits> rzones_;
  std::vector<std::uint8_t> values_;
  std::size_t mask_ = 0;
};

struct TreeStats {
  std::uint64_t nodes = 0;
  std::uint64_t tableHits = 0;
  std::uint64_t tableStores = 0;
  std::uint64_t tableReplacements = 0;
  std::uint64_t symmetryCollapses = 0;
  std::uint64_t symmetricMovesSkipped = 0;
  std::uint64_t dominatedMovesSkipped = 0;
  std::uint64_t pairingCalls = 0;
  std::uint64_t pairingCacheHits = 0;
  std::uint64_t pairingNodes = 0;
  std::uint64_t pairingWins = 0;
  std::uint64_t replyPairingProbes = 0;
  std::uint64_t replyPairingWins = 0;
  std::uint64_t potentialWins = 0;
  std::uint64_t partialPairs = 0;
  std::uint64_t partialPairCellsRemoved = 0;
  std::uint64_t forcedBlocks = 0;
  std::uint64_t doubleThreatWins = 0;
  std::uint64_t irrelevantMovesSkipped = 0;
  std::uint64_t rzoneMovesSkipped = 0;
  std::uint64_t rzoneWins = 0;
  std::uint64_t depthLeaves = 0;
  std::uint64_t maxPly = 0;
};

class DrawTreeSolver {
 public:
  DrawTreeSolver(const BoardSpec& spec, unsigned tablePower,
                 std::uint64_t maxNodes, std::uint64_t maxPairingNodes,
                 std::size_t maxPairBranches, std::size_t replyProbes,
                 int replyProbeMinStones,
                 std::uint64_t maxReplyPairingNodes)
      : spec_(spec),
        table_(tablePower),
        pairingTable_(std::min(tablePower, 20U)),
        maxNodes_(maxNodes),
        maxPairingNodes_(maxPairingNodes),
        maxPairBranches_(maxPairBranches),
        replyProbes_(replyProbes),
        replyProbeMinStones_(replyProbeMinStones),
        pairingSolver_(spec, maxPairingNodes, maxPairBranches),
        replyPairingSolver_(spec, maxReplyPairingNodes, maxPairBranches),
        started_(Clock::now()) {
    transformedBits_.resize(8);
    for (int transform = 0; transform < 8; ++transform) {
      transformedBits_[static_cast<std::size_t>(transform)].resize(
          static_cast<std::size_t>(spec_.cellCount));
      for (int cell = 0; cell < spec_.cellCount; ++cell) {
        transformedBits_[static_cast<std::size_t>(transform)]
                        [static_cast<std::size_t>(cell)] =
            Bits{1} << spec_.transformIndex(cell, transform);
      }
    }
  }

  GameValue solve(int maxDepth) {
    maxDepth_ = maxDepth;
    return search(0, 0, true, maxDepth, 0).value;
  }

  GameValue solvePosition(Bits maker, Bits breaker, bool makerTurn,
                          int maxDepth) {
    maxDepth_ = maxDepth;
    return search(maker, breaker, makerTurn, maxDepth, 0).value;
  }

  const TreeStats& stats() const { return stats_; }
  std::size_t tableSize() const { return table_.size(); }
  std::size_t tableCapacity() const { return table_.capacity(); }
  std::size_t tableBytes() const { return table_.bytes(); }
  std::size_t pairingTableCapacity() const {
    return pairingTable_.capacity();
  }
  std::size_t pairingTableBytes() const { return pairingTable_.bytes(); }
  bool nodeBudgetExhausted() const { return nodeBudgetExhausted_; }

  double elapsedSeconds() const {
    return std::chrono::duration<double>(Clock::now() - started_).count();
  }

 private:
  using Clock = std::chrono::steady_clock;

  struct CanonicalState {
    StateKey key;
    int symmetry = 0;
  };

  Bits transform(Bits bits, int transformIndex) const {
    Bits result = 0;
    while (bits != 0) {
      const int cell = std::countr_zero(bits);
      bits &= bits - 1;
      result |= transformedBits_[static_cast<std::size_t>(transformIndex)]
                                [static_cast<std::size_t>(cell)];
    }
    return result;
  }

  CanonicalState canonicalState(Bits maker, Bits breaker) const {
    CanonicalState best{{maker, breaker}, 0};
    for (int symmetry = 1; symmetry < 8; ++symmetry) {
      const StateKey candidate{transform(maker, symmetry),
                               transform(breaker, symmetry)};
      if (candidate < best.key) {
        best = {candidate, symmetry};
      }
    }
    return best;
  }

  StateKey canonical(Bits maker, Bits breaker) const {
    return canonicalState(maker, breaker).key;
  }

  static int inverseSymmetry(int symmetry) {
    constexpr std::array<int, 8> inverses{0, 3, 2, 1, 4, 5, 6, 7};
    return inverses[static_cast<std::size_t>(symmetry)];
  }

  bool makerHasWin(Bits maker) const {
    for (const Bits line : spec_.winningMasks) {
      if ((maker & line) == line) {
        return true;
      }
    }
    return false;
  }

  Bits immediateMakerWins(Bits maker, Bits breaker) const {
    Bits result = 0;
    for (const Bits line : spec_.winningMasks) {
      if ((line & breaker) == 0 &&
          std::popcount(line & maker) == spec_.winLength - 1) {
        result |= line & ~(maker | breaker);
      }
    }
    return result;
  }

  Bits relevantMoves(Bits maker, Bits breaker) const {
    Bits result = 0;
    for (const Bits line : spec_.winningMasks) {
      if ((line & breaker) == 0) {
        result |= line;
      }
    }
    return result & ~(maker | breaker);
  }

  std::uint64_t potential(Bits maker, Bits breaker) const {
    std::uint64_t result = 0;
    for (const Bits line : spec_.winningMasks) {
      if ((line & breaker) == 0) {
        result += std::uint64_t{1} << std::popcount(line & maker);
      }
    }
    return result;
  }

  std::pair<std::uint64_t, std::uint64_t> activeLineSignature(
      int cell, Bits breaker) const {
    std::pair<std::uint64_t, std::uint64_t> result{0, 0};
    for (const int line :
         spec_.linesByCell[static_cast<std::size_t>(cell)]) {
      if ((spec_.winningMasks[static_cast<std::size_t>(line)] & breaker) != 0) {
        continue;
      }
      if (line < 64) {
        result.first |= Bits{1} << line;
      } else {
        result.second |= Bits{1} << (line - 64);
      }
    }
    return result;
  }

  Bits partialPairReduction(Bits maker, Bits breaker) {
    Bits removed = 0;
    while (true) {
      const Bits unavailable = maker | breaker | removed;
      std::array<std::pair<std::uint64_t, std::uint64_t>, 64> signatures{};
      for (int cell = 0; cell < spec_.cellCount; ++cell) {
        if ((unavailable & (Bits{1} << cell)) == 0) {
          signatures[static_cast<std::size_t>(cell)] =
              activeLineSignature(cell, breaker | removed);
        }
      }
      std::optional<Pair> found;
      for (int first = 0; first < spec_.cellCount && !found.has_value();
           ++first) {
        if ((unavailable & (Bits{1} << first)) != 0) {
          continue;
        }
        const auto firstSignature =
            signatures[static_cast<std::size_t>(first)];
        if (firstSignature == std::pair<std::uint64_t, std::uint64_t>{0, 0}) {
          continue;
        }
        for (int second = first + 1; second < spec_.cellCount; ++second) {
          if ((unavailable & (Bits{1} << second)) != 0) {
            continue;
          }
          if (firstSignature == signatures[static_cast<std::size_t>(second)]) {
            found = Pair{first, second};
            break;
          }
        }
      }
      if (!found.has_value()) {
        break;
      }
      removed |= (Bits{1} << found->first) | (Bits{1} << found->second);
      ++stats_.partialPairs;
      stats_.partialPairCellsRemoved += 2;
    }
    return removed;
  }

  int moveScore(int move, Bits maker, Bits breaker) const {
    int result = 0;
    for (const int lineIndex :
         spec_.linesByCell[static_cast<std::size_t>(move)]) {
      const Bits line = spec_.winningMasks[static_cast<std::size_t>(lineIndex)];
      if ((line & breaker) == 0) {
        result += 1 << std::popcount(line & maker);
      }
    }
    const auto [x, y] = spec_.coordOf(move);
    result = result * 16 -
             std::abs(2 * x - (spec_.boardSize - 1)) -
             std::abs(2 * y - (spec_.boardSize - 1));
    return result;
  }

  std::vector<MoveGroup> orderedUniqueMoves(Bits moves, Bits maker,
                                            Bits breaker,
                                            Bits symmetryBreaker,
                                            bool makerTurn,
                                            std::vector<Pair>& dominatedMoves) {
    std::vector<int> ordered;
    while (moves != 0) {
      const int move = std::countr_zero(moves);
      moves &= moves - 1;
      ordered.push_back(move);
    }

    std::array<std::pair<std::uint64_t, std::uint64_t>, 64> signatures{};
    for (const int move : ordered) {
      signatures[static_cast<std::size_t>(move)] =
          activeLineSignature(move, breaker);
    }
    std::vector<int> dominators(ordered.size(), -1);
    for (std::size_t candidate = 0; candidate < ordered.size(); ++candidate) {
      const auto candidateLines =
          signatures[static_cast<std::size_t>(ordered[candidate])];
      int bestDominator = -1;
      int bestLineCount = -1;
      for (std::size_t dominator = 0; dominator < ordered.size();
           ++dominator) {
        if (candidate == dominator) {
          continue;
        }
        const auto dominatorLines =
            signatures[static_cast<std::size_t>(ordered[dominator])];
        const bool contains =
            (dominatorLines.first | candidateLines.first) ==
                dominatorLines.first &&
            (dominatorLines.second | candidateLines.second) ==
                dominatorLines.second;
        const bool equal = dominatorLines == candidateLines;
        if (!contains ||
            (equal && ordered[dominator] > ordered[candidate])) {
          continue;
        }
        const int lineCount =
            std::popcount(dominatorLines.first) +
            std::popcount(dominatorLines.second);
        if (lineCount > bestLineCount ||
            (lineCount == bestLineCount &&
             (bestDominator < 0 ||
              ordered[dominator] < bestDominator))) {
          bestDominator = ordered[dominator];
          bestLineCount = lineCount;
        }
      }
      if (bestDominator >= 0) {
        dominators[candidate] = bestDominator;
        ++stats_.dominatedMovesSkipped;
        if (makerTurn) {
          dominatedMoves.push_back({ordered[candidate], bestDominator});
        }
      }
    }

    std::vector<int> reduced;
    reduced.reserve(ordered.size());
    for (std::size_t index = 0; index < ordered.size(); ++index) {
      if (dominators[index] < 0) {
        reduced.push_back(ordered[index]);
      }
    }
    ordered = std::move(reduced);
    std::ranges::stable_sort(ordered, [&](int left, int right) {
      return moveScore(left, maker, breaker) >
             moveScore(right, maker, breaker);
    });

    std::vector<int> stabilizers;
    for (int symmetry = 0; symmetry < 8; ++symmetry) {
      if (transform(maker, symmetry) == maker &&
          transform(symmetryBreaker, symmetry) == symmetryBreaker) {
        stabilizers.push_back(symmetry);
      }
    }

    std::vector<MoveGroup> result;
    for (const int move : ordered) {
      std::size_t matchingGroup = result.size();
      int matchingSymmetry = -1;
      for (std::size_t groupIndex = 0; groupIndex < result.size();
           ++groupIndex) {
        for (const int symmetry : stabilizers) {
          if (spec_.transformIndex(result[groupIndex].move, symmetry) == move) {
            matchingGroup = groupIndex;
            matchingSymmetry = symmetry;
            break;
          }
        }
        if (matchingGroup != result.size()) {
          break;
        }
      }
      if (matchingGroup != result.size()) {
        ++stats_.symmetricMovesSkipped;
        if (makerTurn) {
          result[matchingGroup].equivalents.push_back(
              {move, matchingSymmetry});
        }
        continue;
      }
      result.push_back({move, {{move, 0}}});
    }
    return result;
  }

  void store(const CanonicalState& state, GameValue value, Bits rzone = 0) {
    const Bits canonicalRzone = transform(rzone, state.symmetry);
    if (table_.store(state.key, value, canonicalRzone)) {
      ++stats_.tableReplacements;
    }
    ++stats_.tableStores;
  }

  void reportProgress() const {
    constexpr std::uint64_t interval = 1'000'000;
    if (stats_.nodes % interval == 0) {
      std::cerr << "progress nodes=" << stats_.nodes
                << " table=" << table_.size()
                << " pair_calls=" << stats_.pairingCalls
                << " elapsed_s=" << elapsedSeconds() << '\n';
    }
  }

  std::optional<Bits> pairingCertificateRzone(Bits maker, Bits breaker) {
    const StateKey key{maker, breaker};
    ++stats_.pairingCalls;
    if (const std::optional<PairingLookup> cached = pairingTable_.find(key)) {
      ++stats_.pairingCacheHits;
      if (cached->found) {
        ++stats_.pairingWins;
        return cached->rzone;
      }
      return std::nullopt;
    }

    const PairingResult pairing = pairingSolver_.solve(maker, breaker);
    stats_.pairingNodes += pairing.nodes;
    if (pairing.status != PairingStatus::found) {
      pairingTable_.store(key, {false, 0});
      return std::nullopt;
    }
    if (!pairingSolver_.verify(maker, breaker, pairing.pairs)) {
      throw std::logic_error("tree pairing verification failed");
    }
    Bits rzone = 0;
    for (const Pair pair : pairing.pairs) {
      rzone |= (Bits{1} << pair.first) | (Bits{1} << pair.second);
    }
    pairingTable_.store(key, {true, rzone});
    ++stats_.pairingWins;
    return rzone;
  }

  std::optional<Bits> probePairingCertificateRzone(Bits maker,
                                                   Bits breaker) {
    const StateKey key{maker, breaker};
    ++stats_.pairingCalls;
    if (const std::optional<PairingLookup> cached = pairingTable_.find(key)) {
      ++stats_.pairingCacheHits;
      if (cached->found) {
        ++stats_.pairingWins;
        return cached->rzone;
      }
      return std::nullopt;
    }

    const PairingResult pairing = replyPairingSolver_.solve(maker, breaker);
    stats_.pairingNodes += pairing.nodes;
    if (pairing.status != PairingStatus::found) {
      return std::nullopt;
    }
    if (!replyPairingSolver_.verify(maker, breaker, pairing.pairs)) {
      throw std::logic_error("reply pairing verification failed");
    }
    Bits rzone = 0;
    for (const Pair pair : pairing.pairs) {
      rzone |= (Bits{1} << pair.first) | (Bits{1} << pair.second);
    }
    pairingTable_.store(key, {true, rzone});
    ++stats_.pairingWins;
    return rzone;
  }

  SearchResult search(Bits maker, Bits breaker, bool makerTurn,
                      int remainingDepth, int ply) {
    if (stats_.nodes >= maxNodes_) {
      nodeBudgetExhausted_ = true;
      return {};
    }
    ++stats_.nodes;
    stats_.maxPly =
        std::max(stats_.maxPly, static_cast<std::uint64_t>(ply));
    reportProgress();

    if (makerHasWin(maker)) {
      return {GameValue::makerWin, 0};
    }

    const StateKey raw{maker, breaker};
    const CanonicalState state = canonicalState(maker, breaker);
    const StateKey key = state.key;
    if (!(state.key == raw)) {
      ++stats_.symmetryCollapses;
    }
    if (const std::optional<SearchResult> cached = table_.find(key)) {
      ++stats_.tableHits;
      if (cached->value == GameValue::breakerWin) {
        return {cached->value,
                transform(cached->rzone, inverseSymmetry(state.symmetry))};
      }
      return {cached->value, 0};
    }

    const Bits partialPairCells = partialPairReduction(maker, breaker);
    const Bits effectiveBreaker = breaker | partialPairCells;
    const Bits relevant = relevantMoves(maker, effectiveBreaker);
    if (relevant == 0) {
      const SearchResult result{GameValue::breakerWin, partialPairCells};
      store(state, result.value, result.rzone);
      return result;
    }

    const Bits immediateWins = immediateMakerWins(maker, effectiveBreaker);
    if (makerTurn && immediateWins != 0) {
      ++stats_.doubleThreatWins;
      store(state, GameValue::makerWin);
      return {GameValue::makerWin, 0};
    }
    if (!makerTurn) {
      const int threatCount = std::popcount(immediateWins);
      if (threatCount >= 2) {
        ++stats_.doubleThreatWins;
        store(state, GameValue::makerWin);
        return {GameValue::makerWin, 0};
      }
      if (potential(maker, effectiveBreaker) <
          (Bits{1} << spec_.winLength)) {
        ++stats_.potentialWins;
        const SearchResult result{
            GameValue::breakerWin,
            spec_.fullBoard & ~(maker | breaker)};
        store(state, result.value, result.rzone);
        return result;
      }
    }

    if (makerTurn) {
      if (const std::optional<Bits> pairingRzone =
              pairingCertificateRzone(maker, effectiveBreaker)) {
        const SearchResult result{
            GameValue::breakerWin, *pairingRzone | partialPairCells};
        store(state, result.value, result.rzone);
        return result;
      }
    }

    if (remainingDepth == 0) {
      ++stats_.depthLeaves;
      return {};
    }

    Bits moves = relevant;
    const Bits allEmpty =
        spec_.fullBoard & ~(maker | breaker | partialPairCells);
    stats_.irrelevantMovesSkipped +=
        static_cast<std::uint64_t>(std::popcount(allEmpty & ~relevant));
    if (!makerTurn && immediateWins != 0) {
      moves = immediateWins;
      ++stats_.forcedBlocks;
    }
    std::vector<Pair> dominatedMoves;
    const std::vector<MoveGroup> ordered = orderedUniqueMoves(
        moves, maker, effectiveBreaker, breaker, makerTurn,
        dominatedMoves);

    if (!makerTurn &&
        std::popcount(maker | breaker) >= replyProbeMinStones_) {
      const std::size_t probeLimit = std::min(replyProbes_, ordered.size());
      for (std::size_t index = 0; index < probeLimit; ++index) {
        const int move = ordered[index].move;
        const Bits moveBit = Bits{1} << move;
        ++stats_.replyPairingProbes;
        if (const std::optional<Bits> pairingRzone =
                probePairingCertificateRzone(
                    maker, effectiveBreaker | moveBit)) {
          ++stats_.replyPairingWins;
          const SearchResult result{
              GameValue::breakerWin,
              *pairingRzone | moveBit | partialPairCells};
          store(state, result.value, result.rzone);
          return result;
        }
      }
    }

    if (makerTurn) {
      Bits unresolved = moves;
      Bits dominatedBits = 0;
      for (const Pair dominated : dominatedMoves) {
        dominatedBits |= Bits{1} << dominated.first;
      }
      Bits combinedRzone = partialPairCells;
      for (const MoveGroup& group : ordered) {
        bool groupNeeded = false;
        for (const auto [move, symmetry] : group.equivalents) {
          static_cast<void>(symmetry);
          if ((unresolved & (Bits{1} << move)) != 0) {
            groupNeeded = true;
            break;
          }
        }
        if (!groupNeeded) {
          continue;
        }
        const Bits moveBit = Bits{1} << group.move;
        const SearchResult child =
            search(maker | moveBit, breaker, false,
                   remainingDepth - 1, ply + 1);
        if (child.value == GameValue::makerWin) {
          store(state, GameValue::makerWin);
          return {GameValue::makerWin, 0};
        }
        if (child.value == GameValue::unknown) {
          continue;
        }
        for (const auto [equivalentMove, symmetry] : group.equivalents) {
          const Bits equivalentBit = Bits{1} << equivalentMove;
          if ((unresolved & equivalentBit) == 0) {
            continue;
          }
          const Bits equivalentRzone = transform(child.rzone, symmetry);
          combinedRzone |= equivalentRzone;
          const Bits previouslyUnresolved = unresolved;
          unresolved &= equivalentRzone;
          unresolved &= ~equivalentBit;
          stats_.rzoneMovesSkipped += static_cast<std::uint64_t>(
              std::popcount(previouslyUnresolved & ~unresolved &
                            ~equivalentBit));
        }
        if ((unresolved & ~dominatedBits) == 0) {
          break;
        }
      }
      if ((unresolved & ~dominatedBits) == 0) {
        for (const Pair dominated : dominatedMoves) {
          const Bits dominatedBit = Bits{1} << dominated.first;
          if ((unresolved & dominatedBit) != 0) {
            combinedRzone |= Bits{1} << dominated.second;
            unresolved &= ~dominatedBit;
          }
        }
      }
      if (unresolved == 0) {
        ++stats_.rzoneWins;
        const SearchResult result{GameValue::breakerWin, combinedRzone};
        store(state, result.value, result.rzone);
        return result;
      }
    } else {
      bool sawUnknown = false;
      for (const MoveGroup& group : ordered) {
        const int move = group.move;
        const Bits moveBit = Bits{1} << move;
        const SearchResult child =
            search(maker, breaker | (Bits{1} << move), true,
                   remainingDepth - 1, ply + 1);
        if (child.value == GameValue::breakerWin) {
          const SearchResult result{
              GameValue::breakerWin,
              child.rzone | moveBit | partialPairCells};
          store(state, result.value, result.rzone);
          return result;
        }
        sawUnknown = sawUnknown || child.value == GameValue::unknown;
      }
      if (!sawUnknown) {
        store(state, GameValue::makerWin);
        return {GameValue::makerWin, 0};
      }
    }
    return {};
  }

  const BoardSpec& spec_;
  CompactTable table_;
  PairingTable pairingTable_;
  std::uint64_t maxNodes_;
  std::uint64_t maxPairingNodes_;
  std::size_t maxPairBranches_;
  std::size_t replyProbes_;
  int replyProbeMinStones_;
  PairingSolver pairingSolver_;
  PairingSolver replyPairingSolver_;
  int maxDepth_ = 0;
  bool nodeBudgetExhausted_ = false;
  TreeStats stats_;
  Clock::time_point started_;
  std::vector<std::vector<Bits>> transformedBits_;
};

int breakerMoveScore(const BoardSpec& spec, int move, Bits maker) {
  int score = 0;
  for (const int line : spec.linesByCell[static_cast<std::size_t>(move)]) {
    const Bits mask = spec.winningMasks[static_cast<std::size_t>(line)];
    const int makerCount = std::popcount(mask & maker);
    score += 1 << makerCount;
  }
  return score;
}

ReplySearchResult findReplyPairings(const BoardSpec& spec,
                                    std::uint64_t maxPairingNodes,
                                    std::size_t maxPairBranches) {
  ReplySearchResult result;
  result.status = PairingStatus::found;
  PairingSolver solver(spec, maxPairingNodes, maxPairBranches);
  for (const int makerMove : spec.openingRepresentatives()) {
    const Bits maker = Bits{1} << makerMove;
    std::vector<int> replies;
    for (int move = 0; move < spec.cellCount; ++move) {
      if (move != makerMove) {
        replies.push_back(move);
      }
    }
    std::ranges::stable_sort(replies, [&](int left, int right) {
      return breakerMoveScore(spec, left, maker) >
             breakerMoveScore(spec, right, maker);
    });

    bool found = false;
    bool sawNodeLimit = false;
    for (const int breakerMove : replies) {
      ++result.pairingCalls;
      const PairingResult pairing =
          solver.solve(maker, Bits{1} << breakerMove);
      result.pairingNodes += pairing.nodes;
      if (pairing.status == PairingStatus::nodeLimit) {
        sawNodeLimit = true;
      }
      if (pairing.status != PairingStatus::found) {
        continue;
      }
      if (!solver.verify(maker, Bits{1} << breakerMove, pairing.pairs)) {
        throw std::logic_error("internal pairing verification failed");
      }
      result.proofs.push_back({makerMove, breakerMove, pairing.pairs});
      found = true;
      break;
    }
    if (!found) {
      result.status = sawNodeLimit ? PairingStatus::nodeLimit
                                   : PairingStatus::impossible;
      return result;
    }
  }
  return result;
}

void printCell(const BoardSpec& spec, int cell) {
  const auto [x, y] = spec.coordOf(cell);
  std::cout << '(' << x << ',' << y << ')';
}

void printPairs(const BoardSpec& spec, const std::vector<Pair>& pairs) {
  for (std::size_t index = 0; index < pairs.size(); ++index) {
    if (index != 0) {
      std::cout << ' ';
    }
    printCell(spec, pairs[index].first);
    std::cout << '-';
    printCell(spec, pairs[index].second);
  }
  std::cout << '\n';
}

std::uint64_t parseUnsigned(std::string_view text) {
  std::size_t parsed = 0;
  const std::uint64_t value = std::stoull(std::string(text), &parsed);
  if (parsed != text.size()) {
    throw std::invalid_argument("invalid unsigned integer: " +
                                std::string(text));
  }
  return value;
}

struct Options {
  int boardSize = 6;
  std::uint64_t maxPairingNodes = 10'000'000;
  std::size_t maxPairBranches = 2;
  std::size_t replyProbes = 0;
  int replyProbeMinStones = 5;
  std::uint64_t maxReplyPairingNodes = 20;
  std::uint64_t maxSearchNodes = 100'000'000;
  unsigned tablePower = 22;
  int searchDepth = 0;
  int openingOrbit = -1;
  bool staticOnly = false;
  bool skipReplyPairing = false;
};

Options parseOptions(int argc, char** argv) {
  Options options;
  for (int index = 1; index < argc; ++index) {
    const std::string_view argument = argv[index];
    if (argument == "--board" && index + 1 < argc) {
      options.boardSize =
          static_cast<int>(parseUnsigned(argv[++index]));
    } else if (argument == "--pairing-nodes" && index + 1 < argc) {
      options.maxPairingNodes = parseUnsigned(argv[++index]);
    } else if (argument == "--pair-branches" && index + 1 < argc) {
      options.maxPairBranches =
          static_cast<std::size_t>(parseUnsigned(argv[++index]));
    } else if (argument == "--reply-probes" && index + 1 < argc) {
      options.replyProbes =
          static_cast<std::size_t>(parseUnsigned(argv[++index]));
    } else if (argument == "--reply-probe-min-stones" && index + 1 < argc) {
      options.replyProbeMinStones =
          static_cast<int>(parseUnsigned(argv[++index]));
    } else if (argument == "--reply-probe-nodes" && index + 1 < argc) {
      options.maxReplyPairingNodes = parseUnsigned(argv[++index]);
    } else if (argument == "--search-nodes" && index + 1 < argc) {
      options.maxSearchNodes = parseUnsigned(argv[++index]);
    } else if (argument == "--table-power" && index + 1 < argc) {
      options.tablePower =
          static_cast<unsigned>(parseUnsigned(argv[++index]));
    } else if (argument == "--search-depth" && index + 1 < argc) {
      options.searchDepth =
          static_cast<int>(parseUnsigned(argv[++index]));
    } else if (argument == "--opening-orbit" && index + 1 < argc) {
      options.openingOrbit =
          static_cast<int>(parseUnsigned(argv[++index]));
    } else if (argument == "--static-only") {
      options.staticOnly = true;
    } else if (argument == "--skip-reply-pairing") {
      options.skipReplyPairing = true;
    } else {
      throw std::invalid_argument("unknown or incomplete option: " +
                                  std::string(argument));
    }
  }
  return options;
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const Options options = parseOptions(argc, argv);
    const BoardSpec spec(options.boardSize);
    const auto started = std::chrono::steady_clock::now();
    PairingSolver solver(spec, options.maxPairingNodes,
                         options.maxPairBranches);
    const PairingResult staticPairing = solver.solve(0, 0);

    std::cout << "self_check=passed\n";
    std::cout << "board=" << spec.boardSize << 'x' << spec.boardSize << '\n';
    std::cout << "win_length=" << spec.winLength << '\n';
    std::cout << "winning_lines=" << spec.winningMasks.size() << '\n';
    std::cout << "method=maker_breaker_pairing\n";
    std::cout << "static_pairing_status="
              << pairingStatusName(staticPairing.status) << '\n';
    std::cout << "static_pairing_nodes=" << staticPairing.nodes << '\n';
    if (staticPairing.status == PairingStatus::found) {
      if (!solver.verify(0, 0, staticPairing.pairs)) {
        throw std::logic_error("static pairing verification failed");
      }
      std::cout << "result_for_black=draw\n";
      std::cout << "pair_count=" << staticPairing.pairs.size() << '\n';
      std::cout << "pairs=";
      printPairs(spec, staticPairing.pairs);
    } else if (!options.staticOnly) {
      ReplySearchResult replyResult;
      if (options.skipReplyPairing) {
        replyResult.status = PairingStatus::nodeLimit;
        std::cout << "reply_pairing_status=skipped\n";
      } else {
        replyResult = findReplyPairings(spec, options.maxPairingNodes,
                                        options.maxPairBranches);
        std::cout << "reply_pairing_status="
                  << pairingStatusName(replyResult.status) << '\n';
      }
      std::cout << "opening_orbits="
                << spec.openingRepresentatives().size() << '\n';
      std::cout << "proved_opening_orbits=" << replyResult.proofs.size()
                << '\n';
      std::cout << "pairing_calls=" << replyResult.pairingCalls << '\n';
      std::cout << "pairing_nodes=" << replyResult.pairingNodes << '\n';
      if (replyResult.status == PairingStatus::found) {
        std::cout << "result_for_black=draw\n";
        for (const ReplyProof& proof : replyResult.proofs) {
          std::cout << "opening=";
          printCell(spec, proof.makerMove);
          std::cout << " reply=";
          printCell(spec, proof.breakerMove);
          std::cout << " pair_count=" << proof.pairs.size() << '\n';
          std::cout << "pairs=";
          printPairs(spec, proof.pairs);
        }
      } else if (options.searchDepth > 0) {
        DrawTreeSolver treeSolver(spec, options.tablePower,
                                  options.maxSearchNodes,
                                  options.maxPairingNodes,
                                  options.maxPairBranches,
                                  options.replyProbes,
                                  options.replyProbeMinStones,
                                  options.maxReplyPairingNodes);
        GameValue treeValue = GameValue::unknown;
        if (options.openingOrbit >= 0) {
          const std::vector<int> openings = spec.openingRepresentatives();
          if (static_cast<std::size_t>(options.openingOrbit) >=
              openings.size()) {
            throw std::invalid_argument("opening orbit index is out of range");
          }
          const int opening =
              openings[static_cast<std::size_t>(options.openingOrbit)];
          std::cout << "tree_scope=opening_orbit\n";
          std::cout << "tree_opening_orbit=" << options.openingOrbit << '\n';
          std::cout << "tree_opening=";
          printCell(spec, opening);
          std::cout << '\n';
          treeValue = treeSolver.solvePosition(
              Bits{1} << opening, 0, false, options.searchDepth);
        } else {
          std::cout << "tree_scope=full_game\n";
          treeValue = treeSolver.solve(options.searchDepth);
        }
        const TreeStats& stats = treeSolver.stats();
        std::cout << "tree_value=" << gameValueName(treeValue) << '\n';
        std::cout << "tree_depth=" << options.searchDepth << '\n';
        std::cout << "tree_nodes=" << stats.nodes << '\n';
        std::cout << "tree_table_entries=" << treeSolver.tableSize() << '\n';
        std::cout << "tree_table_capacity=" << treeSolver.tableCapacity()
                  << '\n';
        std::cout << "tree_table_bytes=" << treeSolver.tableBytes() << '\n';
        std::cout << "tree_pairing_table_capacity="
                  << treeSolver.pairingTableCapacity() << '\n';
        std::cout << "tree_pairing_table_bytes="
                  << treeSolver.pairingTableBytes() << '\n';
        std::cout << "tree_table_hits=" << stats.tableHits << '\n';
        std::cout << "tree_table_replacements=" << stats.tableReplacements
                  << '\n';
        std::cout << "tree_symmetry_collapses=" << stats.symmetryCollapses
                  << '\n';
        std::cout << "tree_symmetric_moves_skipped="
                  << stats.symmetricMovesSkipped << '\n';
        std::cout << "tree_dominated_moves_skipped="
                  << stats.dominatedMovesSkipped << '\n';
        std::cout << "tree_pairing_calls=" << stats.pairingCalls << '\n';
        std::cout << "tree_pairing_cache_hits="
                  << stats.pairingCacheHits << '\n';
        std::cout << "tree_pairing_nodes=" << stats.pairingNodes << '\n';
        std::cout << "tree_pairing_wins=" << stats.pairingWins << '\n';
        std::cout << "tree_reply_pairing_probes="
                  << stats.replyPairingProbes << '\n';
        std::cout << "tree_reply_pairing_wins="
                  << stats.replyPairingWins << '\n';
        std::cout << "tree_potential_wins=" << stats.potentialWins << '\n';
        std::cout << "tree_partial_pairs=" << stats.partialPairs << '\n';
        std::cout << "tree_partial_pair_cells_removed="
                  << stats.partialPairCellsRemoved << '\n';
        std::cout << "tree_forced_blocks=" << stats.forcedBlocks << '\n';
        std::cout << "tree_double_threat_wins=" << stats.doubleThreatWins
                  << '\n';
        std::cout << "tree_irrelevant_moves_skipped="
                  << stats.irrelevantMovesSkipped << '\n';
        std::cout << "tree_rzone_moves_skipped="
                  << stats.rzoneMovesSkipped << '\n';
        std::cout << "tree_rzone_wins=" << stats.rzoneWins << '\n';
        std::cout << "tree_depth_leaves=" << stats.depthLeaves << '\n';
        std::cout << "tree_max_ply=" << stats.maxPly << '\n';
        std::cout << "tree_node_budget_exhausted="
                  << (treeSolver.nodeBudgetExhausted() ? "true" : "false")
                  << '\n';
        std::cout << "tree_elapsed_s=" << treeSolver.elapsedSeconds() << '\n';
        if (options.openingOrbit >= 0) {
          std::cout << "opening_result_for_black="
                    << (treeValue == GameValue::breakerWin ? "draw"
                                                           : "unknown")
                    << '\n';
          std::cout << "result_for_black=unknown\n";
        } else {
          std::cout << "result_for_black="
                    << (treeValue == GameValue::breakerWin ? "draw"
                                                           : "unknown")
                    << '\n';
        }
      } else {
        std::cout << "result_for_black=unknown\n";
      }
    } else {
      std::cout << "result_for_black=unknown\n";
    }

    const double elapsed = std::chrono::duration<double>(
                               std::chrono::steady_clock::now() - started)
                               .count();
    std::cout << "elapsed_s=" << elapsed << '\n';
    return 0;
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return 1;
  }
}
