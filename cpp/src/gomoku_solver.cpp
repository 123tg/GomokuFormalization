#include "gomoku_solver.hpp"

#include <algorithm>
#include <cctype>
#include <iterator>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <string_view>
#include <unordered_map>
#include <utility>

namespace gomoku {
namespace {

constexpr std::uint32_t infinity = 1U << 30;
constexpr std::size_t noParent = static_cast<std::size_t>(-1);

int indexOf(Coord move) {
  return move.y * boardSize + move.x;
}

std::uint64_t splitMix64(std::uint64_t value) {
  value += 0x9e3779b97f4a7c15ULL;
  value = (value ^ (value >> 30U)) * 0xbf58476d1ce4e5b9ULL;
  value = (value ^ (value >> 27U)) * 0x94d049bb133111ebULL;
  return value ^ (value >> 31U);
}

std::uint64_t stoneHash(Coord move, Player player) {
  const std::uint64_t salt = player == Player::black
      ? 0x243f6a8885a308d3ULL
      : 0x13198a2e03707344ULL;
  return splitMix64(static_cast<std::uint64_t>(indexOf(move)) ^ salt);
}

std::uint32_t saturatedAdd(std::uint32_t lhs, std::uint32_t rhs) {
  if (lhs >= infinity || rhs >= infinity || lhs > infinity - rhs) {
    return infinity;
  }
  return lhs + rhs;
}

std::uint32_t plusOne(std::uint32_t value) {
  return value >= infinity ? infinity : value + 1U;
}

Cell playerCell(Player player) {
  return player == Player::black ? Cell::black : Cell::white;
}

Outcome playerOutcome(Player player) {
  return player == Player::black ? Outcome::blackWin : Outcome::whiteWin;
}

std::string trim(std::string value) {
  const auto first = std::find_if_not(value.begin(), value.end(),
      [](unsigned char ch) { return std::isspace(ch) != 0; });
  const auto last = std::find_if_not(value.rbegin(), value.rend(),
      [](unsigned char ch) { return std::isspace(ch) != 0; }).base();
  if (first >= last) {
    return {};
  }
  return std::string(first, last);
}

std::string lower(std::string value) {
  std::transform(value.begin(), value.end(), value.begin(),
      [](unsigned char ch) { return static_cast<char>(std::tolower(ch)); });
  return value;
}

Player parsePlayer(const std::string& value) {
  const std::string normalized = lower(trim(value));
  if (normalized == "black" || normalized == "b" || normalized == "x") {
    return Player::black;
  }
  if (normalized == "white" || normalized == "w" || normalized == "o") {
    return Player::white;
  }
  throw std::runtime_error("expected player black or white, got: " + value);
}

const char* leanPlayer(Player player) {
  return player == Player::black ? ".black" : ".white";
}

const char* leanOutcome(Outcome outcome) {
  switch (outcome) {
    case Outcome::blackWin:
      return ".blackWin";
    case Outcome::whiteWin:
      return ".whiteWin";
    case Outcome::draw:
      return ".draw";
  }
  return ".draw";
}

std::string leanCoord(Coord move) {
  return "(" + std::to_string(move.x) + ", " +
      std::to_string(move.y) + ")";
}

std::string sanitizeIdentifier(std::string value) {
  if (value.empty()) {
    return "cppGenerated";
  }
  for (char& ch : value) {
    const unsigned char uch = static_cast<unsigned char>(ch);
    if (std::isalnum(uch) == 0 && ch != '_') {
      ch = '_';
    }
  }
  if (std::isalpha(static_cast<unsigned char>(value.front())) == 0 &&
      value.front() != '_') {
    value.insert(value.begin(), '_');
  }
  return value;
}

struct StateKey {
  std::array<std::uint64_t, 4> black{};
  std::array<std::uint64_t, 4> white{};
  std::uint64_t zobrist = 0;
  std::uint16_t depth = 0;
  Player turn = Player::black;
  Player target = Player::black;

  friend bool operator==(const StateKey& lhs, const StateKey& rhs) {
    return lhs.depth == rhs.depth && lhs.turn == rhs.turn &&
        lhs.target == rhs.target && lhs.black == rhs.black &&
        lhs.white == rhs.white;
  }
};

struct StateKeyHash {
  std::size_t operator()(const StateKey& key) const {
    std::uint64_t value = key.zobrist;
    value ^= splitMix64(static_cast<std::uint64_t>(key.depth) << 2U);
    value ^= key.turn == Player::black ? 0x452821e638d01377ULL
                                       : 0xbe5466cf34e90c6cULL;
    value ^= key.target == Player::black ? 0xc0ac29b7c97c50ddULL
                                         : 0x3f84d5b5b5470917ULL;
    return static_cast<std::size_t>(splitMix64(value));
  }
};

StateKey makeKey(const Position& position, std::uint16_t depth,
                 Player target) {
  return {position.board.black, position.board.white, position.board.zobrist,
          depth, position.turn, target};
}

struct Entry {
  std::uint32_t proof = 1;
  std::uint32_t disproof = 1;
  bool expanded = false;
  std::vector<Coord> moves;
};

struct VcfEntry {
  std::optional<Coord> move;
};

struct ScoredMove {
  Coord move;
  bool winning = false;
  bool defense = false;
  int score = 0;
};

int neighborhoodScore(const Board& board, Coord move) {
  int score = 0;
  for (int dy = -2; dy <= 2; ++dy) {
    for (int dx = -2; dx <= 2; ++dx) {
      if (dx == 0 && dy == 0) {
        continue;
      }
      const Coord neighbor{move.x + dx, move.y + dy};
      if (board.inside(neighbor) && board.at(neighbor) != Cell::empty) {
        score += (std::abs(dx) <= 1 && std::abs(dy) <= 1) ? 8 : 2;
      }
    }
  }
  score -= std::abs(move.x - boardSize / 2) +
      std::abs(move.y - boardSize / 2);
  return score;
}

}  // namespace

Player other(Player player) {
  return player == Player::black ? Player::white : Player::black;
}

const char* playerName(Player player) {
  return player == Player::black ? "black" : "white";
}

bool Board::inside(Coord move) const {
  return move.x >= 0 && move.x < boardSize && move.y >= 0 &&
      move.y < boardSize;
}

Cell Board::at(Coord move) const {
  if (!inside(move)) {
    throw std::out_of_range("coordinate outside 7x7 board");
  }
  const int index = indexOf(move);
  const std::uint64_t mask = 1ULL << (index % 64);
  const std::size_t word = static_cast<std::size_t>(index / 64);
  if ((black[word] & mask) != 0) {
    return Cell::black;
  }
  if ((white[word] & mask) != 0) {
    return Cell::white;
  }
  return Cell::empty;
}

bool Board::isEmpty(Coord move) const {
  return inside(move) && at(move) == Cell::empty;
}

void Board::place(Coord move, Player player) {
  if (!inside(move)) {
    throw std::out_of_range("cannot place outside 7x7 board");
  }
  if (!isEmpty(move)) {
    throw std::runtime_error("cannot place on an occupied point");
  }
  const int index = indexOf(move);
  const std::uint64_t mask = 1ULL << (index % 64);
  const std::size_t word = static_cast<std::size_t>(index / 64);
  (player == Player::black ? black[word] : white[word]) |= mask;
  ++stones;
  zobrist ^= stoneHash(move, player);
}

bool Board::full() const {
  return stones == boardCells;
}

bool Board::createsFive(Coord move, Player player) const {
  if (!isEmpty(move)) {
    return false;
  }
  constexpr std::array<Coord, 4> directions{{
      {1, 0}, {0, 1}, {1, 1}, {1, -1}}};
  const Cell stone = playerCell(player);
  for (const Coord direction : directions) {
    int length = 1;
    for (int sign : {-1, 1}) {
      Coord cursor{move.x + sign * direction.x,
                   move.y + sign * direction.y};
      while (inside(cursor) && at(cursor) == stone) {
        ++length;
        cursor.x += sign * direction.x;
        cursor.y += sign * direction.y;
      }
    }
    if (length >= winLength) {
      return true;
    }
  }
  return false;
}

bool Board::hasFive(Player player) const {
  constexpr std::array<Coord, 4> directions{{
      {1, 0}, {0, 1}, {1, 1}, {1, -1}}};
  const Cell stone = playerCell(player);
  for (int y = 0; y < boardSize; ++y) {
    for (int x = 0; x < boardSize; ++x) {
      const Coord start{x, y};
      if (at(start) != stone) {
        continue;
      }
      for (const Coord direction : directions) {
        const Coord before{x - direction.x, y - direction.y};
        if (inside(before) && at(before) == stone) {
          continue;
        }
        int length = 0;
        Coord cursor = start;
        while (inside(cursor) && at(cursor) == stone) {
          ++length;
          cursor.x += direction.x;
          cursor.y += direction.y;
        }
        if (length >= winLength) {
          return true;
        }
      }
    }
  }
  return false;
}

std::optional<Outcome> Board::terminal() const {
  // This order intentionally matches Gomoku.Position.terminal.
  if (hasFive(Player::black)) {
    return Outcome::blackWin;
  }
  if (hasFive(Player::white)) {
    return Outcome::whiteWin;
  }
  if (full()) {
    return Outcome::draw;
  }
  return std::nullopt;
}

std::vector<Coord> Board::emptyMoves() const {
  std::vector<Coord> result;
  result.reserve(boardCells - stones);
  for (int y = 0; y < boardSize; ++y) {
    for (int x = 0; x < boardSize; ++x) {
      const Coord move{x, y};
      if (isEmpty(move)) {
        result.push_back(move);
      }
    }
  }
  return result;
}

Position play(const Position& position, Coord move) {
  if (position.board.terminal().has_value()) {
    throw std::runtime_error("cannot play from a terminal position");
  }
  Position child = position;
  child.board.place(move, position.turn);
  child.turn = other(position.turn);
  return child;
}

const char* solveStatusName(SolveStatus status) {
  switch (status) {
    case SolveStatus::found:
      return "found";
    case SolveStatus::depthLimit:
      return "depth-limit";
    case SolveStatus::nodeLimit:
      return "node-limit";
    case SolveStatus::tableLimit:
      return "table-limit";
    case SolveStatus::certificateLimit:
      return "certificate-limit";
  }
  return "unknown";
}

struct DfpnSolver::Impl {
  SearchConfig config;
  Player target;
  std::unordered_map<StateKey, Entry, StateKeyHash> table;
  std::unordered_map<StateKey, VcfEntry, StateKeyHash> vcfTable;
  std::unordered_map<StateKey, Coord, StateKeyHash> vcfHints;
  SearchStats stats;
  SolveStatus limitStatus = SolveStatus::depthLimit;
  bool stopped = false;
  bool vcfStopped = false;

  explicit Impl(SearchConfig configValue, Player targetValue)
      : config(configValue), target(targetValue) {
    table.reserve(std::min<std::size_t>(config.maxTableEntries == 0
        ? 262'144 : config.maxTableEntries, 262'144));
    vcfTable.reserve(static_cast<std::size_t>(std::min<std::uint64_t>(
        config.maxVcfNodes == 0 ? 65'536 : config.maxVcfNodes, 65'536)));
    vcfHints.reserve(4'096);
  }

  Entry* ensureEntry(const Position& position, std::uint16_t depth) {
    const StateKey key = makeKey(position, depth, target);
    auto found = table.find(key);
    if (found != table.end()) {
      ++stats.tableHits;
      return &found->second;
    }
    if (config.maxTableEntries != 0 &&
        table.size() >= config.maxTableEntries) {
      stopped = true;
      limitStatus = SolveStatus::tableLimit;
      return nullptr;
    }

    Entry entry;
    const auto terminal = position.board.terminal();
    if (terminal.has_value()) {
      entry.expanded = true;
      if (*terminal == playerOutcome(target)) {
        entry.proof = 0;
        entry.disproof = infinity;
      } else {
        entry.proof = infinity;
        entry.disproof = 0;
      }
    } else if (depth == 0) {
      // This is a disproof only for the bounded-depth query.
      entry.expanded = true;
      entry.proof = infinity;
      entry.disproof = 0;
    }
    auto inserted = table.emplace(key, std::move(entry));
    return &inserted.first->second;
  }

  std::vector<Coord> sortedEmptyMoves(const Board& board) const {
    std::vector<Coord> moves = board.emptyMoves();
    std::stable_sort(moves.begin(), moves.end(),
        [&board](Coord lhs, Coord rhs) {
          const int lhsScore = neighborhoodScore(board, lhs);
          const int rhsScore = neighborhoodScore(board, rhs);
          if (lhsScore != rhsScore) {
            return lhsScore > rhsScore;
          }
          if (lhs.y != rhs.y) {
            return lhs.y < rhs.y;
          }
          return lhs.x < rhs.x;
        });
    return moves;
  }

  std::vector<Coord> winningMoves(const Board& board, Player player) const {
    std::vector<Coord> result;
    for (const Coord move : sortedEmptyMoves(board)) {
      if (board.createsFive(move, player)) {
        result.push_back(move);
      }
    }
    return result;
  }

  std::optional<Coord> finishVcf(const StateKey& key,
                                 const Position& position,
                                 std::optional<Coord> move) {
    vcfTable.insert_or_assign(key, VcfEntry{move});
    if (move.has_value()) {
      vcfHints.insert_or_assign(makeKey(position, 0, target), *move);
    }
    return move;
  }

  std::optional<Coord> probeVcf(const Position& position,
                                std::uint16_t remaining) {
    const StateKey key = makeKey(position, remaining, target);
    const auto cached = vcfTable.find(key);
    if (cached != vcfTable.end()) {
      ++stats.vcfTableHits;
      return cached->second.move;
    }
    if (vcfStopped) {
      return std::nullopt;
    }
    if (config.maxVcfNodes != 0 &&
        stats.vcfNodes >= config.maxVcfNodes) {
      stats.vcfBudgetExhausted = true;
      vcfStopped = true;
      return std::nullopt;
    }
    ++stats.vcfNodes;

    if (remaining == 0 || position.turn != target ||
        position.board.terminal().has_value()) {
      return finishVcf(key, position, std::nullopt);
    }

    const std::vector<Coord> candidates = sortedEmptyMoves(position.board);
    for (const Coord move : candidates) {
      if (position.board.createsFive(move, target)) {
        return finishVcf(key, position, move);
      }
    }
    if (remaining < 3) {
      return finishVcf(key, position, std::nullopt);
    }

    for (const Coord move : candidates) {
      if (vcfStopped) {
        return std::nullopt;
      }
      const Position afterAttack = play(position, move);
      const auto outcome = afterAttack.board.terminal();
      if (outcome.has_value()) {
        if (*outcome == playerOutcome(target)) {
          return finishVcf(key, position, move);
        }
        continue;
      }

      const std::vector<Coord> targetThreats =
          winningMoves(afterAttack.board, target);
      if (targetThreats.empty()) {
        continue;
      }
      if (!winningMoves(afterAttack.board, other(target)).empty()) {
        continue;
      }
      if (targetThreats.size() >= 2) {
        return finishVcf(key, position, move);
      }

      const Position afterBlock = play(afterAttack, targetThreats.front());
      if (afterBlock.board.terminal().has_value()) {
        continue;
      }
      const auto continuation = probeVcf(
          afterBlock, static_cast<std::uint16_t>(remaining - 2));
      if (continuation.has_value()) {
        return finishVcf(key, position, move);
      }
      if (vcfStopped) {
        return std::nullopt;
      }
    }
    return finishVcf(key, position, std::nullopt);
  }

  std::vector<Coord> orderedMoves(const Position& position) const {
    std::vector<ScoredMove> scored;
    for (const Coord move : position.board.emptyMoves()) {
      const bool winning = position.board.createsFive(move, position.turn);
      const bool defense = !winning &&
          position.board.createsFive(move, other(position.turn));
      int score = neighborhoodScore(position.board, move);
      if (winning) {
        score += 1'000'000;
      } else if (defense) {
        score += 500'000;
      }
      scored.push_back({move, winning, defense, score});
    }
    std::stable_sort(scored.begin(), scored.end(),
        [](const ScoredMove& lhs, const ScoredMove& rhs) {
          if (lhs.score != rhs.score) {
            return lhs.score > rhs.score;
          }
          if (lhs.move.y != rhs.move.y) {
            return lhs.move.y < rhs.move.y;
          }
          return lhs.move.x < rhs.move.x;
        });

    const bool prover = position.turn == target;
    const bool hasWinning = std::any_of(scored.begin(), scored.end(),
        [](const ScoredMove& move) { return move.winning; });
    const bool hasDefense = std::any_of(scored.begin(), scored.end(),
        [](const ScoredMove& move) { return move.defense; });

    std::vector<Coord> result;
    result.reserve(scored.size());
    for (const ScoredMove& move : scored) {
      if (prover && config.forcedMovePruning) {
        if (hasWinning && !move.winning) {
          continue;
        }
        if (!hasWinning && hasDefense && !move.defense) {
          continue;
        }
      }
      result.push_back(move.move);
    }
    if (prover) {
      const auto hint = vcfHints.find(makeKey(position, 0, target));
      if (hint != vcfHints.end()) {
        const auto preferred = std::find(result.begin(), result.end(),
                                         hint->second);
        if (preferred != result.end()) {
          std::rotate(result.begin(), preferred, std::next(preferred));
        }
      }
    }
    if (prover && config.maxProverMoves != 0 &&
        result.size() > config.maxProverMoves) {
      result.resize(config.maxProverMoves);
    }
    return result;
  }

  void recompute(const Position& position, std::uint16_t depth) {
    const StateKey key = makeKey(position, depth, target);
    auto currentIt = table.find(key);
    if (currentIt == table.end()) {
      stopped = true;
      limitStatus = SolveStatus::tableLimit;
      return;
    }
    const std::vector<Coord> moves = currentIt->second.moves;
    if (moves.empty()) {
      currentIt->second.proof = infinity;
      currentIt->second.disproof = 0;
      return;
    }

    const bool prover = position.turn == target;
    std::uint32_t proof = prover ? infinity : 0;
    std::uint32_t disproof = prover ? 0 : infinity;
    for (const Coord move : moves) {
      const Position child = play(position, move);
      const StateKey childKey = makeKey(child,
          static_cast<std::uint16_t>(depth - 1), target);
      const auto childIt = table.find(childKey);
      if (childIt == table.end()) {
        stopped = true;
        limitStatus = SolveStatus::tableLimit;
        return;
      }
      if (prover) {
        proof = std::min(proof, childIt->second.proof);
        disproof = saturatedAdd(disproof, childIt->second.disproof);
      } else {
        proof = saturatedAdd(proof, childIt->second.proof);
        disproof = std::min(disproof, childIt->second.disproof);
      }
    }
    currentIt = table.find(key);
    currentIt->second.proof = proof;
    currentIt->second.disproof = disproof;
  }

  void expand(const Position& position, std::uint16_t depth) {
    Entry* current = ensureEntry(position, depth);
    if (current == nullptr || current->expanded) {
      return;
    }
    if (config.maxNodes != 0 && stats.expandedNodes >= config.maxNodes) {
      stopped = true;
      limitStatus = SolveStatus::nodeLimit;
      return;
    }
    ++stats.expandedNodes;
    current->moves = orderedMoves(position);
    current->expanded = true;
    const std::vector<Coord> moves = current->moves;
    for (const Coord move : moves) {
      const Position child = play(position, move);
      if (ensureEntry(child, static_cast<std::uint16_t>(depth - 1)) == nullptr) {
        return;
      }
    }
    recompute(position, depth);
  }

  void dfpn(const Position& position, std::uint16_t depth,
            std::uint32_t proofThreshold,
            std::uint32_t disproofThreshold) {
    Entry* initial = ensureEntry(position, depth);
    if (initial == nullptr || stopped || initial->proof == 0 ||
        initial->disproof == 0) {
      return;
    }
    expand(position, depth);

    while (!stopped) {
      const StateKey key = makeKey(position, depth, target);
      const auto currentIt = table.find(key);
      if (currentIt == table.end()) {
        stopped = true;
        limitStatus = SolveStatus::tableLimit;
        return;
      }
      const Entry current = currentIt->second;
      if (current.proof == 0 || current.disproof == 0 ||
          current.proof >= proofThreshold ||
          current.disproof >= disproofThreshold || current.moves.empty()) {
        return;
      }

      const bool prover = position.turn == target;
      std::size_t bestIndex = 0;
      std::uint32_t bestValue = infinity;
      std::uint32_t secondValue = infinity;
      std::uint32_t bestProof = infinity;
      std::uint32_t bestDisproof = infinity;

      for (std::size_t index = 0; index < current.moves.size(); ++index) {
        const Position child = play(position, current.moves[index]);
        const auto childIt = table.find(makeKey(child,
            static_cast<std::uint16_t>(depth - 1), target));
        if (childIt == table.end()) {
          stopped = true;
          limitStatus = SolveStatus::tableLimit;
          return;
        }
        const std::uint32_t value = prover ? childIt->second.proof
                                           : childIt->second.disproof;
        if (value < bestValue) {
          secondValue = bestValue;
          bestValue = value;
          bestIndex = index;
          bestProof = childIt->second.proof;
          bestDisproof = childIt->second.disproof;
        } else if (value < secondValue) {
          secondValue = value;
        }
      }

      const Coord selectedMove = current.moves[bestIndex];
      const Position selected = play(position, selectedMove);
      std::uint32_t childProofThreshold;
      std::uint32_t childDisproofThreshold;
      if (prover) {
        childProofThreshold = std::min(proofThreshold,
            plusOne(secondValue));
        childDisproofThreshold = saturatedAdd(
            disproofThreshold - current.disproof, bestDisproof);
      } else {
        childProofThreshold = saturatedAdd(
            proofThreshold - current.proof, bestProof);
        childDisproofThreshold = std::min(disproofThreshold,
            plusOne(secondValue));
      }

      dfpn(selected, static_cast<std::uint16_t>(depth - 1),
           childProofThreshold, childDisproofThreshold);
      if (stopped) {
        return;
      }
      const auto selectedAfter = table.find(makeKey(
          selected, static_cast<std::uint16_t>(depth - 1), target));
      if (selectedAfter == table.end()) {
        stopped = true;
        limitStatus = SolveStatus::tableLimit;
        return;
      }
      if (selectedAfter->second.proof == bestProof &&
          selectedAfter->second.disproof == bestDisproof) {
        return;
      }
      recompute(position, depth);
    }
  }

  std::size_t emitProof(const Position& position, std::uint16_t depth,
                        Certificate& certificate,
                        std::size_t sourceParent,
                        Coord sourceMove) {
    if (config.maxCertificateNodes != 0 &&
        certificate.nodes.size() >= config.maxCertificateNodes) {
      throw std::length_error("certificate node limit reached");
    }
    const StateKey key = makeKey(position, depth, target);
    const auto found = table.find(key);
    if (found == table.end() || found->second.proof != 0) {
      throw std::logic_error("attempted to emit an unproved DFPN node");
    }

    const std::size_t index = certificate.nodes.size();
    CertificateNode placeholder;
    placeholder.position = position;
    placeholder.sourceParent = sourceParent;
    placeholder.sourceMove = sourceMove;
    certificate.nodes.push_back(std::move(placeholder));

    const auto terminal = position.board.terminal();
    if (terminal.has_value()) {
      certificate.nodes[index].kind = CertificateKind::terminal;
      certificate.nodes[index].outcome = *terminal;
      return index;
    }

    const std::vector<Coord> moves = found->second.moves;
    if (position.turn == target) {
      for (const Coord move : moves) {
        const Position childPosition = play(position, move);
        const auto childIt = table.find(makeKey(childPosition,
            static_cast<std::uint16_t>(depth - 1), target));
        if (childIt != table.end() && childIt->second.proof == 0) {
          certificate.nodes[index].kind = CertificateKind::proverMove;
          certificate.nodes[index].move = move;
          const std::size_t child = emitProof(childPosition,
              static_cast<std::uint16_t>(depth - 1), certificate, index, move);
          certificate.nodes[index].child = child;
          return index;
        }
      }
      throw std::logic_error("proved OR node has no proved child");
    }

    certificate.nodes[index].kind = CertificateKind::opponentMoves;
    for (const Coord move : moves) {
      const Position childPosition = play(position, move);
      const auto childIt = table.find(makeKey(childPosition,
          static_cast<std::uint16_t>(depth - 1), target));
      if (childIt == table.end() || childIt->second.proof != 0) {
        throw std::logic_error("proved AND node has an unproved child");
      }
      const std::size_t child = emitProof(childPosition,
          static_cast<std::uint16_t>(depth - 1), certificate, index, move);
      certificate.nodes[index].children.push_back({move, child});
    }
    return index;
  }

  SolveResult solve(const Position& root) {
    stats = {};
    table.clear();
    vcfTable.clear();
    vcfHints.clear();
    stopped = false;
    vcfStopped = false;
    limitStatus = SolveStatus::depthLimit;

    SolveResult result;
    if (config.maxVcfDepth != 0 && root.turn == target) {
      const std::uint16_t horizon = std::min(config.maxVcfDepth,
                                             config.maxDepth);
      stats.vcfRootSolved = probeVcf(root, horizon).has_value();
    }
    for (std::uint32_t depthValue = 0; depthValue <= config.maxDepth;
         ++depthValue) {
      const auto depth = static_cast<std::uint16_t>(depthValue);
      dfpn(root, depth, infinity, infinity);
      if (stopped) {
        result.status = limitStatus;
        result.stats = stats;
        result.stats.tableEntries = table.size();
        return result;
      }
      const auto rootIt = table.find(makeKey(root, depth, target));
      if (rootIt != table.end() && rootIt->second.proof == 0) {
        Certificate certificate;
        certificate.target = target;
        try {
          emitProof(root, depth, certificate, noParent, {});
        } catch (const std::length_error&) {
          result.status = SolveStatus::certificateLimit;
          result.stats = stats;
          result.stats.tableEntries = table.size();
          return result;
        }
        result.status = SolveStatus::found;
        result.depth = depth;
        result.certificate = std::move(certificate);
        result.stats = stats;
        result.stats.tableEntries = table.size();
        return result;
      }
    }

    result.status = SolveStatus::depthLimit;
    result.stats = stats;
    result.stats.tableEntries = table.size();
    return result;
  }
};

DfpnSolver::DfpnSolver(SearchConfig config, Player target)
    : impl_(std::make_unique<Impl>(config, target)) {}

DfpnSolver::~DfpnSolver() = default;
DfpnSolver::DfpnSolver(DfpnSolver&&) noexcept = default;
DfpnSolver& DfpnSolver::operator=(DfpnSolver&&) noexcept = default;

SolveResult DfpnSolver::solve(const Position& root) {
  return impl_->solve(root);
}

// ---------------------------------------------------------------------------
// Defense proof search
// ---------------------------------------------------------------------------

namespace {

enum class ProofState : std::uint8_t {
  found,
  refuted,
  unknown,
};

struct DefenseStateKey {
  std::array<std::uint64_t, 4> black{};
  std::array<std::uint64_t, 4> white{};
  std::uint64_t zobrist = 0;
  Player turn = Player::black;
  Player defender = Player::white;

  friend bool operator==(const DefenseStateKey& lhs, const DefenseStateKey& rhs) {
    return lhs.turn == rhs.turn && lhs.defender == rhs.defender &&
        lhs.black == rhs.black && lhs.white == rhs.white;
  }
};

struct DefenseStateKeyHash {
  std::size_t operator()(const DefenseStateKey& key) const {
    std::uint64_t value = key.zobrist;
    value ^= splitMix64(key.turn == Player::black ? 0x1'0000'0001ULL
                                                  : 0x2'0000'0002ULL);
    value ^= splitMix64(key.defender == Player::black ? 0x3'0000'0003ULL
                                                      : 0x4'0000'0004ULL);
    return static_cast<std::size_t>(splitMix64(value));
  }
};

DefenseStateKey makeDefenseKey(const Position& position, Player defender) {
  DefenseStateKey key;
  key.black = position.board.black;
  key.white = position.board.white;
  key.zobrist = position.board.zobrist;
  key.turn = position.turn;
  key.defender = defender;
  return key;
}

enum class DefenseStatus : std::uint8_t {
  found,
  refuted,
};

struct DefenseEntry {
  DefenseStatus status = DefenseStatus::refuted;
  std::optional<Coord> chosenMove;
};

}  // namespace

const char* proofSearchStatusName(ProofSearchStatus status) {
  switch (status) {
    case ProofSearchStatus::found:
      return "found";
    case ProofSearchStatus::refuted:
      return "refuted";
    case ProofSearchStatus::unknown:
      return "unknown";
  }
  return "unknown";
}

struct DefenseSearcher::Impl {
  SearchConfig config;
  Player defender;
  std::unordered_map<DefenseStateKey, DefenseEntry, DefenseStateKeyHash> table;
  SearchStats stats;
  std::uint16_t maxDepthReached = 0;
  bool stopped = false;
  std::string unknownReason;

  explicit Impl(SearchConfig configValue, Player defenderValue)
      : config(configValue), defender(defenderValue) {
    table.reserve(std::min<std::size_t>(config.maxTableEntries == 0
        ? 262'144 : config.maxTableEntries, 262'144));
  }

  std::vector<Coord> orderedEmptyMoves(const Board& board) const {
    std::vector<Coord> moves = board.emptyMoves();
    std::stable_sort(moves.begin(), moves.end(),
        [&board](Coord lhs, Coord rhs) {
          const int lhsScore = neighborhoodScore(board, lhs);
          const int rhsScore = neighborhoodScore(board, rhs);
          if (lhsScore != rhsScore) {
            return lhsScore > rhsScore;
          }
          if (lhs.y != rhs.y) {
            return lhs.y < rhs.y;
          }
          return lhs.x < rhs.x;
        });
    return moves;
  }

  // Complete AND/OR proof search for "defender prevents the attacker's win".
  // Terminal nodes succeed exactly for draw or defender win.  Attacker nodes
  // enumerate every legal move; one refuted child refutes the node.  Defender
  // nodes try moves in order; the first found child proves the node.  Found
  // and Refuted results are cached only when the whole subtree below was
  // searched without hitting a limit; Unknown is never cached and propagates
  // to the root, so a limited search can never produce a proof.
  ProofState proveDefense(const Position& position, std::uint16_t depth) {
    if (stopped) {
      return ProofState::unknown;
    }
    if (depth > maxDepthReached) {
      maxDepthReached = depth;
    }
    const DefenseStateKey key = makeDefenseKey(position, defender);
    const auto cached = table.find(key);
    if (cached != table.end()) {
      ++stats.tableHits;
      return cached->second.status == DefenseStatus::found
          ? ProofState::found
          : ProofState::refuted;
    }
    if (config.maxTableEntries != 0 &&
        table.size() >= config.maxTableEntries) {
      stopped = true;
      unknownReason = "table limit";
      return ProofState::unknown;
    }
    const std::optional<Outcome> terminal = position.board.terminal();
    if (terminal.has_value()) {
      if (*terminal == playerOutcome(other(defender))) {
        table.insert_or_assign(key,
            DefenseEntry{DefenseStatus::refuted, std::nullopt});
        return ProofState::refuted;
      }
      table.insert_or_assign(key,
          DefenseEntry{DefenseStatus::found, std::nullopt});
      return ProofState::found;
    }
    if (config.maxNodes != 0 && stats.expandedNodes >= config.maxNodes) {
      stopped = true;
      unknownReason = "node limit";
      return ProofState::unknown;
    }
    ++stats.expandedNodes;

    const std::vector<Coord> moves = orderedEmptyMoves(position.board);
    if (position.turn == defender) {
      bool sawUnknown = false;
      for (const Coord move : moves) {
        if (stopped) {
          return ProofState::unknown;
        }
        const ProofState child = proveDefense(play(position, move),
            static_cast<std::uint16_t>(depth + 1));
        if (child == ProofState::found) {
          if (!stopped) {
            table.insert_or_assign(key,
                DefenseEntry{DefenseStatus::found, move});
          }
          return ProofState::found;
        }
        if (child == ProofState::unknown) {
          sawUnknown = true;
        }
      }
      if (sawUnknown || stopped) {
        return ProofState::unknown;
      }
      table.insert_or_assign(key,
          DefenseEntry{DefenseStatus::refuted, std::nullopt});
      return ProofState::refuted;
    }

    bool sawUnknown = false;
    for (const Coord move : moves) {
      if (stopped) {
        return ProofState::unknown;
      }
      const ProofState child = proveDefense(play(position, move),
          static_cast<std::uint16_t>(depth + 1));
      if (child == ProofState::refuted) {
        if (!stopped) {
          table.insert_or_assign(key,
              DefenseEntry{DefenseStatus::refuted, std::nullopt});
        }
        return ProofState::refuted;
      }
      if (child == ProofState::unknown) {
        sawUnknown = true;
      }
    }
    if (sawUnknown || stopped) {
      return ProofState::unknown;
    }
    table.insert_or_assign(key,
        DefenseEntry{DefenseStatus::found, std::nullopt});
    return ProofState::found;
  }

  std::size_t emitDefenseProof(const Position& position, std::uint16_t depth,
                               DefenseCertificate& certificate,
                               std::size_t sourceParent, Coord sourceMove) {
    if (config.maxCertificateNodes != 0 &&
        certificate.nodes.size() >= config.maxCertificateNodes) {
      throw std::length_error("defense certificate node limit reached");
    }
    const std::size_t index = certificate.nodes.size();
    DefenseCertificateNode placeholder;
    placeholder.position = position;
    placeholder.sourceParent = sourceParent;
    placeholder.sourceMove = sourceMove;
    certificate.nodes.push_back(std::move(placeholder));

    const std::optional<Outcome> terminal = position.board.terminal();
    if (terminal.has_value()) {
      certificate.nodes[index].kind = DefenseNodeKind::terminal;
      certificate.nodes[index].outcome = *terminal;
      return index;
    }

    const DefenseStateKey key = makeDefenseKey(position, defender);
    if (position.turn == defender) {
      const auto found = table.find(key);
      if (found == table.end() ||
          found->second.status != DefenseStatus::found ||
          !found->second.chosenMove.has_value()) {
        throw std::logic_error(
            "defense export: defender node has no proved move");
      }
      const Coord move = *found->second.chosenMove;
      certificate.nodes[index].kind = DefenseNodeKind::defenderMove;
      certificate.nodes[index].move = move;
      certificate.nodes[index].child = emitDefenseProof(play(position, move),
          static_cast<std::uint16_t>(depth + 1), certificate, index, move);
      return index;
    }

    certificate.nodes[index].kind = DefenseNodeKind::attackerMoves;
    const std::vector<Coord> moves = orderedEmptyMoves(position.board);
    for (const Coord move : moves) {
      const Position childPosition = play(position, move);
      const auto childIt = table.find(makeDefenseKey(childPosition, defender));
      if (childIt == table.end() ||
          childIt->second.status != DefenseStatus::found) {
        throw std::logic_error(
            "defense export: attacker node has an unproved child");
      }
      const std::size_t child = emitDefenseProof(childPosition,
          static_cast<std::uint16_t>(depth + 1), certificate, index, move);
      certificate.nodes[index].children.push_back({move, child});
    }
    return index;
  }

  DefenseSolveResult solve(const Position& root) {
    stats = {};
    table.clear();
    stopped = false;
    unknownReason.clear();
    maxDepthReached = 0;

    DefenseSolveResult result;
    const ProofState rootState = proveDefense(root, 0);
    result.stats = stats;
    result.stats.tableEntries = table.size();
    result.stats.maxDepthReached = maxDepthReached;
    if (stopped || rootState == ProofState::unknown) {
      result.status = ProofSearchStatus::unknown;
      return result;
    }
    if (rootState == ProofState::refuted) {
      result.status = ProofSearchStatus::refuted;
      return result;
    }
    DefenseCertificate certificate;
    certificate.defender = defender;
    try {
      emitDefenseProof(root, 0, certificate, noParent, {});
    } catch (const std::length_error&) {
      result.status = ProofSearchStatus::unknown;
      result.stats.certificateExhausted = true;
      return result;
    }
    result.status = ProofSearchStatus::found;
    result.certificate = std::move(certificate);
    return result;
  }
};

DefenseSearcher::DefenseSearcher(SearchConfig config, Player defender)
    : impl_(std::make_unique<Impl>(config, defender)) {}

DefenseSearcher::~DefenseSearcher() = default;
DefenseSearcher::DefenseSearcher(DefenseSearcher&&) noexcept = default;
DefenseSearcher& DefenseSearcher::operator=(DefenseSearcher&&) noexcept = default;

DefenseSolveResult DefenseSearcher::solve(const Position& root) {
  return impl_->solve(root);
}

ParsedProblem parseProblem(std::istream& input) {
  std::vector<std::string> rows;
  Player turn = Player::black;
  Player target = Player::black;
  bool sawTurn = false;
  bool sawTarget = false;
  std::string line;
  while (std::getline(input, line)) {
    line = trim(line);
    if (line.empty() || line.front() == '#') {
      continue;
    }
    const std::size_t separator = line.find_first_of("= ");
    const std::string key = lower(separator == std::string::npos
        ? line : line.substr(0, separator));
    if (key == "turn" || key == "target") {
      if (separator == std::string::npos) {
        throw std::runtime_error("missing player value after " + key);
      }
      std::string value = trim(line.substr(separator + 1));
      if (!value.empty() && value.front() == '=') {
        value = trim(value.substr(1));
      }
      if (key == "turn") {
        turn = parsePlayer(value);
        sawTurn = true;
      } else {
        target = parsePlayer(value);
        sawTarget = true;
      }
      continue;
    }
    rows.push_back(line);
  }

  if (!sawTurn || !sawTarget) {
    throw std::runtime_error("position file must specify turn and target");
  }
  if (rows.size() != boardSize) {
    throw std::runtime_error("position file must contain exactly " +
        std::to_string(boardSize) + " board rows");
  }

  Board board;
  for (int y = 0; y < boardSize; ++y) {
    if (rows[static_cast<std::size_t>(y)].size() != boardSize) {
      throw std::runtime_error("every board row must contain exactly " +
          std::to_string(boardSize) + " cells");
    }
    for (int x = 0; x < boardSize; ++x) {
      const char cell = rows[static_cast<std::size_t>(y)]
                            [static_cast<std::size_t>(x)];
      if (cell == '.') {
        continue;
      }
      if (cell == 'X' || cell == 'x' || cell == 'B' || cell == 'b') {
        board.place({x, y}, Player::black);
      } else if (cell == 'O' || cell == 'o' || cell == 'W' || cell == 'w') {
        board.place({x, y}, Player::white);
      } else {
        throw std::runtime_error("board cells must be '.', 'X', or 'O'");
      }
    }
  }
  return {{board, turn}, target};
}

bool usesGlobalCertificateChecker(const Position& root,
                                  const Certificate& certificate) {
  const Position initialPosition{};
  return certificate.target == Player::black && root == initialPosition;
}

void validateCertificate(const Position& root,
                         const Certificate& certificate) {
  if (certificate.nodes.empty()) {
    throw std::runtime_error("cannot export an empty certificate");
  }
  if (!(certificate.nodes.front().position == root)) {
    throw std::runtime_error("certificate root position does not match input root");
  }

  const auto fail = [](std::size_t index, const std::string& message) {
    throw std::runtime_error("invalid certificate node " +
        std::to_string(index) + ": " + message);
  };
  const auto checkChild = [&](std::size_t index, const Position& position,
                              Coord move, std::size_t child) {
    if (!position.board.inside(move) || !position.board.isEmpty(move)) {
      fail(index, "edge move is not an empty in-range coordinate");
    }
    if (child <= index || child >= certificate.nodes.size()) {
      fail(index, "child reference must be in range and greater than parent");
    }
    if (!(certificate.nodes[child].position == play(position, move))) {
      fail(index, "child position does not equal play(parent, move)");
    }
  };

  for (std::size_t index = 0; index < certificate.nodes.size(); ++index) {
    const CertificateNode& node = certificate.nodes[index];
    if (index == 0) {
      if (node.sourceParent != noParent) {
        fail(index, "root must not have an exporter source parent");
      }
    } else {
      if (node.sourceParent == noParent || node.sourceParent >= index) {
        fail(index, "exporter source parent must precede the node");
      }
      const Position& source = certificate.nodes[node.sourceParent].position;
      if (source.board.terminal().has_value() ||
          !source.board.inside(node.sourceMove) ||
          !source.board.isEmpty(node.sourceMove) ||
          !(node.position == play(source, node.sourceMove))) {
        fail(index, "exporter source edge does not reconstruct the node position");
      }
    }

    const std::optional<Outcome> terminal = node.position.board.terminal();
    switch (node.kind) {
      case CertificateKind::terminal:
        if (!terminal.has_value() || *terminal != node.outcome ||
            node.outcome != playerOutcome(certificate.target)) {
          fail(index, "terminal label must be the target player's actual win");
        }
        break;
      case CertificateKind::proverMove:
        if (terminal.has_value()) {
          fail(index, "proverMove position is already terminal");
        }
        if (node.position.turn != certificate.target) {
          fail(index, "proverMove turn does not equal certificate target");
        }
        checkChild(index, node.position, node.move, node.child);
        break;
      case CertificateKind::opponentMoves: {
        if (terminal.has_value()) {
          fail(index, "opponentMoves position is already terminal");
        }
        if (node.position.turn != other(certificate.target)) {
          fail(index, "opponentMoves turn is not the opponent's turn");
        }
        const std::vector<Coord> legalMoves = node.position.board.emptyMoves();
        if (node.children.size() != legalMoves.size()) {
          fail(index, "opponentMoves must contain every legal move exactly once");
        }
        std::array<bool, boardCells> covered{};
        for (const auto& childEdge : node.children) {
          const Coord move = childEdge.first;
          if (!node.position.board.inside(move)) {
            fail(index, "opponent edge coordinate is outside the board");
          }
          const std::size_t moveIndex = static_cast<std::size_t>(indexOf(move));
          if (covered[moveIndex]) {
            fail(index, "opponentMoves contains a duplicate move");
          }
          covered[moveIndex] = true;
          checkChild(index, node.position, move, childEdge.second);
        }
        for (const Coord move : legalMoves) {
          if (!covered[static_cast<std::size_t>(indexOf(move))]) {
            fail(index, "opponentMoves omits a legal move");
          }
        }
        break;
      }
    }
  }
}

void writeLeanCertificate(std::ostream& output, const Position& root,
                          const Certificate& certificate,
                          const std::string& definitionPrefix) {
  validateCertificate(root, certificate);
  const std::string prefix = sanitizeIdentifier(definitionPrefix);
  output << "import Gomoku.Certificate\n\n";
  output << "namespace Gomoku.Generated\n\n";
  output << "/- Generated by cpp/gomoku_solver.  The generator is untrusted;\n";
  output << "   interface: CompactCertificate-v1, root index 0, parent < child;\n";
  output << "   the theorem below depends on the existing Lean checker. -/\n";
  output << "def " << prefix
         << "RootStones : Array (Coord × Player) := #[\n";
  bool firstStone = true;
  for (int y = 0; y < boardSize; ++y) {
    for (int x = 0; x < boardSize; ++x) {
      const Coord move{x, y};
      const Cell cell = root.board.at(move);
      if (cell == Cell::empty) {
        continue;
      }
      if (!firstStone) {
        output << ",\n";
      }
      firstStone = false;
      output << "  (" << leanCoord(move) << ", "
             << leanPlayer(cell == Cell::black ? Player::black
                                               : Player::white)
             << ")";
    }
  }
  output << "\n]\n\n";
  output << "def " << prefix << "RootBoard : Board :=\n";
  output << "  " << prefix
         << "RootStones.foldl (fun board stone =>\n";
  output << "    Board.place board stone.1 stone.2) Board.empty\n\n";
  output << "def " << prefix << "RootPosition : Position :=\n";
  output << "  ⟨" << prefix << "RootBoard, " << leanPlayer(root.turn)
         << "⟩\n\n";

  for (std::size_t index = 0; index < certificate.nodes.size(); ++index) {
    const CertificateNode& node = certificate.nodes[index];
    output << "def " << prefix << "Position" << index
           << " : Position :=\n  ";
    if (index == 0) {
      output << prefix << "RootPosition\n\n";
    } else {
      if (node.sourceParent == noParent || node.sourceParent >= index) {
        throw std::runtime_error("certificate exporter requires parent-before-child order");
      }
      output << "play " << prefix << "Position" << node.sourceParent << " "
             << leanCoord(node.sourceMove) << "\n\n";
    }
  }

  output << "def " << prefix << "Certificate : CompactCertificate :=\n";
  output << "  { target := " << leanPlayer(certificate.target) << "\n";
  output << "    root := 0\n";
  output << "    nodes := #[\n";
  for (std::size_t index = 0; index < certificate.nodes.size(); ++index) {
    const CertificateNode& node = certificate.nodes[index];
    output << "      ";
    if (node.kind == CertificateKind::terminal) {
      output << ".terminal " << prefix << "Position" << index << " "
             << leanOutcome(node.outcome);
    } else if (node.kind == CertificateKind::proverMove) {
      output << ".proverMove " << prefix << "Position" << index << " "
             << leanCoord(node.move) << " " << node.child;
    } else {
      output << ".opponentMoves " << prefix << "Position" << index << " #[";
      for (std::size_t childIndex = 0; childIndex < node.children.size();
           ++childIndex) {
        if (childIndex != 0) {
          output << ", ";
        }
        output << "(" << leanCoord(node.children[childIndex].first) << ", "
               << node.children[childIndex].second << ")";
      }
      output << "]";
    }
    output << (index + 1 == certificate.nodes.size() ? "\n" : ",\n");
  }
  output << "    ] }\n\n";
  output << "set_option linter.style.nativeDecide false in\n";
  output << "theorem " << prefix << "Certificate_checked :\n";
  if (usesGlobalCertificateChecker(root, certificate)) {
    output << "    checkCertificate " << prefix
           << "Certificate = true := by\n";
  } else {
    output << "    checkLocalCertificateAt " << prefix << "RootPosition "
           << prefix << "Certificate = true := by\n";
  }
  output << "  native_decide\n\n";
  output << "theorem " << prefix << "Certificate_sound :\n";
  if (usesGlobalCertificateChecker(root, certificate)) {
    output << "    CanForceWin initialPosition .black :=\n";
    output << "  compact_certificate_sound " << prefix << "Certificate "
           << prefix << "Certificate_checked\n\n";
  } else {
    output << "    CanForceWin " << prefix << "RootPosition " << prefix
           << "Certificate.target :=\n";
    output << "  local_certificate_at_sound " << prefix << "RootPosition "
           << prefix << "Certificate " << prefix << "Certificate_checked\n\n";
  }
  output << "end Gomoku.Generated\n";
}

void validateDefenseCertificate(const Position& root,
                                const DefenseCertificate& certificate) {
  if (certificate.nodes.empty()) {
    throw std::runtime_error("cannot export an empty defense certificate");
  }
  if (!(certificate.nodes.front().position == root)) {
    throw std::runtime_error(
        "defense certificate root position does not match input root");
  }

  const auto fail = [](std::size_t index, const std::string& message) {
    throw std::runtime_error("invalid defense certificate node " +
        std::to_string(index) + ": " + message);
  };
  const auto checkChild = [&](std::size_t index, const Position& position,
                              Coord move, std::size_t child) {
    if (!position.board.inside(move) || !position.board.isEmpty(move)) {
      fail(index, "edge move is not an empty in-range coordinate");
    }
    if (child <= index || child >= certificate.nodes.size()) {
      fail(index, "child reference must be in range and greater than parent");
    }
    if (!(certificate.nodes[child].position == play(position, move))) {
      fail(index, "child position does not equal play(parent, move)");
    }
  };

  for (std::size_t index = 0; index < certificate.nodes.size(); ++index) {
    const DefenseCertificateNode& node = certificate.nodes[index];
    if (index == 0) {
      if (node.sourceParent != noParent) {
        fail(index, "root must not have an exporter source parent");
      }
    } else {
      if (node.sourceParent == noParent || node.sourceParent >= index) {
        fail(index, "exporter source parent must precede the node");
      }
      const Position& source = certificate.nodes[node.sourceParent].position;
      if (source.board.terminal().has_value() ||
          !source.board.inside(node.sourceMove) ||
          !source.board.isEmpty(node.sourceMove) ||
          !(node.position == play(source, node.sourceMove))) {
        fail(index, "exporter source edge does not reconstruct the node position");
      }
    }

    const std::optional<Outcome> terminal = node.position.board.terminal();
    switch (node.kind) {
      case DefenseNodeKind::terminal:
        if (!terminal.has_value() || *terminal != node.outcome ||
            (node.outcome != playerOutcome(certificate.defender) &&
             node.outcome != Outcome::draw)) {
          fail(index, "terminal label must be the actual outcome and not the attacker's win");
        }
        break;
      case DefenseNodeKind::defenderMove:
        if (terminal.has_value()) {
          fail(index, "defenderMove position is already terminal");
        }
        if (node.position.turn != certificate.defender) {
          fail(index, "defenderMove turn does not equal certificate defender");
        }
        checkChild(index, node.position, node.move, node.child);
        break;
      case DefenseNodeKind::attackerMoves: {
        if (terminal.has_value()) {
          fail(index, "attackerMoves position is already terminal");
        }
        if (node.position.turn != other(certificate.defender)) {
          fail(index, "attackerMoves turn is not the attacker's turn");
        }
        const std::vector<Coord> legalMoves = node.position.board.emptyMoves();
        if (node.children.size() != legalMoves.size()) {
          fail(index, "attackerMoves must contain every legal move exactly once");
        }
        std::array<bool, boardCells> covered{};
        for (const auto& childEdge : node.children) {
          const Coord move = childEdge.first;
          if (!node.position.board.inside(move)) {
            fail(index, "attacker edge coordinate is outside the board");
          }
          const std::size_t moveIndex = static_cast<std::size_t>(indexOf(move));
          if (covered[moveIndex]) {
            fail(index, "attackerMoves contains a duplicate move");
          }
          covered[moveIndex] = true;
          checkChild(index, node.position, move, childEdge.second);
        }
        for (const Coord move : legalMoves) {
          if (!covered[static_cast<std::size_t>(indexOf(move))]) {
            fail(index, "attackerMoves omits a legal move");
          }
        }
        break;
      }
    }
  }
}

void writeLeanDefenseCertificate(std::ostream& output, const Position& root,
                                 const DefenseCertificate& certificate,
                                 const std::string& definitionPrefix) {
  validateDefenseCertificate(root, certificate);
  const std::string prefix = sanitizeIdentifier(definitionPrefix);
  output << "import Gomoku.Defense\n\n";
  output << "namespace Gomoku.Generated\n\n";
  output << "/- Generated by cpp/gomoku_solver.  The generator is untrusted;\n";
  output << "   interface: DefenseCertificate-v1, root index 0, parent < child;\n";
  output << "   the theorem below depends on the existing Lean checker. -/\n";
  output << "def " << prefix << "RootStones : Array (Coord × Player) := #[\n";
  bool firstStone = true;
  for (int y = 0; y < boardSize; ++y) {
    for (int x = 0; x < boardSize; ++x) {
      const Coord move{x, y};
      const Cell cell = root.board.at(move);
      if (cell == Cell::empty) {
        continue;
      }
      if (!firstStone) {
        output << ",\n";
      }
      firstStone = false;
      output << "  (" << leanCoord(move) << ", "
             << leanPlayer(cell == Cell::black ? Player::black
                                               : Player::white)
             << ")";
    }
  }
  output << "\n]\n\n";
  output << "def " << prefix << "RootBoard : Board :=\n";
  output << "  " << prefix
         << "RootStones.foldl (fun board stone =>\n";
  output << "    Board.place board stone.1 stone.2) Board.empty\n\n";
  output << "def " << prefix << "RootPosition : Position :=\n";
  output << "  ⟨" << prefix << "RootBoard, " << leanPlayer(root.turn)
         << "⟩\n\n";

  for (std::size_t index = 0; index < certificate.nodes.size(); ++index) {
    const DefenseCertificateNode& node = certificate.nodes[index];
    output << "def " << prefix << "Position" << index
           << " : Position :=\n  ";
    if (index == 0) {
      output << prefix << "RootPosition\n\n";
    } else {
      if (node.sourceParent == noParent || node.sourceParent >= index) {
        throw std::runtime_error(
            "defense certificate exporter requires parent-before-child order");
      }
      output << "play " << prefix << "Position" << node.sourceParent << " "
             << leanCoord(node.sourceMove) << "\n\n";
    }
  }

  output << "def " << prefix << "Certificate : DefenseCertificate :=\n";
  output << "  { defender := " << leanPlayer(certificate.defender) << "\n";
  output << "    root := 0\n";
  output << "    nodes := #[\n";
  for (std::size_t index = 0; index < certificate.nodes.size(); ++index) {
    const DefenseCertificateNode& node = certificate.nodes[index];
    output << "      ";
    if (node.kind == DefenseNodeKind::terminal) {
      output << ".terminal " << prefix << "Position" << index << " "
             << leanOutcome(node.outcome);
    } else if (node.kind == DefenseNodeKind::defenderMove) {
      output << ".defenderMove " << prefix << "Position" << index << " "
             << leanCoord(node.move) << " " << node.child;
    } else {
      output << ".attackerMoves " << prefix << "Position" << index << " #[";
      for (std::size_t childIndex = 0; childIndex < node.children.size();
           ++childIndex) {
        if (childIndex != 0) {
          output << ", ";
        }
        output << "(" << leanCoord(node.children[childIndex].first) << ", "
               << node.children[childIndex].second << ")";
      }
      output << "]";
    }
    output << (index + 1 == certificate.nodes.size() ? "\n" : ",\n");
  }
  output << "    ] }\n\n";

  const bool globalRoot = (root == Position{});
  output << "set_option linter.style.nativeDecide false in\n";
  output << "theorem " << prefix << "Certificate_checked :\n";
  if (globalRoot) {
    output << "    checkDefenseCertificateAt initialPosition " << prefix
           << "Certificate = true := by\n";
  } else {
    output << "    checkDefenseCertificateAt " << prefix << "RootPosition "
           << prefix << "Certificate = true := by\n";
  }
  output << "  native_decide\n\n";

  const std::string positionName = globalRoot
      ? "initialPosition"
      : (prefix + "RootPosition");
  output << "theorem " << prefix << "Defense_sound :\n";
  if (certificate.defender == Player::white) {
    output << "    WhiteCanPreventBlackWin " << positionName << " :=\n";
    output << "  white_defense_certificate_sound " << positionName << " "
           << prefix << "Certificate rfl " << prefix
           << "Certificate_checked\n\n";
  } else {
    output << "    BlackCanPreventWhiteWin " << positionName << " :=\n";
    output << "  black_defense_certificate_sound " << positionName << " "
           << prefix << "Certificate rfl " << prefix
           << "Certificate_checked\n\n";
  }
  output << "end Gomoku.Generated\n";
}

Position immediateWinExample() {
  Board board;
  for (int x = 1; x <= 4; ++x) {
    board.place({x, 3}, Player::black);
  }
  return {board, Player::black};
}

Position opponentForkExample() {
  Board board;
  for (int y = 0; y < boardSize; ++y) {
    for (int x = 0; x < boardSize; ++x) {
      const Coord move{x, y};
      if (move == Coord{0, 3} || move == Coord{5, 3}) {
        continue;
      }
      if (move == Coord{1, 3} || move == Coord{2, 3} ||
          move == Coord{3, 3} || move == Coord{4, 3}) {
        board.place(move, Player::black);
      } else if ((x + 2 * y) % 4 < 2) {
        board.place(move, Player::black);
      } else {
        board.place(move, Player::white);
      }
    }
  }
  return {board, Player::white};
}

Position vcfOpenFourExample() {
  Board board;
  for (int y = 0; y < boardSize; ++y) {
    for (int x = 0; x < boardSize; ++x) {
      const Coord move{x, y};
      if (move == Coord{0, 3} || move == Coord{1, 3} ||
          move == Coord{5, 3}) {
        continue;
      }
      if (move == Coord{2, 3} || move == Coord{3, 3} ||
          move == Coord{4, 3}) {
        board.place(move, Player::black);
      } else if (move == Coord{6, 3}) {
        board.place(move, Player::white);
      } else if ((x + 2 * y) % 4 < 2) {
        board.place(move, Player::black);
      } else {
        board.place(move, Player::white);
      }
    }
  }
  return {board, Player::black};
}

}  // namespace gomoku
