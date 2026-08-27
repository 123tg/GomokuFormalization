#include "gomoku_solver.hpp"

#include <algorithm>
#include <cctype>
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
  score -= std::abs(move.x - 7) + std::abs(move.y - 7);
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
    throw std::out_of_range("coordinate outside 15x15 board");
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
    throw std::out_of_range("cannot place outside 15x15 board");
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
    if (length >= 5) {
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
        if (length >= 5) {
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
  SearchStats stats;
  SolveStatus limitStatus = SolveStatus::depthLimit;
  bool stopped = false;

  explicit Impl(SearchConfig configValue, Player targetValue)
      : config(configValue), target(targetValue) {
    table.reserve(std::min<std::size_t>(config.maxTableEntries == 0
        ? 262'144 : config.maxTableEntries, 262'144));
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
      const auto beforeProof = current.proof;
      const auto beforeDisproof = current.disproof;
      recompute(position, depth);
      const Entry after = table.find(key)->second;
      if (after.proof == beforeProof && after.disproof == beforeDisproof) {
        return;
      }
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
    stopped = false;
    limitStatus = SolveStatus::depthLimit;

    SolveResult result;
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
    throw std::runtime_error("position file must contain exactly 15 board rows");
  }

  Board board;
  for (int y = 0; y < boardSize; ++y) {
    if (rows[static_cast<std::size_t>(y)].size() != boardSize) {
      throw std::runtime_error("every board row must contain exactly 15 cells");
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

void writeLeanCertificate(std::ostream& output, const Position& root,
                          const Certificate& certificate,
                          const std::string& definitionPrefix) {
  if (certificate.nodes.empty()) {
    throw std::runtime_error("cannot export an empty certificate");
  }
  const std::string prefix = sanitizeIdentifier(definitionPrefix);
  output << "import Gomoku.Certificate\n\n";
  output << "namespace Gomoku.Generated\n\n";
  output << "/- Generated by cpp/gomoku_solver.  The generator is untrusted;\n";
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
  output << "    checkLocalCertificateAt " << prefix << "RootPosition "
         << prefix << "Certificate = true := by\n";
  output << "  native_decide\n\n";
  output << "theorem " << prefix << "Certificate_sound :\n";
  output << "    CanForceWin " << prefix << "RootPosition " << prefix
         << "Certificate.target :=\n";
  output << "  local_certificate_at_sound " << prefix << "RootPosition "
         << prefix << "Certificate " << prefix << "Certificate_checked\n\n";
  output << "end Gomoku.Generated\n";
}

Position immediateWinExample() {
  Board board;
  for (int x = 5; x <= 8; ++x) {
    board.place({x, 7}, Player::black);
  }
  return {board, Player::black};
}

Position opponentForkExample() {
  Board board;
  for (int y = 0; y < boardSize; ++y) {
    for (int x = 0; x < boardSize; ++x) {
      const Coord move{x, y};
      if (move == Coord{4, 7} || move == Coord{9, 7}) {
        continue;
      }
      if (move == Coord{5, 7} || move == Coord{6, 7} ||
          move == Coord{7, 7} || move == Coord{8, 7}) {
        board.place(move, Player::black);
      } else if ((x + 2 * y) % 5 < 2) {
        board.place(move, Player::black);
      } else {
        board.place(move, Player::white);
      }
    }
  }
  return {board, Player::white};
}

}  // namespace gomoku
