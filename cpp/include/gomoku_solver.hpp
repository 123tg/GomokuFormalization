#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <iosfwd>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace gomoku {

constexpr int boardSize = 7;
constexpr int winLength = 5;
constexpr int boardCells = boardSize * boardSize;

enum class Player : std::uint8_t {
  black,
  white,
};

enum class Cell : std::uint8_t {
  empty,
  black,
  white,
};

enum class Outcome : std::uint8_t {
  blackWin,
  whiteWin,
  draw,
};

Player other(Player player);
const char* playerName(Player player);

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
  std::uint16_t stones = 0;
  std::uint64_t zobrist = 0;

  bool inside(Coord move) const;
  Cell at(Coord move) const;
  bool isEmpty(Coord move) const;
  void place(Coord move, Player player);
  bool full() const;
  bool createsFive(Coord move, Player player) const;
  bool hasFive(Player player) const;
  std::optional<Outcome> terminal() const;
  std::vector<Coord> emptyMoves() const;

  friend bool operator==(const Board& lhs, const Board& rhs) {
    return lhs.black == rhs.black && lhs.white == rhs.white;
  }
};

struct Position {
  Board board;
  Player turn = Player::black;

  friend bool operator==(const Position& lhs, const Position& rhs) {
    return lhs.turn == rhs.turn && lhs.board == rhs.board;
  }
};

Position play(const Position& position, Coord move);

struct SearchConfig {
  std::uint16_t maxDepth = 6;
  std::uint16_t maxVcfDepth = 7;
  std::uint64_t maxNodes = 1'000'000;
  std::uint64_t maxVcfNodes = 100'000;
  std::size_t maxTableEntries = 1'000'000;
  std::size_t maxCertificateNodes = 2'000'000;
  std::size_t maxProverMoves = 0;
  bool forcedMovePruning = true;
};

enum class SolveStatus : std::uint8_t {
  found,
  depthLimit,
  nodeLimit,
  tableLimit,
  certificateLimit,
};

const char* solveStatusName(SolveStatus status);

struct SearchStats {
  std::uint64_t expandedNodes = 0;
  std::uint64_t tableHits = 0;
  std::uint64_t vcfNodes = 0;
  std::uint64_t vcfTableHits = 0;
  std::size_t tableEntries = 0;
  std::uint16_t maxDepthReached = 0;
  bool vcfRootSolved = false;
  bool vcfBudgetExhausted = false;
  bool certificateExhausted = false;
};

enum class CertificateKind : std::uint8_t {
  terminal,
  proverMove,
  opponentMoves,
};

struct CertificateNode {
  CertificateKind kind = CertificateKind::terminal;
  Position position;
  Outcome outcome = Outcome::draw;
  Coord move{};
  std::size_t child = 0;
  std::vector<std::pair<Coord, std::size_t>> children;

  // The exporter uses one already-emitted parent to define this position as
  // `play parent move`.  This metadata is not part of CompactCertificate.
  std::size_t sourceParent = static_cast<std::size_t>(-1);
  Coord sourceMove{};
};

struct Certificate {
  Player target = Player::black;
  std::vector<CertificateNode> nodes;
};

struct SolveResult {
  SolveStatus status = SolveStatus::depthLimit;
  std::optional<std::uint16_t> depth;
  SearchStats stats;
  std::optional<Certificate> certificate;
};

// ---------------------------------------------------------------------------
// Defense certificates: prove "the defender can prevent the attacker's win"
// (WhiteCanPreventBlackWin / BlackCanPreventWhiteWin in Lean).  The search is
// a separate complete AND/OR proof search: attacker nodes must cover every
// legal move, defender nodes need one move, terminal nodes succeed exactly for
// draw or defender win.  Limits yield Unknown, never a proof or a refutation.
// ---------------------------------------------------------------------------

enum class DefenseNodeKind : std::uint8_t {
  terminal,
  defenderMove,
  attackerMoves,
};

struct DefenseCertificateNode {
  DefenseNodeKind kind = DefenseNodeKind::terminal;
  Position position;
  Outcome outcome = Outcome::draw;
  Coord move{};
  std::size_t child = 0;
  std::vector<std::pair<Coord, std::size_t>> children;

  // The exporter uses one already-emitted parent to define this position as
  // `play parent move`.  This metadata is not part of DefenseCertificate.
  std::size_t sourceParent = static_cast<std::size_t>(-1);
  Coord sourceMove{};
};

struct DefenseCertificate {
  Player defender = Player::white;
  std::vector<DefenseCertificateNode> nodes;
};

enum class ProofSearchStatus : std::uint8_t {
  found,
  refuted,
  unknown,
};

const char* proofSearchStatusName(ProofSearchStatus status);

struct DefenseSolveResult {
  ProofSearchStatus status = ProofSearchStatus::unknown;
  SearchStats stats;
  std::optional<DefenseCertificate> certificate;
};

class DefenseSearcher {
 public:
  DefenseSearcher(SearchConfig config, Player defender);
  ~DefenseSearcher();
  DefenseSearcher(DefenseSearcher&&) noexcept;
  DefenseSearcher& operator=(DefenseSearcher&&) noexcept;
  DefenseSearcher(const DefenseSearcher&) = delete;
  DefenseSearcher& operator=(const DefenseSearcher&) = delete;

  DefenseSolveResult solve(const Position& root);

 private:
  struct Impl;
  std::unique_ptr<Impl> impl_;
};

void validateDefenseCertificate(const Position& root,
                                const DefenseCertificate& certificate);
void writeLeanDefenseCertificate(std::ostream& output, const Position& root,
                                 const DefenseCertificate& certificate,
                                 const std::string& definitionPrefix);

class DfpnSolver {
 public:
  DfpnSolver(SearchConfig config, Player target);
  ~DfpnSolver();
  DfpnSolver(DfpnSolver&&) noexcept;
  DfpnSolver& operator=(DfpnSolver&&) noexcept;
  DfpnSolver(const DfpnSolver&) = delete;
  DfpnSolver& operator=(const DfpnSolver&) = delete;

  SolveResult solve(const Position& root);

 private:
  struct Impl;
  std::unique_ptr<Impl> impl_;
};

struct ParsedProblem {
  Position root;
  Player target = Player::black;
};

ParsedProblem parseProblem(std::istream& input);
bool usesGlobalCertificateChecker(const Position& root,
                                  const Certificate& certificate);
void validateCertificate(const Position& root,
                         const Certificate& certificate);
void writeLeanCertificate(std::ostream& output, const Position& root,
                          const Certificate& certificate,
                          const std::string& definitionPrefix);

Position immediateWinExample();
Position opponentForkExample();
Position vcfOpenFourExample();

}  // namespace gomoku
