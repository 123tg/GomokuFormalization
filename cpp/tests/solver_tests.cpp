#include "gomoku_solver.hpp"

#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>

namespace {

void require(bool condition, const std::string& message) {
  if (!condition) {
    throw std::runtime_error(message);
  }
}

void testGeometry() {
  require(gomoku::boardSize == 7, "solver board must be 7x7");
  require(gomoku::boardCells == 49, "7x7 board must contain 49 cells");

  const gomoku::Position initial;
  require(initial.turn == gomoku::Player::black,
          "Black must move first");
  require(initial.board.emptyMoves().size() == 49,
          "initial board must expose 49 legal cells");
  require(!initial.board.terminal().has_value(),
          "initial board must be non-terminal");

  gomoku::Board horizontal;
  for (int x = 1; x <= 4; ++x) {
    horizontal.place({x, 3}, gomoku::Player::black);
  }
  require(horizontal.createsFive({0, 3}, gomoku::Player::black),
          "left horizontal endpoint should win");
  require(horizontal.createsFive({5, 3}, gomoku::Player::black),
          "right horizontal endpoint should win");
  require(!horizontal.createsFive({3, 2}, gomoku::Player::black),
          "unrelated move should not win");

  gomoku::Board vertical;
  for (int y = 1; y <= 4; ++y) {
    vertical.place({3, y}, gomoku::Player::white);
  }
  require(vertical.createsFive({3, 0}, gomoku::Player::white),
          "vertical endpoint should win for White");

  gomoku::Board mainDiagonal;
  for (int value = 0; value < 4; ++value) {
    mainDiagonal.place({value, value}, gomoku::Player::black);
  }
  require(mainDiagonal.createsFive({4, 4}, gomoku::Player::black),
          "main diagonal should win");

  gomoku::Board antiDiagonal;
  for (int value = 0; value < 4; ++value) {
    antiDiagonal.place({value, 6 - value}, gomoku::Player::white);
  }
  require(antiDiagonal.createsFive({4, 2}, gomoku::Player::white),
          "anti-diagonal should win for White");
}

void testParser() {
  std::ostringstream text;
  text << "turn black\n";
  text << "target black\n";
  for (int y = 0; y < gomoku::boardSize; ++y) {
    text << (y == 3 ? ".XXXX.." : ".......")
         << "\n";
  }
  std::istringstream input(text.str());
  const gomoku::ParsedProblem problem = gomoku::parseProblem(input);
  require(problem.root.turn == gomoku::Player::black,
          "parser should preserve turn");
  require(problem.root.board.stones == 4,
          "parser should load four stones");
}

void testImmediateCertificate() {
  gomoku::SearchConfig config;
  config.maxDepth = 1;
  config.maxNodes = 10;
  gomoku::DfpnSolver solver(config, gomoku::Player::black);
  const gomoku::Position root = gomoku::immediateWinExample();
  const gomoku::SolveResult result = solver.solve(root);
  require(result.status == gomoku::SolveStatus::found,
          "immediate win should be found");
  require(result.depth == 1, "immediate win should need one ply");
  require(result.certificate.has_value(),
          "found result should contain a certificate");
  require(result.certificate->nodes.size() == 2,
          "immediate proof should have two nodes");
  gomoku::validateCertificate(root, *result.certificate);

  std::ostringstream lean;
  gomoku::writeLeanCertificate(lean, root, *result.certificate,
                               "cppSmoke");
  require(lean.str().find("checkLocalCertificateAt") != std::string::npos,
          "export should call the current Lean checker");
  require(lean.str().find("CompactCertificate") != std::string::npos,
          "export should retain CompactCertificate format");
  require(lean.str().find("CompactCertificate-v1") != std::string::npos,
          "export should identify the Lean interface version");

  gomoku::Certificate invalid = *result.certificate;
  invalid.nodes.front().child = 0;
  bool rejected = false;
  try {
    gomoku::validateCertificate(root, invalid);
  } catch (const std::runtime_error&) {
    rejected = true;
  }
  require(rejected, "preflight must reject a non-forward child reference");
}

void testOpponentForkCertificate() {
  gomoku::SearchConfig config;
  config.maxDepth = 2;
  config.maxNodes = 100;
  gomoku::DfpnSolver solver(config, gomoku::Player::black);
  const gomoku::Position root = gomoku::opponentForkExample();
  require(!root.board.terminal().has_value(),
          "opponent fork root should be non-terminal");
  require(root.board.emptyMoves().size() == 2,
          "opponent fork should have exactly two replies");
  const gomoku::SolveResult result = solver.solve(root);
  require(result.status == gomoku::SolveStatus::found,
          "two-reply opponent fork should be solved");
  require(result.depth == 2, "opponent fork should need two plies");
  require(result.certificate.has_value(),
          "opponent fork should emit a certificate");
  require(result.certificate->nodes.size() == 5,
          "opponent fork proof should have five nodes");
  const auto& rootNode = result.certificate->nodes.front();
  require(rootNode.kind == gomoku::CertificateKind::opponentMoves,
          "opponent root should emit opponentMoves");
  require(rootNode.children.size() == 2,
          "opponent root must cover both legal replies");
  gomoku::validateCertificate(root, *result.certificate);

  gomoku::Certificate incomplete = *result.certificate;
  incomplete.nodes.front().children.pop_back();
  bool rejected = false;
  try {
    gomoku::validateCertificate(root, incomplete);
  } catch (const std::runtime_error&) {
    rejected = true;
  }
  require(rejected, "preflight must reject an omitted opponent reply");
}

void testCheckerSelection() {
  const gomoku::Position initialPosition{};
  gomoku::Certificate certificate;
  certificate.target = gomoku::Player::black;
  require(gomoku::usesGlobalCertificateChecker(initialPosition, certificate),
          "empty board with Black target must select checkCertificate");

  gomoku::Position localPosition = initialPosition;
  localPosition.board.place({3, 3}, gomoku::Player::black);
  localPosition.turn = gomoku::Player::white;
  require(!gomoku::usesGlobalCertificateChecker(localPosition, certificate),
          "non-initial root must select checkLocalCertificateAt");
}

void testVcfHintCertificate() {
  gomoku::SearchConfig config;
  config.maxDepth = 3;
  config.maxVcfDepth = 3;
  config.maxVcfNodes = 100;
  config.maxNodes = 1'000;
  config.maxProverMoves = 1;
  gomoku::DfpnSolver solver(config, gomoku::Player::black);
  const gomoku::Position root = gomoku::vcfOpenFourExample();
  require(!root.board.terminal().has_value(),
          "VCF root should be non-terminal");
  require(root.board.emptyMoves().size() == 3,
          "VCF root should have three legal moves");

  const gomoku::SolveResult result = solver.solve(root);
  require(result.status == gomoku::SolveStatus::found,
          "bounded VCF hint should guide selective DFPN to the proof");
  require(result.depth == 3, "open-four VCF should need three plies");
  require(result.stats.vcfRootSolved,
          "VCF oracle should recognize the root forcing line");
  require(result.stats.vcfNodes > 0,
          "VCF oracle should report its bounded work");
  require(result.certificate.has_value(),
          "VCF-guided result should contain a certificate");
  require(result.certificate->nodes.size() == 6,
          "two-reply open-four proof should have six nodes");

  const auto& rootNode = result.certificate->nodes.front();
  require(rootNode.kind == gomoku::CertificateKind::proverMove,
          "VCF proof should start with a prover move");
  require(rootNode.move == gomoku::Coord{1, 3},
          "VCF oracle should choose the double-ended four at (1,3)");
  require(rootNode.child < result.certificate->nodes.size(),
          "VCF root child should be valid");
  const auto& opponentNode = result.certificate->nodes[rootNode.child];
  require(opponentNode.kind == gomoku::CertificateKind::opponentMoves,
          "VCF attack should be followed by an opponent AND node");
  require(opponentNode.children.size() == 2,
          "VCF certificate must retain both legal opponent replies");

  gomoku::SearchConfig limitedConfig;
  limitedConfig.maxDepth = 3;
  limitedConfig.maxVcfDepth = 3;
  limitedConfig.maxVcfNodes = 1;
  limitedConfig.maxNodes = 1'000;
  gomoku::DfpnSolver limitedSolver(limitedConfig, gomoku::Player::black);
  const gomoku::SolveResult limitedResult = limitedSolver.solve(root);
  require(limitedResult.stats.vcfBudgetExhausted,
          "VCF probe should report its independent node budget");
  require(!limitedResult.stats.vcfRootSolved,
          "an interrupted VCF probe must not report a solved root");
  require(limitedResult.status == gomoku::SolveStatus::found,
          "VCF budget exhaustion must not stop complete DFPN search");

  gomoku::SearchConfig disabledConfig;
  disabledConfig.maxDepth = 3;
  disabledConfig.maxVcfDepth = 0;
  disabledConfig.maxNodes = 1'000;
  gomoku::DfpnSolver disabledSolver(disabledConfig,
                                    gomoku::Player::black);
  const gomoku::SolveResult disabledResult = disabledSolver.solve(root);
  require(disabledResult.stats.vcfNodes == 0,
          "zero VCF depth should disable the oracle");
  require(disabledResult.status == gomoku::SolveStatus::found,
          "complete DFPN should prove the line without VCF guidance");
}

void testResourceLimits() {
  gomoku::SearchConfig nodeConfig;
  nodeConfig.maxDepth = 2;
  nodeConfig.maxNodes = 1;
  gomoku::DfpnSolver nodeSolver(nodeConfig, gomoku::Player::black);
  require(nodeSolver.solve(gomoku::opponentForkExample()).status ==
              gomoku::SolveStatus::nodeLimit,
          "node budget should stop iterative DFPN");

  gomoku::SearchConfig tableConfig;
  tableConfig.maxDepth = 1;
  tableConfig.maxTableEntries = 1;
  gomoku::DfpnSolver tableSolver(tableConfig, gomoku::Player::black);
  require(tableSolver.solve(gomoku::immediateWinExample()).status ==
              gomoku::SolveStatus::tableLimit,
          "table bound should be reported separately");

  gomoku::SearchConfig certificateConfig;
  certificateConfig.maxDepth = 1;
  certificateConfig.maxCertificateNodes = 1;
  gomoku::DfpnSolver certificateSolver(certificateConfig,
                                       gomoku::Player::black);
  require(certificateSolver.solve(gomoku::immediateWinExample()).status ==
              gomoku::SolveStatus::certificateLimit,
          "certificate bound should be reported separately");
}

// ---------------------------------------------------------------------------
// Defense proof search tests
// ---------------------------------------------------------------------------

// A full 7x7 board with no five-in-a-row for either player:
// black iff (x + 2y) mod 4 is 0 or 1; every line is periodic with run <= 4.
gomoku::Board noFiveFill() {
  gomoku::Board board;
  for (int y = 0; y < gomoku::boardSize; ++y) {
    for (int x = 0; x < gomoku::boardSize; ++x) {
      const int mod = (x + 2 * y) % 4;
      board.place({x, y}, (mod == 0 || mod == 1) ? gomoku::Player::black
                                                 : gomoku::Player::white);
    }
  }
  return board;
}

// The no-five fill with row 3 carved to a four at (1,3)-(4,3) for `four` and
// exactly two empty cells (0,3) and (5,3).  The other player's stones keep
// the periodic fill; the result contains no five for either player.
gomoku::Board carvedBoard(gomoku::Player four) {
  gomoku::Board board;
  for (int y = 0; y < gomoku::boardSize; ++y) {
    for (int x = 0; x < gomoku::boardSize; ++x) {
      const gomoku::Coord move{x, y};
      if ((x == 0 && y == 3) || (x == 5 && y == 3)) {
        continue;
      }
      gomoku::Player player;
      if (y == 3 && x >= 1 && x <= 4) {
        player = four;
      } else {
        const int mod = (x + 2 * y) % 4;
        player = (mod == 0 || mod == 1) ? gomoku::Player::black
                                        : gomoku::Player::white;
      }
      board.place(move, player);
    }
  }
  return board;
}

void testDefenseTerminal() {
  const gomoku::Board fill = noFiveFill();
  require(fill.full(), "no-five fill must be full");
  require(!fill.hasFive(gomoku::Player::black),
          "no-five fill must not contain a black five");
  require(!fill.hasFive(gomoku::Player::white),
          "no-five fill must not contain a white five");

  gomoku::Position root;
  root.board = fill;
  const std::optional<gomoku::Outcome> terminal = root.board.terminal();
  require(terminal.has_value() && *terminal == gomoku::Outcome::draw,
          "full no-five board must be a draw terminal");

  gomoku::SearchConfig config;
  gomoku::DefenseSearcher white(config, gomoku::Player::white);
  const gomoku::DefenseSolveResult result = white.solve(root);
  require(result.status == gomoku::ProofSearchStatus::found,
          "a terminal draw must be found immediately");
  require(result.certificate.has_value(),
          "terminal draw must emit a certificate");
  require(result.certificate->nodes.size() == 1,
          "terminal draw certificate should have one node");
  gomoku::validateDefenseCertificate(root, *result.certificate);

  // Black five on the board: White cannot prevent, Black's defense closes.
  gomoku::Board five;
  for (int x = 0; x < 5; ++x) {
    five.place({x, 0}, gomoku::Player::black);
  }
  gomoku::Position blackWinRoot;
  blackWinRoot.board = five;
  require(blackWinRoot.board.terminal().has_value(),
          "five in a row must be terminal");

  gomoku::DefenseSearcher white2(config, gomoku::Player::white);
  const gomoku::DefenseSolveResult refuted = white2.solve(blackWinRoot);
  require(refuted.status == gomoku::ProofSearchStatus::refuted,
          "an attacker-win terminal must refute the defense");

  gomoku::DefenseSearcher black(config, gomoku::Player::black);
  const gomoku::DefenseSolveResult blackOk = black.solve(blackWinRoot);
  require(blackOk.status == gomoku::ProofSearchStatus::found,
          "a defender-win terminal must close the defense");
  require(blackOk.certificate.has_value() &&
              blackOk.certificate->nodes.size() == 1,
          "defender-win terminal certificate should have one node");
  gomoku::validateDefenseCertificate(blackWinRoot, *blackOk.certificate);
}

void testDefenseWhiteImmediateWin() {
  // White to move, four at (1,3)-(4,3), both ends empty.
  gomoku::Position root;
  root.board = carvedBoard(gomoku::Player::white);
  root.turn = gomoku::Player::white;
  require(!root.board.terminal().has_value(),
          "white-four root must be non-terminal");
  require(root.board.emptyMoves().size() == 2,
          "white-four root must have exactly two empties");

  gomoku::SearchConfig config;
  gomoku::DefenseSearcher searcher(config, gomoku::Player::white);
  const gomoku::DefenseSolveResult result = searcher.solve(root);
  require(result.status == gomoku::ProofSearchStatus::found,
          "White should prevent Black by winning immediately");
  require(result.certificate.has_value(),
          "found defense must emit a certificate");
  require(result.certificate->nodes.size() == 2,
          "defender move plus terminal win should be two nodes");
  const auto& rootNode = result.certificate->nodes.front();
  require(rootNode.kind == gomoku::DefenseNodeKind::defenderMove,
          "White-to-move defense should start with a defender move");
  gomoku::validateDefenseCertificate(root, *result.certificate);

  std::ostringstream lean;
  gomoku::writeLeanDefenseCertificate(lean, root, *result.certificate,
                                      "auditWhiteFour");
  require(lean.str().find("DefenseCertificate") != std::string::npos,
          "defense export should use the DefenseCertificate format");
  require(lean.str().find(".defenderMove") != std::string::npos,
          "defense export should emit defenderMove nodes");
  require(lean.str().find("checkDefenseCertificateAt") != std::string::npos,
          "defense export should call the Lean defense checker");
  require(lean.str().find("WhiteCanPreventBlackWin") != std::string::npos,
          "defense export should state the white defense theorem");
}

void testDefenseAttackerAllReplies() {
  // Black to move, same two-gap board: White must answer both replies.
  gomoku::Position root;
  root.board = carvedBoard(gomoku::Player::white);
  root.turn = gomoku::Player::black;
  require(!root.board.terminal().has_value(),
          "black-to-move root must be non-terminal");
  require(root.board.emptyMoves().size() == 2,
          "black-to-move root must have exactly two empties");

  gomoku::SearchConfig config;
  gomoku::DefenseSearcher searcher(config, gomoku::Player::white);
  const gomoku::DefenseSolveResult result = searcher.solve(root);
  require(result.status == gomoku::ProofSearchStatus::found,
          "White should answer both Black replies");
  require(result.certificate.has_value(),
          "found defense must emit a certificate");
  const auto& rootNode = result.certificate->nodes.front();
  require(rootNode.kind == gomoku::DefenseNodeKind::attackerMoves,
          "Black-to-move defense should start with attackerMoves");
  require(rootNode.children.size() == 2,
          "attacker node must cover both legal replies");
  require(result.certificate->nodes.size() == 5,
          "two-reply defense should have five nodes");
  gomoku::validateDefenseCertificate(root, *result.certificate);

  // Missing reply must be rejected by the preflight validator.
  gomoku::DefenseCertificate incomplete = *result.certificate;
  incomplete.nodes.front().children.pop_back();
  bool rejected = false;
  try {
    gomoku::validateDefenseCertificate(root, incomplete);
  } catch (const std::runtime_error&) {
    rejected = true;
  }
  require(rejected, "preflight must reject an omitted attacker reply");

  // Duplicate reply must be rejected as well.
  gomoku::DefenseCertificate duplicated = *result.certificate;
  duplicated.nodes.front().children.push_back(
      duplicated.nodes.front().children.front());
  rejected = false;
  try {
    gomoku::validateDefenseCertificate(root, duplicated);
  } catch (const std::runtime_error&) {
    rejected = true;
  }
  require(rejected, "preflight must reject a duplicate attacker reply");
}

void testDefenseRefutedImmediateAttackerWin() {
  // Black to move with a black four: an immediate winning move refutes
  // White's defense, so the search must answer Refuted (not Unknown).
  gomoku::Position root;
  root.board = carvedBoard(gomoku::Player::black);
  root.turn = gomoku::Player::black;
  require(!root.board.terminal().has_value(),
          "black-four root must be non-terminal");

  gomoku::SearchConfig config;
  gomoku::DefenseSearcher searcher(config, gomoku::Player::white);
  const gomoku::DefenseSolveResult result = searcher.solve(root);
  require(result.status == gomoku::ProofSearchStatus::refuted,
          "an immediate black win must refute White's defense");
  require(!result.certificate.has_value(),
          "refuted search must not emit a certificate");

  // The symmetric defense (Black prevents White) must be found here, since
  // Black is already threatening to win.
  gomoku::DefenseSearcher blackSearcher(config, gomoku::Player::black);
  const gomoku::DefenseSolveResult blackResult = blackSearcher.solve(root);
  require(blackResult.status == gomoku::ProofSearchStatus::found,
          "Black's own win threat closes BlackCanPreventWhiteWin");
  require(blackResult.certificate.has_value(),
          "black defense must emit a certificate");
  gomoku::validateDefenseCertificate(root, *blackResult.certificate);
}

void testDefenseUnknownPropagation() {
  // A tiny node budget must yield Unknown, never Found or Refuted.
  gomoku::SearchConfig config;
  config.maxNodes = 1;
  config.maxTableEntries = 10'000;
  gomoku::DefenseSearcher searcher(config, gomoku::Player::white);
  const gomoku::DefenseSolveResult result = searcher.solve(gomoku::Position{});
  require(result.status == gomoku::ProofSearchStatus::unknown,
          "exhausted budget must be Unknown, not Found or Refuted");
  require(!result.certificate.has_value(),
          "Unknown search must not emit a certificate");

  // A second run with a fresh searcher and a larger budget must still be
  // able to find a proof: Unknown results are never cached as permanent.
  gomoku::SearchConfig generous;
  generous.maxNodes = 0;
  gomoku::DefenseSearcher fresh(generous, gomoku::Player::black);
  gomoku::Position root;
  root.board = carvedBoard(gomoku::Player::black);
  root.turn = gomoku::Player::black;
  const gomoku::DefenseSolveResult found = fresh.solve(root);
  require(found.status == gomoku::ProofSearchStatus::found,
          "a fresh unlimited search must still find the defense");
}

void testDefenseTableLimit() {
  gomoku::SearchConfig config;
  config.maxTableEntries = 1;
  gomoku::DefenseSearcher searcher(config, gomoku::Player::white);
  const gomoku::DefenseSolveResult result = searcher.solve(gomoku::Position{});
  require(result.status == gomoku::ProofSearchStatus::unknown,
          "table exhaustion must be Unknown in defense mode");
}

}  // namespace

int main() {
  try {
    testGeometry();
    testParser();
    testImmediateCertificate();
    testOpponentForkCertificate();
    testCheckerSelection();
    testVcfHintCertificate();
    testResourceLimits();
    testDefenseTerminal();
    testDefenseWhiteImmediateWin();
    testDefenseAttackerAllReplies();
    testDefenseRefutedImmediateAttackerWin();
    testDefenseUnknownPropagation();
    testDefenseTableLimit();
    std::cout << "all C++ solver tests passed\n";
    return 0;
  } catch (const std::exception& error) {
    std::cerr << "test failure: " << error.what() << "\n";
    return 1;
  }
}
