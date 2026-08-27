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
  gomoku::Board horizontal;
  for (int x = 5; x <= 8; ++x) {
    horizontal.place({x, 7}, gomoku::Player::black);
  }
  require(horizontal.createsFive({4, 7}, gomoku::Player::black),
          "left horizontal endpoint should win");
  require(horizontal.createsFive({9, 7}, gomoku::Player::black),
          "right horizontal endpoint should win");
  require(!horizontal.createsFive({7, 6}, gomoku::Player::black),
          "unrelated move should not win");

  gomoku::Board diagonal;
  for (int value = 0; value < 4; ++value) {
    diagonal.place({value, value}, gomoku::Player::white);
  }
  require(diagonal.createsFive({4, 4}, gomoku::Player::white),
          "boundary diagonal should win");
}

void testParser() {
  std::ostringstream text;
  text << "turn black\n";
  text << "target black\n";
  for (int y = 0; y < gomoku::boardSize; ++y) {
    text << (y == 7 ? ".....XXXX......" : "...............")
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

  std::ostringstream lean;
  gomoku::writeLeanCertificate(lean, root, *result.certificate,
                               "cppSmoke");
  require(lean.str().find("checkLocalCertificateAt") != std::string::npos,
          "export should call the current Lean checker");
  require(lean.str().find("CompactCertificate") != std::string::npos,
          "export should retain CompactCertificate format");
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

}  // namespace

int main() {
  try {
    testGeometry();
    testParser();
    testImmediateCertificate();
    testOpponentForkCertificate();
    testResourceLimits();
    std::cout << "all C++ solver tests passed\n";
    return 0;
  } catch (const std::exception& error) {
    std::cerr << "test failure: " << error.what() << "\n";
    return 1;
  }
}
