#include "gomoku_solver.hpp"

#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <limits>
#include <optional>
#include <stdexcept>
#include <string>

namespace {

std::uint64_t parseUnsigned(const std::string& value,
                            const std::string& option) {
  if (value.empty() || value.front() == '-') {
    throw std::runtime_error("invalid numeric value for " + option);
  }
  std::size_t consumed = 0;
  const std::uint64_t result = std::stoull(value, &consumed);
  if (consumed != value.size()) {
    throw std::runtime_error("invalid numeric value for " + option);
  }
  return result;
}

std::size_t parseSize(const std::string& value,
                      const std::string& option) {
  const std::uint64_t result = parseUnsigned(value, option);
  if (result > std::numeric_limits<std::size_t>::max()) {
    throw std::runtime_error("numeric value out of range for " + option);
  }
  return static_cast<std::size_t>(result);
}

std::string normalizeGoal(std::string value) {
  value.erase(std::remove_if(value.begin(), value.end(),
      [](char ch) { return ch == '-' || ch == '_' || ch == ' '; }),
      value.end());
  std::transform(value.begin(), value.end(), value.begin(),
      [](unsigned char ch) { return static_cast<char>(std::tolower(ch)); });
  return value;
}

std::size_t certificateEdgeCount(const gomoku::DefenseCertificate& certificate) {
  std::size_t edges = 0;
  for (const gomoku::DefenseCertificateNode& node : certificate.nodes) {
    switch (node.kind) {
      case gomoku::DefenseNodeKind::terminal:
        break;
      case gomoku::DefenseNodeKind::defenderMove:
        ++edges;
        break;
      case gomoku::DefenseNodeKind::attackerMoves:
        edges += node.children.size();
        break;
    }
  }
  return edges;
}

void usage(std::ostream& output) {
  output <<
      "Usage: gomoku_solver --input POSITION --output CERTIFICATE [options]\n"
      "       gomoku_solver --prove GOAL [--root empty | --input POSITION]\n"
      "                     --output CERTIFICATE [options]\n"
      "\n"
      "Options:\n"
      "  --prove GOAL             prevent-black-win | prevent-white-win\n"
      "  --root MODE              only 'empty' (7x7 empty board, Black to move)\n"
      "  --input FILE             position file (turn/target or turn only)\n"
      "  --output FILE            generated Lean certificate file\n"
      "  --max-depth N            iterative DFPN ply bound (default 6)\n"
      "  --max-vcf-depth N        bounded VCF hint horizon (default 7)\n"
      "  --max-nodes N            expanded-node budget, 0 is unlimited\n"
      "  --max-vcf-nodes N        VCF probe budget, 0 is unlimited\n"
      "  --max-table-entries N    transposition-table bound, 0 is unlimited\n"
      "  --max-certificate-nodes N emitted certificate bound\n"
      "  --max-prover-moves N      selective target width, 0 is complete\n"
      "  --definition NAME         generated Lean definition prefix\n"
      "  --no-forced-pruning       disable target immediate/defense pruning\n"
      "  --help                    show this message\n";
}

}  // namespace

int main(int argc, char** argv) {
  try {
    gomoku::SearchConfig config;
    std::string inputPath;
    std::string outputPath;
    std::string definition = "cppGenerated";
    std::optional<gomoku::Player> defender;
    bool rootIsEmpty = false;

    for (int index = 1; index < argc; ++index) {
      const std::string option = argv[index];
      auto requireValue = [&]() -> std::string {
        if (index + 1 >= argc) {
          throw std::runtime_error("missing value for " + option);
        }
        return argv[++index];
      };

      if (option == "--input") {
        inputPath = requireValue();
      } else if (option == "--output") {
        outputPath = requireValue();
      } else if (option == "--definition") {
        definition = requireValue();
      } else if (option == "--prove") {
        const std::string goal = normalizeGoal(requireValue());
        if (goal == "preventblackwin") {
          defender = gomoku::Player::white;
        } else if (goal == "preventwhitewin") {
          defender = gomoku::Player::black;
        } else {
          throw std::runtime_error(
              "--prove expects prevent-black-win or prevent-white-win");
        }
      } else if (option == "--root") {
        const std::string mode = requireValue();
        if (mode != "empty") {
          throw std::runtime_error("--root only supports 'empty'");
        }
        rootIsEmpty = true;
      } else if (option == "--max-depth") {
        const std::uint64_t depth = parseUnsigned(requireValue(), option);
        if (depth > static_cast<std::uint64_t>(gomoku::boardCells)) {
          throw std::runtime_error("--max-depth cannot exceed " +
              std::to_string(gomoku::boardCells) + " plies");
        }
        config.maxDepth = static_cast<std::uint16_t>(depth);
      } else if (option == "--max-vcf-depth") {
        const std::uint64_t depth = parseUnsigned(requireValue(), option);
        if (depth > static_cast<std::uint64_t>(gomoku::boardCells)) {
          throw std::runtime_error("--max-vcf-depth cannot exceed " +
              std::to_string(gomoku::boardCells) + " plies");
        }
        config.maxVcfDepth = static_cast<std::uint16_t>(depth);
      } else if (option == "--max-nodes") {
        config.maxNodes = parseUnsigned(requireValue(), option);
      } else if (option == "--max-vcf-nodes") {
        config.maxVcfNodes = parseUnsigned(requireValue(), option);
      } else if (option == "--max-table-entries") {
        config.maxTableEntries = parseSize(requireValue(), option);
      } else if (option == "--max-certificate-nodes") {
        config.maxCertificateNodes = parseSize(requireValue(), option);
      } else if (option == "--max-prover-moves") {
        config.maxProverMoves = parseSize(requireValue(), option);
      } else if (option == "--no-forced-pruning") {
        config.forcedMovePruning = false;
      } else if (option == "--help" || option == "-h") {
        usage(std::cout);
        return 0;
      } else {
        throw std::runtime_error("unknown option: " + option);
      }
    }

    if (outputPath.empty()) {
      usage(std::cerr);
      return 1;
    }

    if (defender.has_value()) {
      // ------------------------------------------------------------------
      // Defense proof mode: complete AND/OR search with Found/Refuted/Unknown.
      // ------------------------------------------------------------------
      gomoku::Position root;
      if (rootIsEmpty) {
        root = gomoku::Position{};
      } else {
        if (inputPath.empty()) {
          throw std::runtime_error(
              "defense mode requires --root empty or --input FILE");
        }
        std::ifstream input(inputPath);
        if (!input) {
          throw std::runtime_error("cannot open position file: " + inputPath);
        }
        root = gomoku::parseProblem(input).root;
      }

      gomoku::DefenseSearcher searcher(config, *defender);
      const auto started = std::chrono::steady_clock::now();
      gomoku::DefenseSolveResult result = searcher.solve(root);
      const auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
          std::chrono::steady_clock::now() - started);

      std::cout << "board_size=" << gomoku::boardSize << "\n";
      std::cout << "win_length=" << gomoku::winLength << "\n";
      std::cout << "rules=standard\n";
      std::cout << "root=" << (rootIsEmpty ? "empty" : "input") << "\n";
      std::cout << "proof_goal="
                << (*defender == gomoku::Player::white
                        ? "prevent_black_win"
                        : "prevent_white_win")
                << "\n";
      std::cout << "status=" << gomoku::proofSearchStatusName(result.status)
                << "\n";
      std::cout << "search_nodes=" << result.stats.expandedNodes << "\n";
      std::cout << "search_depth=" << result.stats.maxDepthReached << "\n";
      std::cout << "time_ms=" << elapsed.count() << "\n";
      std::cout << "cache_entries=" << result.stats.tableEntries << "\n";
      std::cout << "cache_hits=" << result.stats.tableHits << "\n";
      std::cout << "d4=false\n";
      std::cout << "pairing=false\n";
      std::cout << "partial_pairing=false\n";
      std::cout << "relevancy=false\n";
      std::cout << "potential=false\n";
      std::cout << "dominance=false\n";
      std::cout << "transposition=true\n";

      if (result.status != gomoku::ProofSearchStatus::found ||
          !result.certificate.has_value()) {
        std::cout << "certificate=none\n";
        std::cout << "certificate_nodes=0\n";
        std::cout << "certificate_edges=0\n";
        std::cout << "certificate_bytes=0\n";
        std::cout << "lean_checker=not-run\n";
        return result.status == gomoku::ProofSearchStatus::unknown ? 2 : 3;
      }

      std::ofstream output(outputPath);
      if (!output) {
        throw std::runtime_error("cannot open certificate output: " + outputPath);
      }
      gomoku::writeLeanDefenseCertificate(output, root, *result.certificate,
                                           definition);
      const std::streamoff certificateBytes =
          static_cast<std::streamoff>(output.tellp());
      output.flush();
      if (!output) {
        throw std::runtime_error("failed to write certificate output: " + outputPath);
      }
      std::cout << "certificate=some\n";
      std::cout << "certificate_nodes=" << result.certificate->nodes.size()
                << "\n";
      std::cout << "certificate_edges="
                << certificateEdgeCount(*result.certificate) << "\n";
      std::cout << "certificate_bytes=" << certificateBytes << "\n";
      std::cout << "lean_checker=not-run\n";
      std::cout << "output=" << outputPath << "\n";
      return 0;
    }

    // ------------------------------------------------------------------
    // Existing force-win mode (regression behaviour unchanged).
    // ------------------------------------------------------------------
    if (inputPath.empty()) {
      usage(std::cerr);
      return 1;
    }

    std::ifstream input(inputPath);
    if (!input) {
      throw std::runtime_error("cannot open position file: " + inputPath);
    }
    const gomoku::ParsedProblem problem = gomoku::parseProblem(input);
    if (problem.root.board.terminal().has_value()) {
      std::cerr << "warning: root position is already terminal\n";
    }

    gomoku::DfpnSolver solver(config, problem.target);
    const auto started = std::chrono::steady_clock::now();
    gomoku::SolveResult result = solver.solve(problem.root);
    const auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
        std::chrono::steady_clock::now() - started);

    std::cout << "search_target=" << gomoku::playerName(problem.target) << "\n";
    std::cout << "max_depth=" << config.maxDepth << "\n";
    std::cout << "max_vcf_depth=" << config.maxVcfDepth << "\n";
    std::cout << "max_nodes=" << config.maxNodes << "\n";
    std::cout << "max_vcf_nodes=" << config.maxVcfNodes << "\n";
    std::cout << "max_table_entries=" << config.maxTableEntries << "\n";
    std::cout << "max_certificate_nodes=" << config.maxCertificateNodes << "\n";
    std::cout << "max_prover_moves=" << config.maxProverMoves << "\n";
    std::cout << "forced_move_pruning="
              << (config.forcedMovePruning ? "true" : "false") << "\n";
    std::cout << "status=" << gomoku::solveStatusName(result.status) << "\n";
    if (result.depth.has_value()) {
      std::cout << "depth=" << *result.depth << "\n";
    }
    std::cout << "expanded_nodes=" << result.stats.expandedNodes << "\n";
    std::cout << "table_entries=" << result.stats.tableEntries << "\n";
    std::cout << "table_hits=" << result.stats.tableHits << "\n";
    std::cout << "vcf_nodes=" << result.stats.vcfNodes << "\n";
    std::cout << "vcf_table_hits=" << result.stats.vcfTableHits << "\n";
    std::cout << "vcf_root_solved="
              << (result.stats.vcfRootSolved ? "true" : "false") << "\n";
    std::cout << "vcf_budget_exhausted="
              << (result.stats.vcfBudgetExhausted ? "true" : "false")
              << "\n";
    std::cout << "elapsed_ms=" << elapsed.count() << "\n";

    if (result.status != gomoku::SolveStatus::found ||
        !result.certificate.has_value()) {
      std::cout << "certificate=none\n";
      std::cout << "lean_checker=not-run\n";
      return result.status == gomoku::SolveStatus::depthLimit ? 2 : 3;
    }

    std::ofstream output(outputPath);
    if (!output) {
      throw std::runtime_error("cannot open certificate output: " + outputPath);
    }
    gomoku::writeLeanCertificate(output, problem.root, *result.certificate,
                                  definition);
    const std::streamoff certificateBytes =
        static_cast<std::streamoff>(output.tellp());
    output.flush();
    if (!output) {
      throw std::runtime_error("failed to write certificate output: " + outputPath);
    }
    std::cout << "certificate=some\n";
    std::cout << "certificate_nodes=" << result.certificate->nodes.size()
              << "\n";
    std::cout << "certificate_bytes=" << certificateBytes << "\n";
    std::cout << "certificate_sharing=false\n";
    std::cout << "cache_key=depth,target,turn,black_bits,white_bits\n";
    std::cout << "lean_checker="
              << (gomoku::usesGlobalCertificateChecker(
                      problem.root, *result.certificate)
                      ? "checkCertificate"
                      : "checkLocalCertificateAt")
              << "\n";
    std::cout << "output=" << outputPath << "\n";
    return 0;
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << "\n";
    return 1;
  }
}
