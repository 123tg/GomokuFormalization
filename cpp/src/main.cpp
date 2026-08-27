#include "gomoku_solver.hpp"

#include <chrono>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <limits>
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

void usage(std::ostream& output) {
  output <<
      "Usage: gomoku_solver --input POSITION --output CERTIFICATE [options]\n"
      "\n"
      "Options:\n"
      "  --max-depth N             iterative DFPN ply bound (default 6)\n"
      "  --max-nodes N             expanded-node budget, 0 is unlimited\n"
      "  --max-table-entries N     transposition-table bound, 0 is unlimited\n"
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
      } else if (option == "--max-depth") {
        const std::uint64_t depth = parseUnsigned(requireValue(), option);
        if (depth > static_cast<std::uint64_t>(gomoku::boardCells)) {
          throw std::runtime_error("--max-depth cannot exceed 225 plies");
        }
        config.maxDepth = static_cast<std::uint16_t>(depth);
      } else if (option == "--max-nodes") {
        config.maxNodes = parseUnsigned(requireValue(), option);
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

    if (inputPath.empty() || outputPath.empty()) {
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

    std::cout << "status=" << gomoku::solveStatusName(result.status) << "\n";
    if (result.depth.has_value()) {
      std::cout << "depth=" << *result.depth << "\n";
    }
    std::cout << "expanded_nodes=" << result.stats.expandedNodes << "\n";
    std::cout << "table_entries=" << result.stats.tableEntries << "\n";
    std::cout << "table_hits=" << result.stats.tableHits << "\n";
    std::cout << "elapsed_ms=" << elapsed.count() << "\n";

    if (result.status != gomoku::SolveStatus::found ||
        !result.certificate.has_value()) {
      return result.status == gomoku::SolveStatus::depthLimit ? 2 : 3;
    }

    std::ofstream output(outputPath);
    if (!output) {
      throw std::runtime_error("cannot open certificate output: " + outputPath);
    }
    gomoku::writeLeanCertificate(output, problem.root, *result.certificate,
                                  definition);
    std::cout << "certificate_nodes=" << result.certificate->nodes.size()
              << "\n";
    std::cout << "output=" << outputPath << "\n";
    return 0;
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << "\n";
    return 1;
  }
}
