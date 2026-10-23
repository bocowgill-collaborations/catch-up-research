// Small calibration only; includes the preserved implementation without running its CLI.
#define main preserved_catch_up_main
#include "catch_up_search.cpp"
#undef main

int main() {
  using namespace catch_up_search;
  try {
    std::uint64_t states = 0;
    testPackedBitOperations();  // Both word widths; does not allocate the N=32 table.
    testTerminalAndTransitionCases();
    for (unsigned n = 1; n <= 8; ++n) {
      AbsoluteAtomicSolver absolute(n);
      TurnBoundarySolver turns(n);
      PackedExactTable packed(n);
      packed.solve();
      require(packed.verifyScalar(1), "scalar table check failed");
      require(absolute.gameValue() == packed.gameValue(), "opening mismatch");
      for (std::uint32_t r = 0; r <= fullMask(n); ++r) {
        for (unsigned d = 0; d <= n; ++d) {
          const auto expected = absolute.value(r, 0, d, false);
          require(turns.value(r, d) == expected, "whole-turn mismatch");
          require(packed.outcome(r, d) == expected, "packed mismatch");
          ++states;
        }
      }
    }
    // Independently enumerate every ordered turn, including same-player picks.
    for (unsigned n = 1; n <= 5; ++n) {
      TurnBoundarySolver turns(n);
      MaskData masks(n);
      for (std::uint32_t r = 0; r <= fullMask(n); ++r) {
        for (unsigned d = 0; d <= masks.sum(r) + 1; ++d) {
          std::vector<std::uint32_t> actual;
          for (auto a : turns.legalActions(r, d)) actual.push_back(a.selected);
          require(actual == orderedSequenceActions(r, d, masks), "turn enumeration mismatch");
        }
      }
    }
    std::cout << "Small packed calibration passed: " << states << " normalized states\n";
  } catch (const std::exception& e) {
    std::cerr << e.what() << '\n';
    return 1;
  }
}
