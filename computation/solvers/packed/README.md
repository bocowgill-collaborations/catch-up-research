# Packed exact interval solver

The [August 7 historical run record](../../../archive/campaigns/packed-exact-run-2026-08-07.md) now preserves the original validation narrative, N=23–32 timings, memory measurements, table checksums and Monte Carlo observations at N=35,36. These are recorded runs, not new measurements. The obsolete frontier claim is corrected; the large table files were absent at their recorded locations.

[catch_up_search.cpp](catch_up_search.cpp) is the existing self-contained C++20 implementation recovered from the other local FormalConjectures checkout. Its Apache-2.0 notice is retained. It contains absolute-score atomic and completed-turn reference solvers, packed bottom-up exact tables, a scalar table verifier, serialization, and a separate Monte Carlo reconnaissance mode. **None is a Lean-certified checker.** The formal normalization theorem does not automatically verify this different implementation.

The file was untracked local research, so its checkout HEAD is context rather than a commit containing the solver. Its precise source is pinned by SHA-256 in [the provenance manifest](../../../verification/solver-sources.json). The old local report discussed computations through N=32; those large tables were not located or rerun in this audit. It is not a new frontier claim, and [earlier work](../../../docs/earlier-work.md) records the public 2019 report through N=34.

Use the [bounded runner](../../experiments/) first:

```sh
python3 computation/experiments/run.py packed --n 8
python3 computation/experiments/check.py
```

This builds, solves a small interval, reports every opening, verifies every stored label with scalar ternary minimax, saves the table, then reloads and verifies it. `check.py` also compiles [check_small.cpp](check_small.cpp), which compares the three exact implementations through N=8 and validates whole-turn generation through N=5. The preserved implementation's longer `--self-test` includes intervals through N=20 and is not part of these publication checks.

For direct development, the equivalent small commands are:

```sh
c++ -std=c++20 -O2 -pthread -Wall -Wextra -Werror \
  computation/solvers/packed/catch_up_search.cpp -o /tmp/catch_up_search
/tmp/catch_up_search --solve 8 --verify --threads 1 --save /tmp/catchup-small.bin
/tmp/catch_up_search --verify-table /tmp/catchup-small.bin --threads 1
```

The direct executable has **no resource limiter**; use an external limit before choosing larger inputs. For N<=31 its three main arrays need approximately `10*2^N` bytes; the N=32 variant needs approximately `18*2^32` bytes (72 GiB), before other overhead. Saving the N=32 table is disabled. Neither a default demonstration nor CI allocates these large tables. The preserved Monte Carlo mode is not invoked by the runner or publication tests, and its output cannot establish a game value.

Tables use magic `CATCHUP1`, little-endian 32-bit version 1, 32-bit N, 64-bit mask count, then one 32-bit win word and one 32-bit draw word per mask. A missing bit in both words means loss. The verifier checks all labels against terminals and transitions; it rejects the corrupted terminal bit and truncated file in the small tests. Verification here is still C++ computation, not kernel replay. JSON from the Python explorer and strategy DAGs from the Lean certificate checker use different formats.
