# Reproduce retained experiments

These bundles recover the solver drivers, frozen input lists and seed generators behind several [research notes](../../archive/research-notes/). They use exact ternary outcomes, not score margins. **Their output is computational evidence, not a Lean certificate.** The corresponding formal results remain in the [Lean library](../../results/modules.md).

Requirements: Python 3.9 or later, a C++ compiler with C++20 support, and Linux or macOS. No Lean installation, external Python packages or solver service is needed. Set `CXX=clang++` or `CXX=g++` if `c++` is not the desired compiler. Run these commands from the repository root:

```sh
python3 computation/experiments/check.py
python3 computation/experiments/run.py packed --n 12
python3 computation/experiments/run.py consecutive
python3 computation/experiments/run.py seven-pairs
python3 computation/experiments/run.py four-orphan
python3 computation/experiments/run.py near-repair
python3 computation/experiments/run.py whole-turn
```

Every command above runs small checks only. The runner writes inputs, compile logs, raw results and `receipt.json` to a fresh directory under ignored `verification/local/experiments/`. Pass `--out /tmp/my-new-run` to choose another **new** directory. It refuses to overwrite an existing run. A complete receipt means the selected finite job finished; it does not establish a uniform strategy or certify all historical observations.

The runner gives each evaluation subprocess a 15-second wall limit and an integer CPU limit by default; compilation has a separate 30-second wall limit. `--seconds` changes the evaluation limit up to 60 seconds. On Linux, `--memory-mib 256` caps the evaluation child's virtual address space. macOS does not receive a hard memory cap; receipts state this explicitly. Input profiles are fixed and bounded on both systems. Compilation is not memory-capped. Timeout, allocation failure, malformed output or a child failure produces an **incomplete** receipt and exit code 2. Partial raw output is not a completed experiment and supplies no value for missing cases. Limits apply per subprocess, not to the combined duration of a multi-stage command.

## What each bundle tests

| Command | Default small diagnostic | Explicit historical scope |
| --- | --- | --- |
| `packed --n 12` | Exact initial interval, every opening, scalar table verification, save/load verification; `--n` restricted to 1..12 | Large tables are deliberately unavailable through this runner; see the [packed solver](../solvers/packed/). |
| `seven-pairs` | One seven-pair support `(4,6,10,12,20,40,42)` and the recursive-round obstruction at residual starts `(6,10,12,20,40)` | Frozen 594 root supports and 142 residual supports; every first pick and every enumerated completed opponent turn. |
| `four-orphan` | Four pairs with starts `(10,20,40,80)`, both orphan values `z=6,7`, both deficits `z,z+2`, every completed opponent turn | All frozen four-pair input supports from the seeded generator. |
| `near-repair` | Exact values and all first picks at the two reached decisions `q=42,98` | Original completed-turn-set probe for all 30 even values `q=42..100`; the final counter is recorded separately. |
| `consecutive` | `B_11={2,3,4,9,10,11}` at deficit 1; pick 2, then all five opponent replies and every friendly first choice | `B_N={2,3,4} ∪ [9,N]`, `N=11,12,15,16,19,20`; all 57 opponent replies after pick 2. |
| `whole-turn` | Ten-counter arithmetic obstruction to a one-turn balancing rule | Original seven/nine-pair whole-turn arithmetic test; no minimax solver and no root-outcome claim. |

`consecutive` rediscovers why an adjacent reply is insufficient: after pick 2 and opponent pick 9 at N=11, the defender faces `{3,4,10,11}` at deficit 8. The state draws, but replying 10 loses. Safe choices include 3, 4 and 11. This is a policy failure, not a counterexample to the conjecture.

The shared [slots.hpp](seven_pairs/slots.hpp) retains actual counter labels. Its dense cache has a separate unknown marker; stored values are exact. Its internal maximum is 14 supplied counters. The retained [consecutive driver](consecutive/probe.cpp) also handles 15 by evaluating all first children of size 14. This extension is finite, not a state symmetry. The supplied-label API requires nonempty support; the [Python explorer](../explore.py) handles empty positions. Internal empty-mask children are handled by the C++ recurrence. Only the validated runner should feed the raw consecutive driver's input protocol.

The shared header and older drivers have no reliable within-search wall timeout: some check a clock only between input rows. Always use the bounded runner. A winning short-circuit can finish a scalar minimax value without exploring every choice; the drivers explicitly iterate all choices needed for their reported first-reply tables. A favorable reply value allows optimal continuation, not necessarily repetition of the same proposed policy.

## Reproduce an original finite batch deliberately

Full batches are available, but are **not** run by the default commands or CI:

```sh
python3 computation/experiments/run.py seven-pairs --scope historical --seconds 30
python3 computation/experiments/run.py four-orphan --scope historical --seconds 30
python3 computation/experiments/run.py near-repair --scope historical --seconds 30
python3 computation/experiments/run.py consecutive --scope historical --seconds 30
python3 computation/experiments/run.py whole-turn --scope historical --seconds 60
```

These are bounded attempts, not runtime promises. A machine that cannot finish within the limits reports incomplete. The publication checks do not launch these batches, extend their parameter ranges or resume unfinished mutation searches. Existing [observation files](../observations/) remain historical outputs with their original coverage and unprocessed cases.

Seven-pair `candidates.py` uses seed 20261025; four-orphan `inputs.py` uses seed 20261028. Frozen inputs are supplied, so rerunning does not depend on a Python version's random sampling implementation. To regenerate, copy each small generator and its input dependencies into a temporary directory first: the original generators intentionally write beside themselves. `check.py` does this automatically and compares generated files byte-for-byte with the frozen lists. The whole-turn script constructs its finite supports deterministically and writes its generated data only in the runner's new directory.

## Scope of checking and provenance

`check.py` compares the explicit-slot solver with the separate absolute-score evaluator on all 302 nonempty-subset/deficit states from `{1,..,5}` through deficit `sum(R)+1`, including every reported pick. It checks initial roots N=1..12 and every opening of the packed solver, packed/absolute/whole-turn agreement on 4,096 mask/deficit states through N=8, both packed bit widths without allocating N=32, and ordered-turn enumeration through N=5. It independently replays all five N=11 opponent replies, all 38 opponent turns at the eleven-counter recursive-round diagnostic, and all 50 opponent turns across the four nine-counter orphan cases. Removing a real opponent branch is rejected. It also exercises corrupt outcomes, corrupt/truncated tables, invalid inputs, timeouts and failed children. Full historical strategy forests and larger batches are not independently replayed by this check.

Original/exported hashes and every adaptation for these first bundles are in [solver-sources.json](../../verification/solver-sources.json). Fourteen files come from the local downstream research, and the packed C++ source comes from the other local FormalConjectures checkout. All are byte-for-byte copies except one relocated include path. The portable runner and small checks are new adapters.

The [mutation, SMT and shrinking collection](campaign/) now adds original drivers, frozen inputs and deterministic seed recipes, original stopped prefixes, SMT input reconstruction and literal DAG audits. Start with `python3 computation/experiments/check_campaign.py` (requires Z3). Its separate [manifest](../../verification/campaign-sources.json) records the expanded inventory and adaptations. Other interval/reflection/density replay routes and the full near-repair strategy-forest extractor remain outside these bundles.
