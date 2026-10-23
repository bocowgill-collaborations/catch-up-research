# Mutation, SMT and shrinking experiments

This collection recovers the remaining useful source, input and replay bundles from the October campaign. The [research notes](../../../archive/research-notes/) explain the hypotheses; [experimental findings](../../../results/experimental-findings.md) explain their mathematical limits. **The conjecture remains open.** These experiments diagnose auxiliary strategies and midgames. Their numerical outputs are not Lean proof certificates.

## Small reproduction commands

Requirements: Python 3.9+, a C++ compiler with C++20 support, and Linux or macOS. SMT commands additionally require `z3` on PATH, or the `Z3` environment variable pointing to its executable. Historical SMT runs used Z3 5.1.0; fresh receipts record the installed version. No Python Z3 package is needed.

From the repository root:

```sh
python3 computation/experiments/run_campaign.py mutation-joint
python3 computation/experiments/run_campaign.py mutation-two
python3 computation/experiments/run_campaign.py shrink-joint
python3 computation/experiments/run_campaign.py shrink-alternating
python3 computation/experiments/run_campaign.py smt-shadow
python3 computation/experiments/run_campaign.py smt-two
python3 computation/experiments/check_campaign.py
```

Defaults query a few frozen positions or tiny SMT arities, never the whole historical mutation neighborhood. The four position profiles contain 31 positions in total, with every first choice retained. `check_campaign.py` compares them to the independent absolute-score evaluator, runs original mutation drivers on fixed witnesses, checks all 16 original SMT goldens and both mover perspectives, detects always-alternating semantics, replays the 19-node/9-leaf shrinking DAG, regenerates seed lists without evaluating them, and rejects corrupt branches, circular references, unknown/error responses and timeouts. It does not rerun either large mutation prefix, the full shrinking sweeps or either unknown SMT extension.

Outputs go to fresh ignored directories under `verification/local/experiments/`. Use `--out /tmp/my-new-campaign-run` for another **new** directory. Evaluation children default to 10 seconds of wall time, a corresponding integer CPU limit, and 256 MiB of virtual address space on Linux. `--seconds` allows up to 60; `--memory-mib` allows up to 1024. macOS has wall/CPU limits but no claimed OS memory cap. Compilations have a separate 30-second wall limit. SMT also receives Z3's memory limit. These are per-child limits; encoding construction and the combined command duration have separate finite input bounds. Failure, timeout or `unknown` produces an incomplete receipt and exit code 2, with no game outcome inferred.

## What is preserved

| Family | Frozen inputs and original scope | Historical status |
| --- | --- | --- |
| [Two-anchor mutation](search/root_anchor_jointloss_mutation_seeds.py) | Deterministic radius-two parity-preserving edits, from 11 one-sided-loss controls; explicit 18,741-row list, parent links and operations | Stopped at first double loss after 11,149 cases; 7,592 unprocessed rows retained. The witness refutes a generic two-anchor auxiliary, not initial C. |
| [Adaptive minimum-two mutation](resume_01/two-guard-adaptive-mutation/run.py) | Explicit 199-case list and every edit, generated from one frozen support with unique safe choice 13 | Stopped at case 40; 159 unprocessed cases retained. The resulting 12-counter loss is an auxiliary counterexample. |
| [Alternating-tail generation](search/root_alternating_gap_generate.py) | Deterministic rank-parity rounding, 229 frozen tails and named controls | First loss at case 212; 17 unprocessed tails retained. Rank rounding was a candidate generator, never an outcome-preserving symmetry. |
| [Fixed-support shrinking](search/root_anchor_jointloss_shrink_probe.cpp) | All 512 deletion subsets of one nine-label tail; 256 even-sum queries, 256 odd-sum skips | Only the full tail has both deficit-1 and deficit-3 loss. This is deletion minimality within that one support, not a global minimum. |
| [Alternating shrinking](search/root_alternating_gap_shrink_probe.cpp) | All 128 deletions accounted for, 16 admissible inputs, then deterministic coordinate `-2` descent | Ends at a local fixed point. All trials, predicate skips and final choices are retained; this does not prove global optimality. |
| [Eight-shadow SMT](resume_01/shadow-smt/search.py) | Sorted distinct integer tail labels >=9, even sum; bounded tail cardinality, unbounded labels | Both joint-loss and shadow-loss queries at k=0..4 reported UNSAT. Shadow-only k=5 returned **unknown**. |
| [Minimum-two SMT](resume_01/two-guard-smt/search.py) | `R={2}∪U`, sorted distinct U>=3 with odd sum, deficit 1 | k=2..5 reported UNSAT; k=6 returned **unknown**. The subsequent mutation counterexample rules out the uniform claim. |

The precursor unpaired-tail and two-anchor probes, their seed generators/lists and literal audits are retained too. The unpaired generator records seeds **20261022 and 20261023**. The radius-two mutations, adaptive mutations, rank rounding and shrinking orders are deterministic and use no random seed. SMT query files set no random seed; solver/version differences may affect search behavior. Frozen explicit lists are authoritative for exact reproduction. Actual labels are retained; translations, rounding and mutations supply new test cases with no presumed value preservation.

Cutoff-seven/eight data extractors and literal audits are included. The self-contained minimum-two baseline evaluates every leaf rather than depending on private Lean aliases. Lean's `private` visibility modifier does not mark confidential research. These Python/C++ DAG checks remain experimental; the corresponding formal obstruction results are already in the [public Lean library](../../../results/modules.md).

## Reconstruct SMT inputs without solving

Small original SMT2 inputs and all saved result/status records are included. Larger generated inputs, up to roughly 20 MB, are represented by exact generator parameters, original byte counts and SHA-256 fingerprints in [campaign-sources.json](../../../verification/campaign-sources.json). These commands **generate files only**, without invoking Z3:

```sh
python3 computation/experiments/run_campaign.py emit-smt --family shadow-smt --k 4
python3 computation/experiments/run_campaign.py emit-smt --family shadow-smt --k 5 --shadow-only
python3 computation/experiments/run_campaign.py emit-smt --family two-guard-smt --k 6
```

The generator reuses the retained ownership-DAG `Encoding` and refuses an input whose bytes differ from the original fingerprint. It retains every pick, maximizes/minimizes the fixed-player ternary payoff, switches players at equality or overshoot, and keeps the same player below the deficit. Finishing compulsory picks when catching is impossible has the same terminal score as allocating all remaining counters. The encoding has no Lean soundness theorem, and no kernel-replayed UNSAT proof is supplied. Its fixed-cardinality UNSAT results do not establish any uniform statement. An [initial erroneous model request after UNSAT](resume_01/shadow-smt/initial-model-request-error/) is preserved; it exited with an error and is not treated as a clean successful query.

## Deliberate historical reproduction

These options are available but are **not run by the small checks or CI**:

```sh
python3 computation/experiments/run_campaign.py mutation-joint --scope historical --seconds 30
python3 computation/experiments/run_campaign.py mutation-two --scope historical --seconds 30
python3 computation/experiments/run_campaign.py shrink-joint --scope historical --seconds 15
python3 computation/experiments/run_campaign.py shrink-alternating --scope historical --seconds 30
python3 computation/experiments/run_campaign.py smt-shadow --k 4 --scope historical --seconds 30
```

Original first-witness stops are preserved: a successful execution may report `stopped_on_witness`, with planned/completed/unprocessed counts. It does not mean the full input list was evaluated. A resource stop remains incomplete. No command automatically resumes an unprocessed suffix. Larger SMT inputs retain their original internal timeout, but the wrapper's wall limit can expire earlier than the old 120-second runs. No completion or timing is promised across machines.

The older Python scripts write beside themselves and some directly run an entire batch. To use an original generator or literal audit, first make an isolated, complete source/data layout:

```sh
python3 computation/experiments/run_campaign.py prepare --out /tmp/catchup-legacy
```

This only copies `campaign/`, the shared solver header, and the independent literal evaluator. It executes no solver. A bounded example auditing the frozen small DAG is:

```sh
python3 - <<'PY'
from pathlib import Path
import sys
sys.path.insert(0, 'computation/experiments')
from run import bounded
work = Path('/tmp/catchup-legacy')
print(bounded([sys.executable, str(work/'campaign/search/root_alternating_gap_shrink_certificate7_check.py')],
              cwd=work, seconds=10, memory_mib=256))
PY
```

The same layout supports the retained original audits and generators. Recreating a JSON file can change timing, path and helper-source hash metadata; regenerated numerical inputs should be compared with the frozen input lists. Historical reports still describe their original paths and constraints. Original `max_rss_bytes` fields from C++ `getrusage` are platform-dependent: the old code did not convert Linux KiB to bytes. Do not use those labels to compare memory across operating systems without conversion.

## Private material and remaining scope

Excluded from publication are **your email threads and outreach draft, personal contact metadata, the privately received von Stengel slides/attachments and their private extraction/screenshots while sharing permission is pending**, plus account/usage records and automation/administrative settings. Those sources are not needed to run these experiments. The publicly hosted 2019 seminar source remains linked from the [source guide](../../../docs/sources.md). Failed examples, unproved hypotheses, incomplete searches and research checkpoints are included with evidence labels.

The [manifest](../../../verification/campaign-sources.json) records original/exported hashes, every source adaptation, dependency bundles, and dispositions for the inspected source/data paths. Machine-local paths are normalized, JSON is compacted, and the historical SMT launcher now finds Z3 through PATH or `Z3`; the ownership encoding is unchanged. Superseded duplicates, administrative receipts, a Lean-alias-dependent optimized audit, and unrelated interval/reflection/density replay routes are outside these executable bundles. The full near-repair forest extractor remains a separate publication gap. No verified proof or cryptid definition changed in this addition.
