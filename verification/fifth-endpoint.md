# Verification of the fifth-endpoint port

The port adds two modules and six public theorems:
[ExactSumResiduals](../CatchUp/ExactSumResiduals.lean) and
[LowerRayFifthEndpoint](../CatchUp/LowerRayFifthEndpoint.lean).
The pinned Lean 4.27.0/Mathlib revisions, game definitions and all 96 existing
mathematics proof files are preserved. The library imports and named audit entry
point are extended for the port. The cryptid package is unchanged.

[fifth-endpoint-port.json](fifth-endpoint-port.json) identifies both archived inputs
by original SHA-256, Git blob, source commit and source-ledger ID. The interface
is a named-lemma extraction; the endpoint is a whole-source port with disclosed
import/attribute/prose changes. `python3 scripts/check_fifth_endpoint_port.py`
reconstructs both files, checks fingerprints and theorem names, and rejects a
source mutation. It is included in `check_collection.py`. This checks transcription
fidelity, not Lean validity.

## Reproduce

From the repository root:

```sh
lake exe cache get
lake --wfail build
python3 scripts/check_axioms.py
python3 scripts/check_collection.py
python3 computation/check_semantics.py
lake env lean --run computation/CheckEarlier.lean
python3 computation/experiments/check.py
python3 computation/experiments/check_campaign.py
cd cryptid
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

The named axiom audit includes the interface, all four upper-opening exclusions
and the headline `N≥23` theorem. `AuditAll.lean` checks all imported public
Catch-Up theorems transitively. Only `propext`, `Classical.choice` and `Quot.sound`
are allowed; a negative control must reject `sorryAx`. Native-evaluator/compiler-trust
axioms, custom outcome axioms and the unfinished conjecture are excluded.

Kernel checking verifies the terms produced by the symbolic tactics. This is
not a replay of historical large outcome tables or a fresh build of the archived
fourth-endpoint theorem. See the [result guide](../results/fifth-endpoint.md)
for exact mathematical scope.

## Completed local checks

All commands below exited successfully on the port. The
[check receipt](fifth-endpoint-checks.json) records exact commands, elapsed times,
source fingerprints and hashes of the retained output logs.

| Check | Result |
| --- | --- |
| Full mathematics `lake --wfail build` | Passed; 7,984 build jobs, 291 seconds. |
| Mathematics transitive axiom audit | Passed: 162 named endpoints and all 4,364 public Catch-Up theorems, including generated declarations. |
| Full cryptid `lake build` | Passed; 9,249 build jobs, 319 seconds. Existing module-system import warnings remain in unchanged sources. |
| Cryptid transitive axiom audits | Passed: 23 baseline endpoints / 500 public theorems; 201 component endpoints / 2,962 public theorems. |
| Collection, provenance and documentation | Passed: 98 cataloged modules; both new sources reconstructed with mutation rejection; all retained export hashes and documentation links checked. |
| Original local Git history | Passed: 15 refs, 55 commits, 290 path/blob pairs and 183 source-version reconstructions. |
| Semantics and earlier certificate regressions | Passed: 832 noninitial states and 10 roots; extracted certificates through N=8; malformed certificates rejected. |
| Solver and campaign smoke checks | Both passed their bounded fixtures, independent recurrences, limit handling and corruption controls. No large table replay. |

All six added public theorem endpoints report only `propext`, `Classical.choice`
and `Quot.sound`. Each package's audit rejects its `sorryAx` negative control.
The public-theorem counts include generated declarations, not just the six new
source-level theorem statements.

These were fresh local library builds using the pinned Mathlib dependency caches,
not a from-source rebuild of Mathlib. Cache acquisition required retrying a
dependency checkout; no source or pin was changed. Timings cover the successful
verification commands, not dependency downloads or the entire investigation.
The original local Git checkout's absolute path is replaced by a placeholder in
the public receipt; no output log needed redaction. Earlier verification receipts
are preserved unchanged. Hosted CI has its own commit-specific results; local
success does not imply hosted completion.
