# Formal two-buffer ports: provenance and verification

Port date: 27 October 2026. Base: `261fcc3e2d8d47daa8918e895600d71792a02a2d`.
The [manifest](controller-ports.json) pins five original archived inputs by
source ID, Git blob, observed source commit and SHA-256, plus the adapted paths
and fingerprints. The [result guide](../results/two-buffer-controller.md) states
the finite protocol's quantifiers, local repair hypotheses and remaining gaps.

## Exact adaptation

The [reconstruction checker](../scripts/check_controller_ports.py) permits only
four import-reference mappings and removal of `category`/AMS indexing
attributes. It reproduces every statement, proof body and original docstring.
All 34 public theorem declarations, including the mixed namespaces of
`ScoreDebtRepairCertificates`, are named axiom-audit endpoints. Contract, proof,
shadow-filter and policy mutations are rejected.

Original reports, archived source snapshots, replay code/data, certificates,
reference rules, dependency pins and previous verification receipts are
unchanged. The new manifest and receipt supplement rather than rewrite them.
The current default mathematics import contains 110 cataloged modules.

## Reproduce

From the root with the pinned Lean 4.27.0 dependencies available:

```sh
lake --wfail build CatchUp.ScoreDebtRepairCertificates CatchUp.TwoBufferProtocol CatchUp.TwoBufferMandatory CatchUp.TwoPickDebtRepair CatchUp.CompletedMarginBounds
lake --wfail build CatchUp
python3 scripts/check_controller_ports.py
python3 scripts/check_controller_policy.py --lean
python3 scripts/check_axioms.py
python3 scripts/check_collection.py
python3 computation/check_semantics.py
lake env lean -DwarningAsError=true --run computation/CheckEarlier.lean
```

The policy checker first replays the preserved JSON independently of synthesis,
then checks the restricted literal Lean table against every reachable
nonterminal state. With `--lean`, the
[Lean exporter](../computation/CheckTwoBuffer.lean) must output precisely that
same table. No policy choices are resynthesized. Six policy mutations cover a
wrong pick, wrong game, deficit or mover, missing row and conflicting key.
The existing replay additionally checks ownership, ledger, legal branches,
atomic buffers, terminal margins and its own negative controls.

CI's collection job checks exact source reconstruction and policy/replay
matching without needing Lean. The mathematics job also checks the actual Lean
export after building. The cryptid package is unchanged and remains separate.

## Recorded checks and limitations

[controller-checks.json](controller-checks.json) records commands actually run,
exit codes, timings, source hashes and new log fingerprints. Named and full
axiom audits run warning-strictly and reject a deliberate `sorryAx` control;
their only allowed transitive axioms are standard Lean axioms. The full public
theorem count includes generated declarations, not just mathematical results.

The policy comparison found 76 Lean rows, 74 distinct normalized keys, 87 replay
nodes and 17 terminal histories. Repeated keys prescribe identical actions;
first-match lookup therefore agrees with all recorded histories. The original
table remains intact.

This is a source-preserving port and local mathematical/semantic review, not
an independent new proof review or a hosted-CI success claim. The formal result
is the finite inductive protocol, its checker, enforceable margin bounds and
stated local repair lemmas. A general strategy-extraction bridge and uniform
adjacent-hole closure are not added. No new outcome tables, large searches or
machine rebuild were needed.
