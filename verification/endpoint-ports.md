# Verification of the earlier endpoint ports and controller replay

The new endpoint modules preserve the archived mathematical declarations and
proof bodies. Imports/module references and repository indexing attributes are
adapted to this standalone package. `LowerRayFourthEndpoint` omits only the
generic exact-sum declaration already exported unchanged by `ExactSumResiduals`.
The original archives, all 98 previous proof modules, game rules, pins and machine
sources are preserved.

[endpoint-ports.json](endpoint-ports.json) records original SHA-256, Git blobs,
source branches/commits/IDs, current fingerprints and the ten public theorem
names. `scripts/check_endpoint_ports.py` reconstructs the ports exactly and rejects
source mutations. This checks transcription fidelity; Lean verifies the terms.

The [finite two-buffer bundle](../computation/experiments/earlier-campaign/two-buffer/)
is checked computationally. [Its manifest](two-buffer-replay.json) identifies five
archived inputs and four extracted/adapted exports, including the unchanged policy
and full historical replay. `scripts/check_two_buffer_sources.py` reconstructs the
exports and challenges equality-rule and buffer-bound changes. The new replay
check compares all stored states and legal child values with a separate recurrence,
checks the complete historical output, rejects nine policy mutations and rejects
optimized Python execution that would disable assertions.

## Reproduce

From the repository root, with the pinned Lean dependencies/cache available:

```sh
lake --wfail build CatchUp.LowerRayAntepenultimateDescent CatchUp.LowerRayFourthEndpoint
lake --wfail build CatchUp
python3 scripts/check_axioms.py
python3 scripts/check_collection.py
python3 computation/experiments/earlier-campaign/two-buffer/check.py
```

The audit includes all ten new public declarations in `AxiomAudit.lean` and every
imported public Catch-Up theorem in `AuditAll.lean`. Only `propext`,
`Classical.choice` and `Quot.sound` are accepted; a control rejects `sorryAx`.
The small fourth-endpoint computations use `decide +kernel`; no native-evaluation
trust axiom or unfinished conjecture is allowed. The collection checker also runs
both reconstruction scripts and the bounded replay, so CI includes these checks.

The new [result guide](../results/lower-ray-endpoints.md) states the hypotheses
and proof arguments. The supported replay does not add the historical Lean
controller proof to the maintained library or establish an unbounded translator.
The cryptid package is unchanged and its separate verification remains as recorded.

Completed local commands and output fingerprints are recorded in
[endpoint-import-checks.json](endpoint-import-checks.json). Their scope is the
affected mathematics and collection; a successful local check does not predict
the status of a later hosted workflow.

The strict endpoint and import-root builds passed. The audit accepted 172 named
declarations and all 4,500 imported public Catch-Up theorems using only the three
allowed axioms. Collection checks passed for all 100 cataloged modules. The replay
checked 87 nodes, 17 terminal histories and 174 stored-state comparisons, plus
legal child values and the rejection controls described above.
