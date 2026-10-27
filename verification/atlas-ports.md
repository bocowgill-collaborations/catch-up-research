# Verification of the first-pair and failed-strategy atlas

Four archived sources are ported without changes to mathematical declarations,
proof bodies or original docstrings. Only import lines and repository-specific
category/AMS indexing attributes change. Original snapshots, reports,
certificates, reference rules, toolchain pins and the machine package are unchanged.

[atlas-ports.json](atlas-ports.json) pins original SHA-256, Git blobs, source
records/commits, adapted fingerprints, namespaces and public theorem names.
`scripts/check_atlas_ports.py` reconstructs the ports byte-for-byte and rejects
theorem-contract and proof-body mutations. This checks transcription; Lean checks
the mathematical terms.

There are 67 public theorem declarations: 18 adjacent-hole, 23 first-pair,
25 shifted-reply and one reserve-initialization result. All are imported through
`CatchUp.lean`, indexed, and explicit named audit endpoints. `AuditAll.lean` also
checks every imported public Catch-Up theorem transitively, including generated
theorems. Only `propext`, `Classical.choice` and `Quot.sound` are accepted.
The audit control rejects `sorryAx`; the export checker rejects placeholders,
native proof shortcuts and the unfinished conjecture. Finite examples use
`decide +kernel`.

The dated [handoff inventory](handoff-inventory.json) records public collection
counts and bounded local preservation checks, without publishing local paths or
claiming a fresh replay of the large certificate payloads.

## Reproduce

From the repository root with pinned Lean 4.27.0 dependencies available:

```sh
lake --wfail build CatchUp.AdjacentHoleExchangeObstruction CatchUp.FirstPairDescentObstruction CatchUp.ShiftedReplyCycle CatchUp.TurnReserveInitialization
lake --wfail build CatchUp
python3 scripts/check_axioms.py
python3 scripts/check_atlas_ports.py
python3 scripts/check_collection.py
```

The collection check includes atlas reconstruction, so CI checks source fidelity
alongside the library build and axiom audit. Local success does not imply that a
later hosted workflow has completed.

## Completed local checks

The warning-strict four-module and import-root builds passed. The axiom audit
accepted 241 named endpoints and all 4,672 imported public Catch-Up theorems using
only the three allowed axioms; the bad-axiom control was rejected. The full count
includes generated theorems and is not a count of distinct mathematical results.
Collection checks passed for 105 indexed modules, including archive hashes,
documentation links, source mutation controls and the supported two-buffer replay.
Independent semantics and earlier small-certificate regression checks also passed.

[atlas-checks.json](atlas-checks.json) records commands, exit status, source/output
fingerprints, scope and timings. The [named audit log](receipts/atlas-named-axioms.log)
and [full audit log](receipts/atlas-all-theorems.log) retain the actual audit outputs.
No large outcome tables were expanded and no cryptid sources were changed or
locally rebuilt for this batch.

## Mathematical review boundaries

The [atlas](../results/first-pair-atlas.md) gives exact witnesses and limitations.
Original comments retain some old module names; use the current atlas links and
[handoff](../docs/research-handoff.md) commands.

- The mandatory adjacent-hole left state draws: this refutes copying, not the
  proposed nonloss implication.
- The first-pair prefix witness has a drawing shadow root; it is not a universal
  strictly-winning-strategy translator obstruction.
- Shifted edges check availability/nonterminality. Raw reversal equations do not
  assert legality; the graph reduction gives a closed walk, not a simple cycle.
- The reserve theorem classifies one numerical envelope, not game outcomes.
  Reserve-preservation strategy arguments remain informal.

The exact original proof bodies were inspected in a constructive pass and an
adversarial self-review for polarity, player identities, equality, terminal
checks, support restrictions and quantifiers. No independent human or second-agent
review is claimed. The main conjecture and uniform first-pair/interior lower-ray
obligations remain open. The archived Lean controller is not imported here.
