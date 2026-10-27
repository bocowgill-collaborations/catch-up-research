# Endpoint and trap atlas: provenance and checks

Port date: 27 October 2026. Base: `aa0a582866f8578456d00d8ca477a2f7b4918315`.
The [manifest](endpoint-atlas-ports.json) pins original paths, source IDs, observed
commits, Git blobs and SHA-256 hashes, adapted fingerprints, namespaces and theorem
inventories. The [result guide](../results/endpoint-trap-atlas.md) explains scope.

| Module | Public theorems | Adapted imports |
| --- | --- | --- |
| [LowerRayEndpoints](../CatchUp/LowerRayEndpoints.lean) | 3 | `CatchUp.Earlier.DeficitWinningBound` |
| [AdjacentPairGeometryObstruction](../CatchUp/AdjacentPairGeometryObstruction.lean) | 4 | `CatchUp.Reference`, `CatchUp.Earlier.TopFourClassification` |
| [FiveConsecutiveTrap](../CatchUp/FiveConsecutiveTrap.lean) | 5 | `CatchUp.Earlier.TopFourClassification`, `CatchUp.WinningOpening`, `CatchUp.Earlier.LowerRayExactDeficit` |

Only five possible import mappings and removal of category/AMS indexing
attributes are permitted. Original statements, hypotheses, proofs and docstrings
remain verbatim. The existing pair API supplies the required qualified name;
no declaration rename is needed. The default library now catalogs 117 modules.

The [checker](../scripts/check_endpoint_atlas_ports.py), included in collection
CI, checks hashes, Git blobs, attribution, reconstruction and all 12 named axiom
endpoints. Ten mutation controls reject changed names, proofs, bounds and the
reached player's identity. Source fidelity is not kernel checking.

## Reproduce

From the root with pinned Lean 4.27.0 dependencies:

```sh
lake --wfail build CatchUp.LowerRayEndpoints CatchUp.AdjacentPairGeometryObstruction CatchUp.FiveConsecutiveTrap CatchUp
python3 scripts/check_endpoint_atlas_ports.py
python3 scripts/check_axioms.py
python3 scripts/check_collection.py
python3 computation/check_semantics.py
python3 scripts/check_controller_policy.py --lean
lake env lean -DwarningAsError=true --run computation/CheckEarlier.lean
```

The [new receipt](endpoint-atlas-checks.json) records commands, timings, source/log
fingerprints, axiom checks and preservation comparison. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed transitively; the `sorryAx` control
must be rejected. Full-audit counts include generated declarations, not only
distinct mathematical results. Hosted CI has separate results.

Constructive and hostile self-review checks bounds, turn switches, terminal
conditions and polarity. It is not a new independent human review. Reachability
is not forced entry, and a losing pick is not a losing parent. No theorem assumes
the general Catch-Up conjecture.

Existing proof modules, archives, reports, certificates, prior manifests and
receipts, pins, workflow and replay bundles are unchanged. The cryptid package
is unchanged and is not rebuilt locally. This batch neither publishes large
certificate objects nor formalizes the packing lemma.
