> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.TwoAnchorDoubleLossObstruction](../../CatchUp/TwoAnchorDoubleLossObstruction.lean).

# Fixed-support deletion shrink and proof data

The independently verified double-loss tail

```
T={18,33,35,36,52,56,62,74,100}
```

has **no deletion compression within this support**. All512 subsets are retained:256 even-sum subsets were exactly queried,256 odd-sum subsets were recorded/skipped. Exactly one even subset has both losses—the full original T. The objective `(cardinality,max,sum,lex)` minimum within this fixed support is therefore unchanged: cardinality9, maximum100, sum466. No global minimum claim is made.

For E={4,7}∪T, E1 and E3 both lose and every first pick loses. C={2,3,4,7}∪T has C8WIN, C2WIN, and `(C.erase2,4)` LOSS. The minimum is identical to the original mutation witness, so `root_anchor_jointloss_shrink_results.json` explicitly reuses and hashes its already-complete independent literal receipt; it does not relabel a native-only result as literal verification. All five supports/deficits/values/full first-pick maps were compared for exact identity.

The proof worker requested shared normalized proof data down to small leaves, using only the same finalized E1/E3/C8 roots. Unchanged ExactSlots supplies each node's exact support, deficit and value. WIN nodes retain one winning pick; LOSS nodes retain every legal pick. Each edge records the actual picked counter, role switch (`x≥d`, including equality), child deficit `|x-d|`, and child value. Support+deficit nodes are shared, and children precede parents. No new tail or root was searched.

| Data file | Cutoff | Nodes | Leaves | Edges | Roots E1/E3/C8 |
|---|---:|---:|---:|---:|---|
| `root_anchor_jointloss_shrink_certificate.json` | 8 | 145 | 86 | 152 | 55 /110 /145 |
| `root_anchor_jointloss_shrink_certificate7.json` | 7 | 290 | 145 | 308 | 112 /222 /290 |

Both exports have independent edge audits and literal-score verification of **every leaf**. Cutoff8 remains unchanged after the separate cutoff7 request. Hardest literal cutoff8 leaf: `{2,18,35,36,52,62,74,100}`, deficit31, WIN (2,628 cached literal states). Hardest cutoff7 leaf: `{2,7,18,52,62,74,100}`, deficit23, WIN (987 cached states). These are data-complexity controls, not claimed worst cases for Lean.

The exports cover E1LOSS, E3LOSS and C8WIN. The erased-2 loss and C2 win retain their independent literal evidence but are not roots of this DAG export. `density_boundary_proof` owns the Lean construction and kernel checks; no proof source was changed here. Certificate data is not a completed kernel theorem.

The exact512 subset records, all successful subsets, objective minimum and reused literal provenance are in `root_anchor_jointloss_shrink_results.json`. Source/dump/JSON/audit/run receipts remain separate for each cutoff. The manifest verifies the original source literal receipt and all new artifacts; stopped mutation evidence remains intact. All shrink and same-state extraction/validation jobs together used less than10s and512MiB (exact command/resource totals are retained in the run JSON). No further subset/support search was started.
