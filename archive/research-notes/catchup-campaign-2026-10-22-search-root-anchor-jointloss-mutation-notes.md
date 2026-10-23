> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.TwoAnchorDoubleLossObstruction](../../CatchUp/TwoAnchorDoubleLossObstruction.lean).

# The generic two-anchor auxiliary has a verified double-loss diagnostic

Let

```
T = {18,33,35,36,52,56,62,74,100},  sum(T)=466,
E = {4,7} ∪ T.
```

The unchanged ExactSlots solver and independent literal-score replay agree that **V(E,1)=LOSS and V(E,3)=LOSS**. Every one of the11 legal first picks loses at each deficit. This falsifies the proposed unconditional auxiliary forbidding simultaneous loss.

The actual B-anchor context remains winning:

| State | Value |
|---|---|
| `(E,1)` | LOSS |
| `(E,3)` | LOSS |
| `C={2,3,4,7}∪T`, deficit8 | WIN |
| `C`, deficit2 | WIN |
| `C.erase2`, deficit4 | LOSS |

C8 first picks3,4,7 win; only4 wins at C2. Every first pick loses at the erased-2 target. All five state values and full first-pick maps were literally replayed, including continuation/equality cases. Thus this also defeats unconditional nonloss of the erased-2 endpoint, but **does not refute the C8LOSS-conditional reflections, B anchor, actual interval Q_N statement, or conjecture C**. C8 is WIN here.

The fixed mutation list has18,741 distinct actual tails:11 saved one-sided-loss controls,372 radius-one mutants,18,358 radius-two mutants. Four short controls were mutated; seven controls containing labels above128 were evaluated without generating mutations. Radius means at most two specified operations, not numerical distance. Operations are one±2 counter change, two simultaneous distinct-counter±1 changes, and insertion/deletion of one even counter. New tails are distinct,≥9, even-sum and≤128; the actual maximum new tail cardinality is10. Only identical actual tails were deduplicated; no translation, scaling or other symmetry was assumed.

The search stopped immediately at the first double loss, case11,149. It completed all11 controls, all372 radius-one cases, and10,766 radius-two cases. **7,592 generated radius-two cases remain unprocessed**; they were not draws, losses, or completed checks. The prefix contains14 E1-loss cases and983 E3-loss cases, with exactly one simultaneous loss. This is a first-found diagnostic, not a globally minimal counterexample.

Its exact saved path is:

```
control node6: T0={18,32,34,36,52,56,62,74}, E1WIN/E3LOSS
node244: simultaneously32→33 and34→35
node11149: add even counter100
```

T0 is the doubled shifted-cycle prior geometry. Both operations preserve even tail sum. All source/parent IDs, every completed ternary pair, the full explicit planned list, and the remaining input rows are retained. The checkpoint says first double loss, not a resource stop. No continuation is scheduled.

The separately requested named control `R={2,3,4,9,10,12,15}`, deficit1, draws. Its full first-pick map is `2:L,3:L,4:D,9:L,10:L,12:L,15:L`. This control was also literally checked; it does not settle unconditional R1 nonloss.

`root_anchor_jointloss_mutation_literal.json` is complete: six state checks (five witness contexts plus named R1),67 first-pick values, separate literal job1.048s/71.2MB. The original search source/log remain intact. Generation/compile/search/metadata external time totals2.405s (internal search0.494s), within the20s search/30s total limits. Peak compiler RSS142,049,280 bytes; solver5,308,416 bytes; metadata85,557,248 bytes. No interval table, solver-limit extension, Lean source edit, or new tail beyond the fixed list occurred.

The separately authorized fixed-support deletion audit is in `root_anchor_jointloss_shrink_*`: all512 subsets accounted,256 even subsets queried, and the full T is the only double-loss subset. It does not prove global minimality. Same-state proof data for E1/E3/C8 were handed to the kernel prover; those exports are certificate data, not themselves a Lean theorem.
