> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current results guide](../../results/README.md).

# Two-anchor auxiliary: no simultaneous loss in the authorized batch

All **257 cases completed**: the exact256 saved B tails from `root_anchor_unpaired_seeds.json`, plus the separately authorized prior control `T={9,10,12,15}`. No double LOSS or resource-limited case occurred. The condition `not(V({4,7}∪T,1)=LOSS and V({4,7}∪T,3)=LOSS)` has **nonvacuous** finite evidence here:10 cases have E3LOSS, while one has E1LOSS.

| E1 | E3 | Cases |
|---|---|---:|
| LOSS | WIN | 1 |
| DRAW | LOSS | 7 |
| DRAW | DRAW | 35 |
| DRAW | WIN | 21 |
| WIN | LOSS | 3 |
| WIN | DRAW | 14 |
| WIN | WIN | 176 |

This auxiliary remains an unproved uniform statement. The batch neither proves it nor refutes the B anchor, actual interval-root Q_N statement, or conjecture C.

The named prior control was **not** among the256 saved B tails. It was already in the earlier exhaustive B-tail domain `[9,18]`; its saved C8 value there is WIN. It was tested first, followed by the original256 B tails in their existing saved order, with no newly generated support. For `E={4,7,9,10,12,15}`:

- `V(E,1)=LOSS`, with every first pick4,7,9,10,12,15 losing.
- `V(E,3)=WIN`; first picks are `4:L,7:W,9:D,10:L,12:L,15:L`.
- `C={2,3,4,7,9,10,12,15}` has `V(C,8)=WIN`, `V(C,2)=WIN`, and `V(C.erase2,4)=DRAW`.

Thus unconditional E1NONLOSS is false, as the prior diagnostic indicated, while this control does not defeat the proposed *combined* auxiliary. Its C8 is nonloss, so it is not a B-anchor counterexample. All five named-control states and every legal first pick were independently replayed literally.

The ten E3LOSS tails are:

```
{10}; {12}; {32,255,384,595}; {52,141,159,907,987};
{18,32,34,36,52,56,62,74}; {45,80,85,90,130,140,155,185};
{65,70,148,273,400,509,554,661}; {180,320,340,360,520,560,620,740};
{29,156,394,476,619,841,894,917};
{21,112,131,132,237,581,596,629,721}.
```

E1 draws in seven and wins in three. Independent literal-score replay covers **all11 cases with either deficit losing**, both E1/E3 values and every first pick, plus the named control's three C states:25 direct state queries and195 first-pick values. No claim is made that all257 pairs were literally replayed. Every initial E pick ends the turn because each label is≥4 and deficits are1/3; both frozen recurrences use direct behind-player values and switch on equality or overshoot in descendants.

All tails remain exactly those already saved, apart from the one explicit authorized control. They have even sum; E has odd sum11+sum(T), so both effective totals are even. The unchanged ExactSlots handles at most12 E labels and actual labels through1000; no interval table or solver-limit extension was used. Saved C8 values are matched by original source ID and exact T; the fresh named-control C8 independently matches its old exhaustive-domain record.

`root_anchor_doubleloss_seeds.json`/`.txt` retain the257-row input and source hashes. `root_anchor_doubleloss_results.json` retains all outcome pairs, all source C8 values, nonvacuous literal first-move maps, and named-control context values/maps. The checkpoint records257 completed and no unprocessed rows; its remaining-seed file is empty. Exact commands/output hashes/resources are in the run JSON; the manifest verifies new artifacts and frozen/read-only sources. Older artifacts were preserved.

Compile0.612s, probe0.419s externally (internal0.015s), literal audit0.450s; total1.480s. Peak compiler RSS141,852,672 bytes, probe35,717,120 bytes, literal32,194,560 bytes. All work stayed below30s/512MiB. No support expansion or further batch followed completion.
