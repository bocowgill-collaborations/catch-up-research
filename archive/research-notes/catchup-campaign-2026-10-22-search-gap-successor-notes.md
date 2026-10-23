> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.GapSuccessorObstruction](../../CatchUp/GapSuccessorObstruction.lean).

# Gap-successor diagnostic and margin-3 filter

The **geometric version** of the proposed uniform closing step is false even with the retained maximality condition w>b. This is a counterexample to that stronger step; the parent position is winning, so it is not a counterexample to H or to the interval conjecture.

## Crucial scope correction

The N=13 counterexample does **not** satisfy the residual-winning-opening premise of the full dichotomy. For the exact blocks {4,9} and {5,8}, the value after opening the residual at 10 is **win** for the next mover, so 10 is a **losing** residual opening. Only {4,9} contains the globally maximal feasible member b=9; that block also fails the strategic premise. Independent literal-score replay confirms both controls.

Consequently, this diagnostic refutes only the geometric gap-closing statement written below. It does not refute the version additionally requiring an exact block B containing global b with afterOpening(S\B,w).value=loss. The full strategic-premise search and its finite surviving cases are separately recorded in `gap_full_witness_NOTES.md` and `gap_full_witness_results.json`. The original source, log and proof diagnostic remain unchanged; the scope metadata is corrected here.

## First retained-maximality counterexample

The search plans ambient N<=16, but stops at its first retained-maximality losing successor. It exhausts N=0..12, then finds the following diagnostic at N=13:

```
S = {4,5,8,9,10,11,12},  h=6,  d=13,  d+sum(S)=72 (even).
t=3 is a genuine subset-sum gap; w=d-t=10 belongs to S; d does not.
The exact-13 blocks are {4,9} and {5,8}, so maximal exact-block member b=9.
w=10>b=9.
```

The parent is a **win**. Its complete first-move outcomes are:

```
4:win, 5:win, 8:win, 9:draw, 10:loss, 11:draw, 12:draw.
```

Picking 10 continues the same player into the **losing** successor
`({4,5,8,9,11,12},3)`. Every successor first pick (4,5,8,9,11,12) loses. Its effective total is 52, preserving even parity because the transition subtracts 2w from the parent's effective total.

The first weaker diagnostic occurs at N=10:
`S={1,5,6,7,8,9}, h=4, d=10, t=3, w=7`, with maximal exact-block member `b=9` and block `{1,9}`. Its parent draws and its successor `({1,5,6,8,9},3)` loses, but w<b. It does not refute the version retaining w>b; the search continued until N=13 for that reason.

Independent literal-score replay confirms both diagnostics, every parent and successor first-move outcome, full-set maximality of b, both true gaps and exact blocks. It checks the actual continued scores `(w,d)` as well as normalized scores `(0,t)`, so no perspective switch is inserted at w<d. N=13 is the smallest ambient endpoint found in the exhaustive retained-maximality search; no least-mask claim is made. N=13 is partial because the run stops at this diagnostic; N=14..16 were not searched in that first run.

The unmodified N=16 exact table received full scalar verification of 1,114,112 labels. Complete ambient domains and both witnesses are in `gap_successor_results.json`. Through the complete N<=12 portion there are 566 candidates satisfying w>b and 324 weaker candidates, with no retained-maximality loss. The original run, compilation and literal replay sum 1.495s; solver peak RSS is 2,654,208 bytes and replay peak is 14,401,536 bytes. Each subprocess has a 30s cap.

## Separately authorized stronger margin filter

The original source, log and receipt are preserved. The new `gap_successor_margin3_probe.cpp` changes only the deficit lower bound to `d>=2h+3`, plus an explanatory source comment. It uses the same bounded N=16 exact engine and a fresh full scalar check; no larger N is introduced.

Every ambient N=0..16 completes under this stronger filter. There are 14,316 even parent states with d missing and 8,392 true-gap successor candidates:

| Maximality class | Loss | Draw | Win | Total |
|---|---:|---:|---:|---:|
| w>b | 0 | 4,662 | 25 | 4,687 |
| w<=b | 0 | 3,439 | 266 | 3,705 |

No counterexample is found in either class in this bounded range. Therefore there is no new losing witness to replay. These counts do not prove a uniform gap-closing theorem. Per-ambient counts are saved in `gap_successor_margin3_results.json`.

The margin-3 compilation and solver process sum 1.473s; the solver peak is 2,654,208 bytes. Separate command/output receipts and source manifests retain the original diagnostic and the stronger-filter pass. No portfolio test or further experiment was run.
