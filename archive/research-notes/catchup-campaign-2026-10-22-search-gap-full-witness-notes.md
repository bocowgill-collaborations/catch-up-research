> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current results guide](../../results/README.md).

# Gap closing with the full strategic premise retained

The earlier N=13 geometric counterexample does **not** refute the full strategic-witness repair. Its proposed w=10 loses as an opening of either exact-block residual. The new test retains the missing winning-opening condition and finds no losing successor through ambient N=16.

## Exact predicate and enumeration

For every S⊆[1,N], actual holes h, 2h+1<=d<=N, even d+sum(S), and d∉S, the test considers every true gap 1<=t<h with w=d−t∈S. It computes the global maximum b among all counters occurring in any exact-d block. It retains w>b and enumerates **every** exact-d block B⊆S with max(B)=b. The full strategic condition is

```
afterOpening(S\B,w).value = loss.
```

Thus w really is a strictly winning opening of the tied residual. The tested closing conclusion is that the original same-player successor `(S.erase w,t)` is nonlosing. No assumption is made that parent nonloss alone implies every continuation is safe.

The frozen N=16 table passes a full scalar check of 1,114,112 labels. All ambient N=0..16 complete. There are 33,842 even parents with d missing, 13,549 geometric w>b cases, and 14,223 maximal-block tests. Exactly 95 blocks satisfy the strategic condition, across 92 distinct gap cases:

| Margin d−2h | Qualifying blocks | Distinct gap cases | Successor loss | Draw | Win |
|---|---:|---:|---:|---:|---:|
| 1 | 74 | 71 | 0 | 57 | 14 |
| 2 | 18 | 18 | 0 | 14 | 4 |
| At least 3 | 3 | 3 | 0 | 3 | 0 |

Outcome counts use distinct gap cases; multiple qualifying blocks can certify the same case. Every qualifying block is retained in `gap_full_witness_results.json`. The finite pass does not prove a uniform closing lemma or H.

## Strategic rejection control and independent replay

For the old geometric diagnostic `S={4,5,8,9,10,11,12}, d=13, w=10`, the exact blocks are {4,9} and {5,8}. Both post-opening values at w=10 are **win**, so the opening outcome is **loss**. The globally maximal feasible member is 9, and the only block containing it is {4,9}; it fails the strategic condition. The old losing continuation remains a valid geometric counterexample, with its narrower scope now explicit in the old notes/results.

An independent exact-subset enumeration verifies all 95 blocks, their global maximality, and every true-gap hypothesis. Literal-score replay verifies the N=13 rejection controls and the first full strategic witness from each margin class:

- N=5, h=2, d=5, t=1, w=4, b=3, B={2,3}: parent draw, winning residual opening, successor draw.
- N=6, h=2, d=6, t=1, w=5, b=4, B={2,4}: parent draw, winning residual opening, successor draw.
- N=11, h=4, d=11, t=1, w=10, b=9, B={2,9}: parent draw, winning residual opening, successor draw.

For each representative it checks every parent/successor first move, the unique strictly winning residual opening, the post-opening loss, and both actual-score and normalized forms of the same-player continuation. There is no new counterexample requiring a loss replay.

The C++ process took 0.399s and 2,670,592 bytes peak RSS. Independent replay took 0.038s and 14,860,288 bytes peak RSS. Compilation and both jobs sum 1.662s, each with a 30s cap. `gap_full_witness_run.json` records commands, hashes and exit codes; `gap_full_witness_manifest.json` pins the completed evidence and the unmodified solver. No larger N, blind table expansion, or portfolio test was run.
