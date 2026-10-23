> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.AlternatingTailObstruction](../../CatchUp/AlternatingTailObstruction.lean).

# Alternating-tail diagnostic: kernel-certified loss

Status: complete; independent parent review PASS. Frozen source `CatchUp/AlternatingTailObstruction.lean` SHA-256
`4142052a77a1377c80ce56c7101c01e5dcdab7496227272793ceedd78e3cb6d7`.

## Result

Take `T = {19,36,37,50,57,60,99}` and `E={4,7}∪T`.
The kernel proves `V(E,1)=LOSS`, and **every one of the nine legal first
picks has outcome LOSS** (`core_one_loss`, `every_pick_loses`).

The tail is strictly sorted, starts above nine, alternates odd/even/odd/even/
odd/even/odd by index, and has even sum 358. Core mass is 369. These purely
arithmetic conditions are encoded independently of game value in
`AlternatingTail`; `not_uniform_alternating_tail_nonloss` refutes the proposed
unconditional nonloss conclusion for that entire arithmetic class.

Moreover an actual balanced allocation exists: `{36,50,99} ⊆ E` has sum
185, hence twice its sum is `sum E + 1 = 370` (`balanced_allocation`).
Thus even adding existence of a balanced allocation to this arithmetic
geometry cannot justify a strategic nonloss conclusion. No legality of that
allocation as a single turn is asserted.

The same finite witness has precise adjacent-pair deletion geometry inside
the eligible ambient interval `[9,99]`: the omitted labels are exactly
`[9,18]∪[20,35]∪[38,49]∪[51,56]∪[58,59]∪[61,98]`. There are 84 omitted labels,
decomposed into 42 pairwise-disjoint adjacent pairs. Both the even pair count
and `Even(99*100/2)` are kernel proved (`six_gap_geometry`,
`adjacent_pair_deletion_geometry`).

This refutes nonloss inferred from alternating tail geometry alone. It does
not evaluate the undeleted ambient interval, establish failure of an
outcome-preservation theorem under a true strategic premise, prove a legal
deletion trace, give a counterexample to the original Catch-Up conjecture, or
settle the actual interval anchor-eight shadow. Optional deficit-three and
anchor-eight contexts were literal computational draws; they are not
certified in this module or used in any proof.

## Proof and trust boundary

The fixed witness was discovered and compressed by the separate bounded
search workstream. The frozen JSON certificate has 19 exact-state nodes,
18 edges and nine leaves, each with seven counters. It serializes to 10,082
bytes (SHA-256
`c27d41a4d2681e7b9d09e1f4ee4362f30a23f389490e9dea1f0553eb7cbdd892`).
This is not a new support search and no minimality is claimed.

The untrusted renderer creates shared Lean value lemmas. A WIN node supplies
one legal winning pick; a LOSS node covers every legal pick. Explicit
afterPick equalities and the existing moveOutcome definition account for
perspective swaps. Five edges retain the same player; they are not treated
as alternating turns. The root's nine edges all swap, and each resulting
eight-counter WIN node uses one justified reply. Seven-counter leaves use
`Position.eval_eq_value` and `decide +kernel`, not native evaluation. Thus
external answers are not axioms. Existing `WinningOpening` and `DeficitTwo`
provide the proved all-moves LOSS and one-move WIN interfaces. The original
unfinished conjecture is not used.

The producer rejects missing LOSS branches, illegal WIN witnesses, and
circular child references in deliberate negative controls. Lean also rejects
the deliberately corrupted root claim WIN. All eight public transitive
axiom audits contain only `[propext, Classical.choice, Quot.sound]`.

## Checks and cost

From `research/catchup`:

```sh
python3 campaign_2026_10_22/frontier/alternating-tail-obstruction/generate.py
python3 campaign_2026_10_22/frontier/alternating-tail-obstruction/verify.py --fresh
```

The full source passed LeanProbe without sorry. Production checks use
default Lean budgets and a 120-second wall cap per command:

| Check | Seconds | Result |
|---|---:|---|
| Fresh source with warnings as errors | 13.896 | PASS |
| Strict Lake build | 14.723 | PASS |
| Eight public axiom audits and edge examples | 4.549 | PASS |
| Deliberately wrong root outcome | 3.809 | rejected as required |

Source size includes all supporting local mathematics and the shared DAG:
204 lines, 9,995 bytes. Generation took 0.0014 seconds and 12,304,384 bytes
peak RSS; the maximum recorded cumulative child peak RSS for Lean checking
was 7,005,863,936 bytes. Hardware report: macOS 26.6.2 arm64. Lean 4.27.0,
Mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900`. The initial attempt needed
an explicit unfold of the arithmetic predicate for decidability; no game
hypothesis was changed. Exact source/olean hashes, logs, generation costs,
and independently audited producer data are linked in `verification.json`
and `generation.json`. No Turing-machine change is involved.

## Remaining obligation

An actual interval defense needs constraints stronger than alternating
parity/even mass or arbitrary even-count adjacent-pair deletion geometry.
Retain the genuine parent-loss or strategic reentry premise, or exploit
unbroken interval structure; the present sparse witness does not refute
either route. No new numerical expansion is justified by this diagnostic.

Final arithmetic strengthening: balanced_allocation added without changing the
DAG/data. All bounded production checks were refreshed; prior receipts remain
in `before-balanced-allocation/`. Final olean: 253,416 bytes, SHA-256
`ac6c7f362da0108114e5f3e993b8e07bd0a18e6a3b6e38a2bc586451aae9a499`.
