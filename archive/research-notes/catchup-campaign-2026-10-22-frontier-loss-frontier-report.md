> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.DenseLossFrontier](../../CatchUp/DenseLossFrontier.lean), [CatchUp.ExactSumLossObstruction](../../CatchUp/ExactSumLossObstruction.lean), [CatchUp.WinningOpening](../../CatchUp/WinningOpening.lean).

# The remaining frontier of an actual dense loss

`CatchUp/DenseLossFrontier.lean` connects the finished three-residual
closure and the uniform gap mass theorem to a hypothetical losing dense
parent. It retains the strategic witness that the older exported lower
alternative discarded. All earlier sources remain frozen.

## Exact open alternatives

The public theorem `loss_frontier` assumes arbitrary N,d,S with:

* S contained in [1,N]; h is the **actual** number of missing counters.
* 2h+1<=d<=N and sum(S)+d even.
* The normalized parent (S,d) has value LOSS.

It proves one of these alternatives.

1. **Upper descent:** an exact-d block B is nonempty, contained in S,
   and has card(B)<=h+1. There is w in S minus B with d<w and actual
   value LOSS at `afterOpening (S minus B) w`. This is precisely the
   existing upper alternative, with the actual hole budget.
2. **Lower obstruction:** the selected exact block B, its globally
   maximal feasible exact-block member b, and the same opening w are
   retained. They satisfy d-h<=b<w<d, b in B, card(B)<=h+1, and every
   member of every exact-d subset of original S is at most b. The target
   t=d-w satisfies 1<=t<h and cannot be represented by **any** subset
   of original S. The actual residual opening
   `afterOpening (S minus B) w` is LOSS, while the continuing child
   (S.erase w,t) is also LOSS. In particular w is an actual winning
   opening of the tied residual game: `CatchUp.value (S minus B)=WIN`.

For the lower alternative, let C=(S minus B).erase w and k=card(B).
The theorem additionally proves

```
w <= sum(C),       card(C) >= 4,
k*(k-1) <= 2*card(C)+4.
```

Thus every hypothetical H loss either follows the still-open upper
descent, or has a nonterminal lower losing residual of at least four
counters with the all-size exact-block mass restriction. No upper or
lower successor is asserted to preserve density. This necessary
obstruction theorem does not prove H, F, or original interval C, and it
does not start a four-counter enumeration.

## Witness preservation and proof

`LowerGeometry` (`DenseLossFrontier.lean:24`) is an arithmetic witness
record containing B,b,w, support/exactness, global maximality, the near
bound, the block-card budget, and the true small subsum gap. It contains
no game-value field. Both LOSS assertions and the residual WIN assertion
are explicit conclusions of `loss_frontier`, outside the record. This
is a necessary witness extracted from hypothetical loss, not a strategic
invariant or a sufficient condition for loss.

The existing `DenseLossSubsumGap.loss_dichotomy` conclusion exposes only
t, its gap, and the losing child in its lower branch. Those outputs do
not recover the selected B,b,w or the losing residual opening. The new
private `selected_loss_dichotomy` therefore retains the same local
filter/max selection and gap argument, reusing the existing seed and
exact-sum game lemmas. It does not edit or replace the frozen theorem.

The filter ranges over members of **all** exact-d subsets of original S.
Its maximum b lies in a selected exact block B. The existing large-member
seed supplies b>=d-h; positivity bounds card(B)<=h+1. The exact-sum
obstruction provides w>b and actual residual-opening LOSS. If w>d the
upper alternative follows. Otherwise global maximality excludes w=d,
so w<d. If a subset represented t=d-w, adjoining w to it would form an
exact-d block containing w>b, a contradiction. Parent LOSS forces the
strictly continuing pick w to have a losing child. These steps preserve
the same B,b,w rather than reselecting an unrelated witness.

For this lower branch, a terminal residual would contradict the finished
uniform terminal-gap nonloss theorem against the retained child LOSS.
A residual of cardinality at most three would similarly contradict
`DenseThreeResidual.small_residual_successor_nonloss`. Finally,
`DenseGapMassGeneral.block_card_bound` supplies the all-size inequality
directly from the retained arithmetic hypotheses, without any outcome,
parity, or finite-cardinality premise of its own.

## Existing APIs

* `DenseLossSubsumGap.exists_large_exact_block_member`, line 21, gives
  the near-deficit exact-block seed; its loss dichotomy is at line 42.
* `Position.exists_winning_opening_gt_max_of_loss_of_exact_sum`,
  `ExactSumLossObstruction.lean:119`, supplies the same actual losing
  residual opening beyond the chosen block maximum.
* The existing private `Position.loss_after_continuing_pick`,
  `ExactSumLossObstruction.lean:48`, preserves LOSS after w<d.
* `value_eq_win_iff_exists_winning_opening`, `WinningOpening.lean:137`,
  converts that actual opening witness to the tied residual WIN.
* `DenseTerminalNonloss.terminal_gap_successor_nonloss`, line 66,
  excludes terminal lower residuals.
* `DenseThreeResidual.small_residual_successor_nonloss`, line 420,
  excludes lower residual cardinality at most three.
* `DenseGapMassGeneral.block_card_bound`, line 14, gives
  k*(k-1)<=2*card(C)+4 for arbitrary residual size.

## Verification

The source contains 175 lines, 8,356 bytes, one public theorem, one
private witness-preservation theorem, and one arithmetic witness record.
The full headline declaration passed LeanProbe in 0.507 seconds after
imports. The warning-strict production build passed in 7.212 seconds
wall time (4.0 seconds for the module), at default Lean budgets and
within an explicit 120-second subprocess limit. Darwin child-process
maximum RSS was 5,496,815,616 bytes.

The public theorem and witness-type transitive axiom audits both passed
in 3.891 seconds, with maximum RSS 5,295,505,408 bytes. Both depend only
on `propext`, `Classical.choice`, and `Quot.sound`.

`build.log`, `axioms.log`, their statistics JSON, and `audit.lean` retain
the checks. `source-check.json` records source metrics, the forbidden
pattern check, and thirteen unchanged dependency/source hashes. The
source SHA-256 is
`d8bfa0016701f71a39562caf1695f09b473fd7b8f155b5905cc876566d9e0037`.
There is no new game computation, external solver premise, custom
axiom, native proof evaluation, `sorry`, or raised budget. The remaining
mathematical obligations are exactly the upper alternative and the
lower obstruction beyond the proved three-counter closure.
