> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.DenseBlockEntryObstruction](../../CatchUp/DenseBlockEntryObstruction.lean), [CatchUp.Executable](../../CatchUp/Executable.lean), [CatchUp.Reference](../../CatchUp/Reference.lean), [CatchUp.CompletedTurn](../../CatchUp/CompletedTurn.lean), [CatchUp.ExactSumLossObstruction](../../CatchUp/ExactSumLossObstruction.lean).

# Dense block-entry obstruction

`CatchUp/DenseBlockEntryObstruction.lean` formally checks the supplied
N=11 configuration from `search/min_block_entry_NOTES.md`. It proves a
failure of mandatory **first-pick entry through the exact block**. It does
not refute the desired gap-closure statement F, the dense nonloss statement
H, or the original interval conjecture C. No minimality claim is made.

## Exact configuration and values

The parent support is S={4,5,6,7,8,10,11}, deficit d=9, exact block
B={4,5}, global maximal exact-block member b=5, opening w=6, and gap t=3.
The holes in [1,11] are exactly {1,2,3,9}, so h=4 and 2h+1=d<=N.
The effective total is sum(S)+d=60, hence even. Every subset of S of
sum nine is B itself; in particular every member of every exact-nine
subset is at most b. No subset of original S sums to t, and 1<=t<h.
These are proved by `arithmetic_premises`, `exact_block_unique`,
`global_exact_block_bound`, and `original_subsum_gap`.

The actual residual opening after B and w is C={7,8,10,11} at deficit
six. Its total is 36, so it is nonterminal; its exact minimax value is
LOSS. `full_branch_configuration` assembles the density, parity,
maximality, true subsum-gap, losing residual, and nonterminal premises.
It deliberately contains no assumption that the original parent loses.

The continuing state L=(S.erase 6,3) has value DRAW. Its complete legal
first-pick values, proved through the executable/value bridge, are:

| Pick | Minimax outcome for the mover at L |
| --- | --- |
| 4 | LOSS |
| 5 | LOSS |
| 7 | LOSS |
| 8 | DRAW |
| 10 | LOSS |
| 11 | LOSS |

`unique_safe_first_pick` proves the iff for every legal x, and
`no_safe_block_entry` proves there is no x in B whose first-pick outcome
avoids LOSS. Thus every controller requiring that first pick to lie in
B fails on this full branch configuration, despite the continuing state
being drawn. This does not rule out a controller that picks eight first
and subsequently uses block information.

`safe_after_eight` is the actual `CanAvoidLoss` strategy assertion for
the original mover. `every_opponent_turn_safe_after_eight` quantifies
over arbitrary legal `CompletedTurn` traces by the opponent and proves
the original mover still has a nonloss strategy at every endpoint.
The statement concerns existence of the friendly strategy against every
opponent response; it does not promise safety after arbitrary friendly
errors. Conversely, the losing block entries mean the opponent can force
loss, not that every opponent response punishes the entry.

`parent_nonloss` proves that pick six from (S,9) continues to L and
therefore the parent cannot be LOSS. The diagnostic is not an H/C
counterexample, and its source does not assume a parent-loss hypothesis.

## Additive quota versus turn legality

L contains the three adjacent pairs {4,5}, {7,8}, {10,11}.
`selector_totals` kernel-checks that selecting one counter from each pair
attains exactly every integer from 21 through 24. `balanced_selector`
proves {5,8,11} is a subset of L with total 24 and
2*24=sum(L)+3=48.

Nevertheless every counter of L is at least four, greater than its
deficit three. `every_low_turn_singleton` proves directly from the
constructors of `CompletedTurn` that every legal whole turn consists of
one pick. Every remaining counter is at most eleven, so
`no_quota_completed_turn` proves no such turn has total 24.
The balanced reserve is arithmetically attainable yet cannot itself be
a legal whole turn, already inside the full dense branch domain.
Additive selector information therefore needs a legality-aware strategy
argument; existence of the balanced selector alone does not supply it.

## Existing APIs and provenance

The finite configuration came from the retained search notes above.
This module imports no search output and uses no external value table.
All finite arithmetic and value computations are `decide +kernel`.
The values are connected to the existing minimax semantics by
`Position.eval_eq_value` (`Executable.lean:26`), and move outcomes use
`Position.moveOutcome` (`Reference.lean:502`). The strategy assertion
uses `can_avoid_loss_iff_value` (`Reference.lean:517`). Universal
opponent-turn transport reuses
`CompletedTurn.safe_endpoint_of_can_avoid_loss` (`CompletedTurn.lean:567`).
Parent nonloss reuses the existing private
`Position.loss_after_continuing_pick` helper
(`ExactSumLossObstruction.lean:48`), whose proof was preserved from the
old bb10b824 source. No new solver semantics, game framework, or custom
axiom was introduced.

## Verification

Both commands completed within their explicit 120-second subprocess
timeouts at default Lean budgets:

```
lake --wfail build CatchUp.DenseBlockEntryObstruction
lake env lean campaign_2026_10_22/frontier/block-entry/audit.lean
```

The warning-strict build took 6.633 seconds wall time (4.3 seconds for
the module); the complete public-theorem axiom audit took 4.221 seconds.
The Darwin child-process maximum-RSS measurements were respectively
5,692,719,104 and 5,280,694,272 bytes, retained in `build-stats.json`
and `audit-stats.json`. All 20 public theorems have only `propext`,
`Classical.choice`, and `Quot.sound` as transitive axioms.

The source has 196 lines, 8,971 bytes, 20 theorems, and six definitions.
Its SHA-256 is
`f8719ba57b8750a214f5e838c4c5cdf11e7fbc986e11aab1cf5c45e7b3569249`.
`source-check.json` records these counts, the forbidden-pattern check,
and unchanged hashes for all nine prior finished frontier modules.
`build.log`, `axioms.log`, and `audit.lean` retain the verification.
There are no unfinished obligations in this diagnostic. General F,
residuals of cardinality at least three, H, and C remain open.
