# What the failed ideas teach us

These are certified failures of proposed auxiliary statements. No entry below is a counterexample to the initial-interval draw conjecture. A failed candidate is useful when it rules out a precise shortcut and identifies the obligation a stronger idea must address.

| Proposed shortcut | Diagnostic / what survives | Checked source |
| --- | --- | --- |
| Pair count, total, extrema, deficit, parity and selector sums determine value | At deficit 4, adjacent pairs starting at `{6,10,20,40}` win; starts `{6,12,18,40}` lose. Both have eight counters, total 156, minimum 6 and maximum 41, with the same selector interval. | [AdviceFeatureCollision](../CatchUp/AdviceFeatureCollision.lean) |
| Extend a successful small paired defense by adding two pairs | The lifted defense fails against a retained opponent reply. This rejects that lift, not every possible strategy on larger supports. | [SevenPairTest](../CatchUp/SevenPairTest.lean) |
| Enter a maximal exact-sum block with its own counter first | A certified dense drawn state has no safe first pick in the block, but has a safe pick outside it. An arithmetic selector need not supply the strategic entrance. | [DenseBlockEntryObstruction](../CatchUp/DenseBlockEntryObstruction.lean) |
| A proposed gap-successor move preserves safety | The successor can lose even when its dense even ancestor wins. Do not discard the actual parent-value hypotheses. | [GapSuccessorObstruction](../CatchUp/GapSuccessorObstruction.lean) |
| Remove density assumptions from a gap argument | A concrete example and an unbounded sparse family break the unrestricted implication. They do not break the version retaining density. | [FullGapDensityObstruction](../CatchUp/FullGapDensityObstruction.lean), [FullGapDensityFamily](../CatchUp/FullGapDensityFamily.lean) |
| A reserve-containing multi-pick turn repairs the equality case | Under the theorem's losing-shadow hypotheses, every such first repair turn loses. A useful repair must avoid that reserve during this turn. | [EqualityReserveObstruction](../CatchUp/EqualityReserveObstruction.lean) |
| A counter just below the deficit, or a minimum of two, guarantees nonloss | Explicit sparse positions lose despite these features. Inserting a small counter can even reverse value. | [NearDeficitGuardObstruction](../CatchUp/NearDeficitGuardObstruction.lean), [UnitGuardObstruction](../CatchUp/UnitGuardObstruction.lean) |
| An even number of odd-start adjacent pairs guarantees a nonwinning initial root | The six-pair support in the source is a forced P1 win via 4. It is not an interval `{1,…,N}`. | [OddPairRootObstruction](../CatchUp/OddPairRootObstruction.lean) |
| Always answer with the next available integer at the actual interval endpoint | A drawn endpoint reached at N=15 has a losing immediate-successor reply. Other replies are retained and certified. | [IntervalSuccessorReplyObstruction](../CatchUp/IntervalSuccessorReplyObstruction.lean) |

The [module guide](modules.md) includes additional diagnosed exceptions and the successful adaptive repairs. “Repair” refers to a game strategy unless the text explicitly discusses a machine routine.

One can reproduce the first diagnostic computationally without Lean:

```sh
python3 computation/explore.py --remaining 6 7 10 11 20 21 40 41 --deficit 4
python3 computation/explore.py --remaining 6 7 12 13 18 19 40 41 --deficit 4
```

Those Python runs are independent experiments. The linked Lean proofs provide the stronger assurance for the stated instances.
