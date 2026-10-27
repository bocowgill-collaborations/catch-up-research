# What the failed ideas teach us

These are certified failures of proposed auxiliary statements. No entry below is a counterexample to the initial-interval draw conjecture. A failed candidate is useful when it rules out a precise shortcut and identifies the obligation a stronger idea must address.

The [first-pair atlas](first-pair-atlas.md) now provides maintained Lean ports for
four previously archived groups. Their [verification record](../verification/atlas-ports.md)
does not upgrade other historical claims.

Do not drop hypotheses from positive results either: the recovered
[maximum-companion theorem](reply-maximum-companion.md) requires every smaller
pair-deletion position to be nonempty and catchable. It does not establish the
unrestricted or shifted-graph claims mentioned in historical CU-L011. No new
counterexample to those broader claims is asserted by this recovery.

Earlier failures with different assurance levels are indexed in [CU-L016–CU-L020 and CU-L022–CU-L039](legacy-findings.md). They cover statewise four-counter lifts, adjacent-hole copying, debt policies, shifted cycles, prepaid reserves and upper-only exact-sum descent. Follow each entry's evidence label: some have current proofs, others only archived Lean sources or historical computations. In particular, the 921 failures of the tested six-old-counter cutoff do not exclude every larger fixed cutoff.

| Proposed shortcut | Diagnostic / what survives | Checked source |
| --- | --- | --- |
| A smallest orphan supplies a nonwinning adjacent-pair reserve | For every a≥4, `{a,a+2,a+3}` wins at deficit a−1. | [AdjacentPairGeometryObstruction](../CatchUp/AdjacentPairGeometryObstruction.lean) |
| Pick the smallest upper counter from three consecutive pairs | For a≥6, picking a+1 from `([a,a+5],1)` loses to reply a+5. This does not determine the parent value. | [AdjacentPairGeometryObstruction](../CatchUp/AdjacentPairGeometryObstruction.lean) |
| Copy common counters in the adjacent-hole exchange | U draws and V wins, but every nonlosing V move copies to a losing U move. First repair requires U:2 and V:5. This is not a counterexample to V-win implying U-nonloss. | [AdjacentHoleExchangeObstruction](../CatchUp/AdjacentHoleExchangeObstruction.lean) |
| Use only minimum three and parity in a first-pair three-reserve transfer | A sparse deficit-one loss has a winning deficit-two shadow. The separate legal-prefix copy witness starts with a drawing shadow root. | [FirstPairDescentObstruction](../CatchUp/FirstPairDescentObstruction.lean) |
| Exclude shifted cycles using their intact span or maximum companions | Legal two-cycles exist, slides can fail, and intact `{3,…,7}` has no second reply at its maximum. This does not refute the conditional tied-position companion. | [ShiftedReplyCycle](../CatchUp/ShiftedReplyCycle.lean) |
| Initialize the specified prepaid reserve envelope after any first-pair pick | For N≥7 the envelope holds exactly at N=7, opening 3. Other invariants and eventual entry are not excluded. | [TurnReserveInitialization](../CatchUp/TurnReserveInitialization.lean) |
| Pair count, total, extrema, deficit, parity and selector sums determine value | At deficit 4, adjacent pairs starting at `{6,10,20,40}` win; starts `{6,12,18,40}` lose. Both have eight counters, total 156, minimum 6 and maximum 41, with the same selector interval. | [AdviceFeatureCollision](../CatchUp/AdviceFeatureCollision.lean) |
| Extend a successful small paired defense by adding two pairs | The lifted defense fails against a retained opponent reply. This rejects that lift, not every possible strategy on larger supports. | [SevenPairTest](../CatchUp/SevenPairTest.lean) |
| An immediate balanced turn supplies a universal interval defense | For every N>=7 and every opening, P2 cannot take its entire draw quota in its first turn. A successful defense must carry the task across turns. | [WholeTurn](../CatchUp/WholeTurn.lean) |
| The four-pair orphan reserve stays nonwinning when two pairs are added | `{7,10,11,18,19,20,21,40,41}` at deficit 7 wins via 41. The later adaptive repair fixes the reached decision, not this false family. | [FourOrphan](../CatchUp/FourOrphan.lean), [NearRepair](../CatchUp/NearRepair.lean) |
| Enter a maximal exact-sum block with its own counter first | A certified dense drawn state has no safe first pick in the block, but has a safe pick outside it. An arithmetic selector need not supply the strategic entrance. | [DenseBlockEntryObstruction](../CatchUp/DenseBlockEntryObstruction.lean) |
| A proposed gap-successor move preserves safety | The successor can lose even when its dense even ancestor wins. Do not discard the actual parent-value hypotheses. | [GapSuccessorObstruction](../CatchUp/GapSuccessorObstruction.lean) |
| Remove density assumptions from a gap argument | A concrete example and an unbounded sparse family break the unrestricted implication. They do not break the version retaining density. | [FullGapDensityObstruction](../CatchUp/FullGapDensityObstruction.lean), [FullGapDensityFamily](../CatchUp/FullGapDensityFamily.lean) |
| A reserve-containing multi-pick turn repairs the equality case | Under the theorem's losing-shadow hypotheses, every such first repair turn loses. A useful repair must avoid that reserve during this turn. | [EqualityReserveObstruction](../CatchUp/EqualityReserveObstruction.lean) |
| A counter just below the deficit, or a minimum of two, guarantees nonloss | Explicit sparse positions lose despite these features. Inserting a small counter can even reverse value. | [NearDeficitGuardObstruction](../CatchUp/NearDeficitGuardObstruction.lean), [UnitGuardObstruction](../CatchUp/UnitGuardObstruction.lean) |
| An even number of odd-start adjacent pairs guarantees a nonwinning initial root | The six-pair support in the source is a forced P1 win via 4. It is not an interval `{1,…,N}`. | [OddPairRootObstruction](../CatchUp/OddPairRootObstruction.lean) |
| Always answer with the next available integer at the actual interval endpoint | A drawn endpoint reached at N=15 has a losing immediate-successor reply. Other replies are retained and certified. | [IntervalSuccessorReplyObstruction](../CatchUp/IntervalSuccessorReplyObstruction.lean) |
| Two anchors cannot lose at both deficits one and three | With tail `{18,33,35,36,52,56,62,74,100}`, adding anchors `{4,7}` loses at both deficits. Its high shadow wins, so this does not refute the conditional route retaining high-shadow loss. | [TwoAnchorDoubleLossObstruction](../CatchUp/TwoAnchorDoubleLossObstruction.lean) |
| Alternating odd/even tail ranks and a balanced allocation guarantee nonloss | `{4,7,19,36,37,50,57,60,99}` loses at deficit 1 despite those properties; every first pick is covered. | [AlternatingTailObstruction](../CatchUp/AlternatingTailObstruction.lean) |

The [five-counter trap](endpoint-trap-atlas.md) is a different kind of diagnostic:
for every k≥2, opening 3 in I_(4k) admits a legal history reaching a tied top-five
win for player one. This proves neither forced entry nor failure of every
block-clearing defense.

The [module guide](modules.md) includes additional diagnosed exceptions and the successful adaptive repairs. “Repair” refers to a game strategy unless the text explicitly discusses a machine routine.

The [experimental findings](experimental-findings.md) also explain failed fixed entrances, vacuous tests and unprocessed cases. The [research notebook](../archive/research-notes/) retains the full arguments and the sequence of failed and successful repairs; use the [current route guide](research-routes.md) for what is still open.

One can reproduce the first diagnostic computationally without Lean:

```sh
python3 computation/explore.py --remaining 6 7 10 11 20 21 40 41 --deficit 4
python3 computation/explore.py --remaining 6 7 12 13 18 19 40 41 --deficit 4
```

Those Python runs are independent experiments. The linked Lean proofs provide the stronger assurance for the stated instances.
