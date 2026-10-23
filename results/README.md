# Results

The universal conjecture is **open**. These are results about its rules, intermediate positions, and proposed proof methods. Every formal statement is in the linked Lean file; its hypotheses matter.

A normalized position `Position ⟨R,d⟩` has remaining counters `R` and an acting player trailing by `d ≥ 0`. **Nonwinning** means that player cannot force a win. **Nonlosing** means that player can avoid losing. Neither alone establishes a draw.

## Start here

| Result | Meaning | Formal source |
| --- | --- | --- |
| Executable normalization | The executable three-outcome evaluator agrees with the reference game, including the special opening and the empty game. Adding the same amount to both scores preserves the value. | [Executable](../CatchUp/Executable.lean) |
| Strategy semantics | A proved classifier recognizes whether a fixed player can avoid loss; decisions follow the actual turn rules, rather than alternating after every pick. | [Reference](../CatchUp/Reference.lean), [Classifier](../CatchUp/Classifier.lean) |
| Pair deletion | A sufficient family of nonlosing positions implies the desired initial-game draw. This is a reduction with explicit hypotheses, not a proof that the hypotheses always hold. | [PairDeletion](../CatchUp/PairDeletion.lean) |
| Increasing turns | Certain safe turns can be reordered increasingly; this gives exact first-pair reductions and bounds on preparation length. | [Increasing](../CatchUp/Increasing.lean) |
| Pair defenses | Four separated consecutive pairs, with minimum at least four, are nonwinning at deficit two. Further five-pair, anchored, whole-turn and reserve defenses have explicitly stated restrictions. | [DeficitTwo](../CatchUp/DeficitTwo.lean), [FivePair](../CatchUp/FivePair.lean), [AnchorFive](../CatchUp/AnchorFive.lean), [NearRepair](../CatchUp/NearRepair.lean) |
| Exact-sum defense | A counter with a separate block of the same total cannot produce a loss in a near-maximum regime. This works for blocks of arbitrary size. | [AlternativeSumDefense](../CatchUp/AlternativeSumDefense.lean) |
| Interval boundary | On `{3,4} ∪ [9,N]` at deficit one, a winning pick `q ≥ 14` must satisfy `q+6 ≤ N`. Thus the top six large picks cannot win. This does not settle the remaining picks. | [ConsecutiveGuardBoundary](../CatchUp/ConsecutiveGuardBoundary.lean) |
| Upper-branch criteria | Conditional, all-reply reductions isolate the remaining deficit-one core rather than assuming it is safe. | [RootUpperEightCriterion](../CatchUp/RootUpperEightCriterion.lean) |
| Counterexample search | A specified search halts exactly when the universal conjecture is false. The binary machine implements this search. | [Search](../CatchUp/Search.lean), [cryptid](../cryptid/) |

## Certified failures of proposed strategy rules

These examples use **different remaining supports**, not the initial interval `{1,…,N}`. Each is kernel-checked; none disproves the Catch-Up conjecture.

- **Odd consecutive pairs do not guarantee a nonwinning root.** On `{3,4,57,58,65,66,77,78,81,82,97,98}`, the first player wins by opening with 4, despite even total 766. Every opposing reply is covered. [Proof](../CatchUp/OddPairRootObstruction.lean).
- **A small deficit does not itself ensure safety.** `{2,4,7,13,15,19,35,36,50,57,60,99}` at deficit one is losing; all twelve legal first picks lose. [Proof](../CatchUp/UnitGuardObstruction.lean).
- **Inserting a small guard can reverse a result.** `{4,7,13,19,36,37,50,57,60,99}` loses at deficit 14, while inserting 2 makes it winning. This also breaks a proposed rule for copying a winning move. [Proof](../CatchUp/NearDeficitGuardObstruction.lean).

Earlier failures of simple pair extension, whole-turn matching and fixed repair rules are retained in [SevenPairTest](../CatchUp/SevenPairTest.lean), [WholeTurn](../CatchUp/WholeTurn.lean), [FourOrphan](../CatchUp/FourOrphan.lean), and the other obstruction modules. Their precise failed claims are stated in those files.

## How much assurance?

These are Lean proofs, including structural arguments and finite certificates reduced in the kernel. An axiom audit checks the named headline theorems transitively against the allowed standard axioms `propext`, `Classical.choice` and `Quot.sound`. Neither the unfinished upstream conjecture nor an external solver answer is a proof premise.

See [checking instructions](../verification/), [the full module index](modules.md), [informal explanations](informal.md), and [remaining questions](open-questions.md). Computer search and independent mathematical review are distinct from kernel checking. This collection is an initial research snapshot, not a claim that all known work is covered.
