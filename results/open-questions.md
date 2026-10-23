# Open questions

The main target remains the draw conjecture for every eligible initial interval, including `N=0`. A draw needs both players' nonlosing guarantees.

The current proof campaign studies the reductions in [PairDeletion](../CatchUp/PairDeletion.lean) and [RootUpperEightCriterion](../CatchUp/RootUpperEightCriterion.lean). A remaining interval core is `{4,7} ∪ [9,N]` at deficit one, under the original losing-shadow hypothesis. Another branch involves `{3,4} ∪ [9,N]` at deficit one; excluding the top six large picks leaves other picks unresolved. The existing bounds do not imply infinite descent: the residual support differs from the original support.

The highest-value next mathematical step is to identify a defensive condition that survives every legal opponent turn on these interval cores. Alternative subsets with a prescribed sum are promising ingredients, but their existence alone has not been proved to preserve the required game property. Retain the losing-parent hypotheses and distinguish existence of an exact sum from existence of a legal completed turn.

Other contributions could independently audit external finite computations, compress the existing certified obstruction proofs, or complete the smaller machine's remaining simulation proof. Claims about a least counterexample, proof-size lower bounds, or a minimum-state machine require separate evidence.
