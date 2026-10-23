# Informal explanations

These are reading guides to the formal proofs, not additional unverified theorems. The linked Lean statements specify all hypotheses and edge cases.

## Why normalize by a deficit?

Only the score difference matters after the opening. If the acting player trails by `d` and takes `x < d`, that player keeps acting, with deficit `d-x`. If `x ≥ d`, the turn ends and the other player acts with deficit `x-d`. The outcome changes sign only in the latter case. The reference correspondence and common-score translation are proved in [Executable](../CatchUp/Executable.lean).

The first move needs separate attention: player one chooses exactly one counter. The normalized child is evaluated from player two's perspective, so its result is negated when evaluating player one's opening. Equality after a pick ends the turn.

## What does an alternative exact-sum block buy us?

Suppose all counters are at least a positive number `a`, counter `b` is present, and a separate subset `B` sums exactly to `b`. The theorem [AlternativeSumDefense.value_ne_loss](../CatchUp/AlternativeSumDefense.lean) says that if every counter is at most `b+a`, the position at deficit `b` is nonlosing.

The proof is by contradiction. A supposed loss forces a winning opening on a smaller residual support. A completed-turn argument using `B` rules out each residual opening up to `b+a`; the assumed upper bound leaves none. The block argument uses an admissible last counter and checks the preparation sum, so it respects the rule that a turn stops at the first catch. It does not assume the player can freely choose an arbitrary subset after the turn should already have ended.

The companion theorem `winning_opening_gt_bound` states the residual-opening restriction without the upper bound. This is useful when a larger interval has a short remaining tail. [ConsecutiveGuardBoundary](../CatchUp/ConsecutiveGuardBoundary.lean) applies a related defense to exclude the top six large picks.

## Why keep failed ideas?

A strategy fitting one favorable line can fail against a different reply. The certified obstruction examples rule out particular proposed generalizations, including pair-based principles and a guard-insertion principle. They help identify which hypotheses a successful invariant must retain. A loss on an irregular counter set is not a counterexample to a conjecture restricted to initial intervals.

## How does the cryptid help?

Every fixed game is finite and exactly evaluable. Searching eligible `N` in increasing order therefore gives a partial computation that halts exactly when it finds a counterexample. [Search](../CatchUp/Search.lean) proves that equivalence; [the binary machine](../cryptid/) carries it through initialization and compilation. This gives another exact representation of the open problem. A small machine by itself supplies neither a short nonhalting proof nor a solution to the game.
