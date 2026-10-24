> **Historical research handoff.** Plan and reported knowledge at the time; no new theorem is asserted by this export. Consult the [finding ledger](../../../results/legacy-findings.md). The N≤38 attribution is personal communication, not a public certificate.

The revised plan should begin with Step 10 and conceptual Commit 3. Steps 1–9 have already delivered most of the old Commits 1–2, including a normalization theorem stronger than the originally proposed special case.

One important fact changes the roadmap: the naive lift works for most draw states but not all—120/124 at \(N=7\) and 332/340 at \(N=8\). That is encouraging, but it confirms we need a phased, strategy-specific relation rather than the unrestricted equation
\[
\operatorname{Position.value}(p.\mathrm{addFourCounters}\ N)=\operatorname{Position.value}(p).
\]

I would use the following remaining commits.

## Commit 3 — `refactor(CatchUp): expose post-opening evaluation`

This finishes the one genuinely missing interface from the old normalization commit.

10. Prove the top-level unfolding theorem for a nonempty set \(S\):

   ```lean
   theorem value_eq_best_after_opening
       (hS : S.Nonempty) :
       value S =
         .best (S.attach.toList.map fun ⟨a, _⟩ =>
           (afterOpening S a).value.neg)
   ```

   The negation is necessary because `afterOpening S a` is evaluated from player 2’s perspective, while `value S` reports player 1’s outcome.

11. Derive the specialization for `Finset.Icc 1 N`, with the required nonemptiness hypothesis such as \(1\le N\).

12. Add small regression tests for \(N=1\) and \(N=4\), checking the opening decomposition against the original evaluator.

13. Run the targeted and full `lake --wfail build`, then commit.

## Commit 4 — `feat(CatchUp): formalize one-sided non-losing play`

This gives the strategy-transfer theorem an exact meaning.

14. Define an absolute post-opening state:

   ```lean
   structure GamePosition extends Position where
     toMove : Player
   ```

   `Position` still supplies the deficit-based game state; `toMove` records which actual player currently owns that perspective.

15. Define legal moves and `GamePosition.afterPick`. Prove that:

   - the remaining set becomes `erase x`;
   - `toMove` stays fixed when \(x<d\);
   - `toMove` changes to `.other` when \(d\le x\);
   - the remaining-card measure strictly decreases for a legal move.

16. Define terminal states and their fixed-player interpretation. A positive-deficit terminal state is a loss for `toMove`; a zero-deficit empty state is a draw.

17. Define `CanAvoidLoss player p` by recursion on `p.remaining.card`:

   - at `player`’s node, some legal child must be safe;
   - at the opponent’s node, every legal child must be safe;
   - terminal safety is determined directly.

18. Prove clean unfolding lemmas for the terminal, friendly, and adversarial cases. Later simulation proofs should use these rather than unfold the recursive definition manually.

19. Prove the central semantic correspondence:

   ```lean
   theorem canAvoidLoss_iff_value :
       CanAvoidLoss player p ↔
         if p.toMove = player then
           p.toPosition.value ≠ .loss
         else
           p.toPosition.value ≠ .win
   ```

   This will require helper lemmas describing when `Outcome.best` is not `.loss` or not `.win`.

20. Define `GamePosition.afterOpening` with `toMove := .p2`, together with a predicate identifying legal post-opening roots. Prove that \(a\in\{1,\ldots,N\}\) gives such a root. A full general-purpose reachability closure should be added only if the discovered relation needs it.

## Commit 5 — `feat(CatchUp): trace adversarial four-counter strategies`

This is research tooling, not yet a mathematical claim.

21. Extend the exact solver so it can analyze safety for a fixed player, including whether the fixed player or the opponent is currently moving.

22. Extract the complete non-losing strategy DAG:

   - retain every safe candidate move at friendly nodes for pattern discovery;
   - retain every legal edge at opponent nodes;
   - distinguish turn-preserving and turn-switching picks.

23. Pair the DAGs for \(N\) and \(N+4\). For every paired transition, record:

   - the remaining top-four mask;
   - both deficits;
   - both players to move;
   - whether an old counter or a new counter was consumed;
   - whether the small state advanced or temporarily stayed fixed.

24. Test candidate opening families in order:

   - fixed \(a=1\);
   - bounded \(a\in\{1,2,3\}\);
   - another simple uniform family only if those fail.

25. Make output deterministic and independently check the solver against the existing reference evaluator on the small frontier.

26. Use several pairs for discovery and at least one untouched pair for validation. Do not merely inspect optimal principal variations; traverse the complete adversarial closure.

27. Record the smallest plausible phase table and its failures. Commit the reproducible tooling even if no acceptable relation has yet emerged.

## Commit 6 — `feat(CatchUp): define four-counter simulation phases`

This remains the main research gate. Do not manufacture this commit until the data supports a small uniform relation.

28. Infer the smallest phase system explaining the complete strategy DAGs. Each phase should have a human-readable interpretation involving:

   - a subset of \(\{N+1,\ldots,N+4\}\);
   - player alignment;
   - an affine deficit relationship;
   - whether the small game advances or stutters.

29. Require that the phase count be bounded independently of \(N\), contain no numerical lookup table, and handle every opponent edge in the selected reachable family.

30. Validate the proposed phases on the held-out pair. If this fails, narrow the theorem honestly—for example, to a bounded-deficit endgame family—before formalizing anything.

31. Define the resulting finite `FourPhase` type and relation:

   ```lean
   def FourLift
       (N : ℕ) (owner : Player)
       (small large : GamePosition) : Prop := ...
   ```

32. Prove its structural invariants:

   - old and new counters are disjoint;
   - the top mask identifies the phase;
   - old-counter membership is preserved;
   - deficits and player identities satisfy the phase equations.

33. Prove that the selected post-opening family enters the initial phase uniformly for every eligible \(N\), not merely for tested values.

34. Define the phase-progress information needed for stuttering. Prefer the decreasing large-game card measure; add a lexicographic phase rank only if discovery shows that bookkeeping transitions can occur without consuming a counter.

35. Add small sanity checks and run the full build.

## Commit 7 — `feat(CatchUp): prove generic non-loss transfer`

The abstraction should now be shaped by the discovered relation, avoiding premature overengineering.

36. Define a minimal `StrategySimulation owner rel` interface.

37. Add its terminal obligation: a related safe small terminal state must not correspond to an unsafe large terminal state.

38. Add its friendly-node obligation: a safe small strategy move must have an implementable large move leading either to a related small child or to a legitimate stuttering phase.

39. Add its adversarial-node obligation: every legal large opponent move must be matched by an allowed small transition or stuttering transition.

40. State the progress condition. Each recursive large-game call must strictly decrease its remaining-card measure, with a secondary phase rank only if required.

41. Prove by well-founded induction:

   ```lean
   theorem CanAvoidLoss.lift
       (hsim : StrategySimulation owner rel)
       (hrel : rel small large)
       (hsmall : CanAvoidLoss owner small) :
       CanAvoidLoss owner large
   ```

42. Validate the abstraction using identity simulation before attempting the four-counter instance.

## Commit 8 — `feat(CatchUp): verify four-counter simulation`

This is the concrete mathematical core.

43. Prove the top-block arithmetic and all phase inequalities, including

   \[
   (N+1)+(N+4)=(N+2)+(N+3)=2N+5.
   \]

44. Prove terminal compatibility, especially the cannot-catch-up condition involving the total remaining sum.

45. For every friendly phase, prove that its prescribed or matched large move is present, legal, and lands in the asserted next phase.

46. At every adversarial phase, handle all old moves \(x\le N\).

47. Separately handle each remaining top-four move. Every possible opponent choice must be covered.

48. Prove strict progress for all matched and stuttering cases.

49. Assemble these local results into:

   ```lean
   theorem fourLift_strategySimulation :
       StrategySimulation owner (FourLift N owner)
   ```

50. Remove unreachable or redundant phases and rerun the proof. The comprehensibility of the final finite-state protocol is part of the result.

## Commit 9 — `feat(CatchUp): transfer non-loss across four counters`

This commit completes the core stated goal.

51. Prove that the chosen legal post-opening roots satisfy `FourLift`.

52. Instantiate the generic theorem to obtain:

   ```lean
   theorem canAvoidLoss_afterOpening_add_four
       (hN : Eligible N)
       (ha : OpeningFamily N a)
       (hsmall : CanAvoidLoss owner (GamePosition.afterOpening N a)) :
       CanAvoidLoss owner
         (GamePosition.afterOpening (N + 4) (liftOpening N a))
   ```

53. Simplify `liftOpening` to the identity if the successful family preserves an old opening \(a\), using the already-proved `add_four_counters_after_opening`.

54. Translate the result through `canAvoidLoss_iff_value`, the post-opening decomposition, and Step 9’s normalization theorem.

55. State explicitly that the family is uniform, legal, and defined for unboundedly many \(N\). Confirm that the theorem handles every adversarial reply rather than only optimal lines.

56. Run the full build and audit declaration names, categories, imports, and proof assumptions. At this point the parametric \(N\mapsto N+4\) strategy-transfer target is complete.

## Commit 10 — `feat(CatchUp): check finite non-loss certificates`

This is needed only to turn the conditional reduction into an unconditional infinite family.

57. Define a compact certificate: one selected child at friendly nodes and complete coverage at adversarial nodes.

58. Implement an independent checker that recomputes legality, transitions, terminal status, and card decrease.

59. Prove:

   ```lean
   theorem checkCertificate_sound
       (h : checkCertificate owner p cert = true) :
       CanAvoidLoss owner p
   ```

60. Generate and check the smallest base certificates required for the chosen congruence classes and opening family.

61. Compare the certified result against `Position.value` on those small states and run the full build.

## Commit 11 — `feat(CatchUp): derive an infinite reachable family`

62. Prove that eligibility and the opening-family hypotheses are preserved by \(N\mapsto N+4\).

63. Iterate `canAvoidLoss_afterOpening_add_four` by induction on \(k\).

64. Combine the induction with the finite base certificates to obtain non-loss for an infinite family \(N=N_0+4k\).

65. If both players’ certificates and transfers are available, conclude `.draw`. Otherwise state the exact one-sided non-loss theorem; do not overclaim.

66. Add the result as a precisely described solved variant of the open conjecture. Add a `formal_proof` link only once a stable public location exists.

67. Run `lake --wfail build`, check every new declaration’s attributes, and verify that the original open conjecture is the only remaining proof placeholder.

The confidence profile is asymmetric: Commits 3–5 are straightforward engineering, Commit 6 is the genuine research uncertainty, and Commits 7–11 are plausible only after Commit 6 produces a genuinely small phase relation. Delaying certificates and the generic simulation abstraction until after strategy discovery prevents us from spending substantial effort formalizing the wrong invariant.
