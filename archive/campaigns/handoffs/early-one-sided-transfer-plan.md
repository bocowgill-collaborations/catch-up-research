> **Historical research handoff.** Plan and reported knowledge at the time; no new theorem is asserted by this export. Consult the [finding ledger](../../../results/legacy-findings.md). The N≤38 attribution is personal communication, not a public certificate.

The right first theorem is a one-sided strategy-transfer result, not the unrestricted equation
\[
\operatorname{value}(N+4)=\operatorname{value}(N).
\]

I would aim for the following schema:

```lean
theorem canAvoidLoss_of_fourLift
    (hrel : FourLift N small large)
    (hsmall : CanAvoidLoss player small) :
    CanAvoidLoss player large
```

Then prove that `FourLift` contains an infinite family of genuinely reachable positions—ideally post-opening positions
\[
P(N,a)=\bigl(\{1,\ldots,N\}\setminus\{a\},\,a,\,\mathrm{p2}\bigr)
\]
for a natural opening family such as \(a=1\), \(a\in\{1,2,3\}\), or another simple pattern discovered computationally.

This is respectable even if it proves only that one player can avoid losing. If transfer works for both players, the stronger draw result follows.

The key acceptance conditions are:

- the family covers infinitely many \(N\);
- its definition is uniform in \(N\), not a table of positions;
- it contains legally reachable positions;
- it handles every adversarial reply, not merely one optimal line;
- the four additional counters are processed by a bounded, understandable strategy protocol.

## Commit 1 — `refactor(catch-up): introduce deficit-normalized positions`

1. Record the intended theorem schema and the criteria above in the module documentation of CatchUpConjecture.lean (`SOURCE_CHECKOUT/FormalConjectures/Paper/CatchUpConjecture.lean`; historical path), without asserting a particular opening family yet.

2. Introduce a proof-oriented post-opening state:

   ```lean
   structure Position where
     remaining : Finset ℕ
     deficit : ℕ
   ```

   Here `deficit` is the opponent’s score minus the score of the player currently picking.

3. Define the normalized single-pick transition. For \(x\in R\):

   - if \(x<d\), the same player continues with deficit \(d-x\);
   - if \(d\le x\), control changes players with deficit \(x-d\).

4. Define terminal positions:

   - `remaining = ∅`;
   - or `remaining.sum < deficit`, meaning the current player cannot catch up.

5. Prove that every transition decreases `remaining.card`, giving a clean induction principle for later strategy proofs.

6. Prove basic transition lemmas for the two branches, erasure, remaining sums, and positivity on `Finset.Icc 1 N`.

7. Add small `@[category test]` examples reproducing the \(N=4\) play from the paper.

8. Run `lake --wfail build`. This and every later commit must compile independently.

## Commit 2 — `refactor(catch-up): relate normalized and score-based evaluation`

9. Define a normalized recursive evaluator `positionValue remaining deficit`, expressed entirely through the transition from Commit 1.

10. Derive its unfolding equations explicitly. Later proofs should use these equations rather than unfold well-founded recursion manually.

11. Prove score-translation invariance of the existing evaluator:

    \[
    \operatorname{valueAux}(R,a+c,b+c,\mathrm{false})
      =\operatorname{valueAux}(R,a,b,\mathrm{false}).
    \]

12. Prove the main normalization theorem:

    \[
    \operatorname{valueAux}(R,s,s+d,\mathrm{false})
      =\operatorname{positionValue}(R,d).
    \]

13. Define the post-opening state

    ```lean
    def afterOpening (N a : ℕ) : Position :=
      ⟨(.Icc 1 N).erase a, a⟩
    ```

    and prove the corresponding equation for `value (.Icc 1 N)`.

14. Check the normalized evaluator against the original evaluator for small \(N\). These are regression tests, not research claims.

15. Run the full build. If the normalization proof is unexpectedly difficult, resolve it here; later commits should not carry two unconnected semantics.

## Commit 3 — `feat(catch-up): formalize reachability and non-losing strategies`

16. Extend the proof-level state with the identity of the player currently picking:

    ```lean
    structure GamePosition extends Position where
      toMove : Player
    ```

17. Define the absolute transition relation `GamePosition.Step`, including whether a pick keeps or switches `toMove`.

18. Define `ReachableFromOpening N a p` as the reflexive-transitive closure of legal picks starting from the position after player 1 opens with \(a\).

19. Define terminal outcomes relative to a fixed player. In a cannot-catch-up terminal state, `toMove` loses; when the remaining set is empty and the deficit is zero, the outcome is a draw.

20. Define `CanAvoidLoss player p` by well-founded recursion on `remaining.card`:

    - at the player’s nodes, there must exist a safe move;
    - at the opponent’s nodes, every legal move must remain safe;
    - terminal states must be a win or draw for `player`.

21. Define the analogous `CanForceDraw` only if it proves useful. Avoid committing to exact draws when one-sided non-loss is enough for the reduction.

22. Prove that `CanAvoidLoss` corresponds to the appropriate bound on `positionValue` and hence on the existing `value`.

23. Prove that every `afterOpening N a` with \(a\in\{1,\ldots,N\}\) is a legitimate reachable position with player 2 to move.

## Commit 4 — `feat(catch-up): add reproducible exact strategy search`

24. Implement an exact research solver over normalized states keyed by `(remaining-mask, deficit, toMove)`. Keep it under `scripts/catch_up/`; do not put experimental machinery in `FormalConjecturesForMathlib`.

25. Use transposition tables and alpha-beta or outcome-bound pruning. The solver must retain more than the final outcome.

26. For a selected player’s non-losing strategy, export the complete strategy DAG:

    - one selected move at that player’s nodes;
    - every legal continuation at adversarial nodes.

    A principal variation is insufficient for proving a strategy.

27. Reproduce the published outcomes through the available exact frontier before trusting new output.

28. Export normalized traces for paired games \((N,N+4)\), initially using several pairs among \(N\le28\). Record:

    - which top-four counters remain;
    - score deficit;
    - player to move;
    - corresponding smaller-game state;
    - whether a transition consumes an old or new counter.

29. Add deterministic solver tests on small games. Do not make \(N=31,32\) a prerequisite; those instances are held-out evidence if they become affordable.

## Commit 5 — `feat(catch-up): add independently checkable strategy certificates`

30. Define a compact certificate format for `CanAvoidLoss`. At friendly nodes it records one move; at adversarial nodes it must cover every move.

31. Implement an independent checker that recomputes legality, transitions, terminal outcomes, and acyclic progress rather than trusting annotations from the solver.

32. Prove the checker sound:

    ```lean
    theorem checkCertificate_sound
        (h : checkCertificate player p cert = true) :
        CanAvoidLoss player p
    ```

33. Verify small certificates inside Lean and compare them with the original minimax evaluator.

34. Keep large certificates as research data unless their size is reasonable. The eventual parametric theorem must not depend on a giant \(N=28\) certificate.

35. Use the checked policies to distinguish robust strategy structure from accidental optimal lines.

## Commit 6 — `research(catch-up): define the four-counter reduction relation`

This is the research gate. Do not commit it until a stable pattern has actually been found.

36. Compare the strategy DAGs for several \((N,N+4)\) pairs and infer a finite collection of phases. A phase will likely record:

    - a subset of \(\{N+1,N+2,N+3,N+4\}\);
    - whether the large and small games have the same player to move;
    - an affine relationship between their deficits;
    - whether the smaller game is advancing or temporarily stuttering.

37. Test candidate opening families in increasing order of mathematical value:

    - a fixed opening such as \(a=1\);
    - a bounded family such as \(a\in\{1,2,3\}\);
    - a simple affine or complementary opening;
    - a larger class defined by inequalities.

38. Define `FourLift N small large` using the smallest stable phase set. Its definition may refer to \(N+i\) and simple affine deficit offsets, but not to particular numerical values of \(N\).

39. Check the relation on multiple discovery pairs and at least one held-out pair.

40. Reject the candidate unless every opponent move from every related reachable state is covered. Agreement only along the solver’s preferred line is not enough.

41. Prove preliminary structural facts:

    - old and top-four counters are disjoint;
    - the top-four mask determines the phase;
    - related states are well formed;
    - the relation has a bounded phase rank.

42. Confirm nontriviality computationally: the relation should cover an unbounded post-opening family and a substantial adversarial subtree, not a contrived isolated endgame.

If this gate fails, the correct response is to retain the infrastructure and narrow the target—for example, to an endgame reduction with an explicit deficit bound. Do not force a complicated relation merely because it fits data through \(28\).

## Commit 7 — `feat(catch-up): prove the generic strategy-lifting criterion`

43. Formulate an alternating-simulation interface between a smaller state and a larger state. It must distinguish:

    - moves chosen by the strategy owner;
    - universally quantified opponent moves;
    - large-game “stuttering” moves that process a new counter without advancing the small game.

44. Add a well-founded rank combining `remaining.card` with the finite reduction phase, preventing infinite stuttering.

45. State local simulation obligations:

    - safe terminal states map to safe terminal states;
    - at an owner node, a safe smaller move can be implemented in the larger game;
    - at an opponent node, every larger move can be matched;
    - each match either advances the small game or decreases the phase rank.

46. Prove the generic lifting theorem by well-founded induction:

    ```lean
    theorem CanAvoidLoss.lift
        (hsim : StrategySimulation player rel)
        (hrel : rel small large)
        (hsmall : CanAvoidLoss player small) :
        CanAvoidLoss player large
    ```

47. Test the abstraction on a deliberately simple relation, such as identity or score translation, before instantiating it with the top-four block.

## Commit 8 — `feat(catch-up): prove the parametric four-counter simulation`

48. Prove the elementary block arithmetic, including

    \[
    (N+1)+(N+4)=(N+2)+(N+3)=2N+5,
    \]

    together with every inequality required by the phase transitions.

49. For each reduction phase, prove that the prescribed friendly move is present and legal.

50. For each reduction phase, split all adversarial moves into:

    - one of the remaining top-four counters;
    - an old counter \(x\le N\).

    Prove that every case lands in another phase or advances the related smaller state.

51. Prove terminal compatibility, particularly the cannot-catch-up condition. This is likely subtler than the ordinary transition cases because it depends on the total remaining sum.

52. Prove strict progress for every stuttering transition.

53. Assemble the phase lemmas into `StrategySimulation player (FourLift N)`.

54. Instantiate the generic theorem:

    ```lean
    theorem canAvoidLoss_of_fourLift
        (hrel : FourLift N small large)
        (hsmall : CanAvoidLoss player small) :
        CanAvoidLoss player large
    ```

55. Remove any phase that turned out to be unreachable or redundant, then rerun the proof. A small understandable phase machine is part of the mathematical result.

## Commit 9 — `feat(catch-up): derive an infinite reachable-position result`

56. Prove that the selected post-opening family satisfies `FourLift`. The desired corollary should resemble:

    ```lean
    theorem canAvoidLoss_afterOpening_add_four
        (hN : EligibleResidue N)
        (ha : OpeningFamily N a)
        (h : CanAvoidLoss player (afterOpening N a)) :
        CanAvoidLoss player (afterOpening (N + 4) (liftOpening N a))
    ```

57. Prove the required finite base cases with small, transparent certificates.

58. Iterate the reduction to derive a theorem for every \(N\) in at least one infinite congruence subsequence and the chosen opening family.

59. If both players’ non-losing strategies transfer, derive that the minimax value is `.draw`. Otherwise state the honest one-sided result; that is still meaningful partial progress.

60. Add the final result as a `research solved` variant beside the open conjecture, with a concise description of exactly what has been proved. Supporting lemmas should use `category API`.

61. Update the references with the current computational-status source and explain that finite computation was used to discover the invariant but is not part of the parametric proof.

62. Run `lake --wfail build`, audit every new declaration’s attributes, and ensure the only remaining `sorry` is the original open conjecture.

The main uncertainty is Commit 6, not the Lean work. The evidence threshold there should be high: a three-phase uniform relation that handles all replies would be a result; a forty-phase relation reconstructed from particular \(N\)-values would be disguised computation. I would consider the project successful once Commit 9 proves one infinite, legally reachable post-opening family—even if the full Catch-up conjecture remains well out of reach.
