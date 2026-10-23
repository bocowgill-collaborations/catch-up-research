> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.Increasing](../../CatchUp/Increasing.lean).

# Increasing first-pair strategies — October 20, 2026

The first-pair draw family remains open. This session proves an exact canonical strategy reduction
and a quantitative turn bound, and connects them to the recovered pair-deletion reduction.

## Proved structural result

For every finite set of positive counters, every deficit, and either fixed protected player:

> The protected player can avoid losing if and only if they can do so while choosing strictly
> increasing counters within each of their own turns. The opponent retains every legal pick.

`Increasing.check_iff` proves this equivalence for the explicit executable restricted classifier.
Its recurrence tests `lower < counter` only at the protected player's nodes. It resets the lower
bound after opponent picks; same-player continuation follows the actual deficit rule. Soundness
holds even without the positivity assumption; completeness at initial lower bound zero uses it.

The proof kernel is `safe_next_gt`. Let x be the least safe pick and suppose x < d, so the same
player continues. If a safe next pick y were no larger than x, legality gives y != x and hence
both x,y < d. Taking x then y and y then x gives the identical remaining set, deficit, and actual
player, including when the second pick catches exactly. The reversed first pick is nonterminal:
subtracting a below-deficit counter preserves catchability. The mover can therefore take y then x
and reach the same safe endpoint, contradicting minimality of x. Thus **every** safe next pick is
larger than x, not only the next least-safe pick.

Induction on remaining cardinality selects a least-safe witness at friendly states. At opponent
states the induction handles every available counter. The invariant used in completeness says
that safe friendly choices exceed the stored lower bound; it is justified by the commutation
lemma. It is not an assumed draw invariant or a lookup-based proof of interval safety.

`exists_least_safe_turn` constructs a complete legal turn ending in a safe state.
`LeastSafeTurn.pairwise` proves that its entire list, including the final catching pick, increases.
If k picks precede that final pick, positivity and strict increase imply

    k*(k+1) <= 2*sum(preparation) < 2*deficit <= 2*N.

`reachable_preparation_length_bound` proves the strict bound `k*(k+1) < 2*N` for every such turn
from any reachable size-N interval position. It reuses the existing completed-turn and reachable-
deficit theorems. This bounds preparation length by O(sqrt N); it does not bound total strategy-DAG
size or prove a polynomial-size proof family. The old unordered completed-turn API already removes
turn permutations at the set level. The new result banks the previously unformalized atomic
least-safe rule and its protected-player-only classifier; no new solver-complexity bound is claimed.

## Application to the first pair and the original conjecture

`first_pair_eq` identifies `P_N = Position(Icc 3 N,1)` with `pairDeletionPosition N 1 2`.
`first_pair_reachable` proves that, for N >= 2, it is reached by the actual original opening one
and the following pick two. Every later legal reply remains within the recovered reachability API.

`first_pair_draw_iff` characterizes P_N being drawn by acceptance of both restricted classifiers,
one for each protected player. This does not assert that either accepts for arbitrary N.
`interval_draw_of_checks` feeds both guarantees into the existing
`value_Icc_eq_draw_of_lower_pair_deletion_nonloss`; **the lower pair-deletion nonloss hypothesis
remains required**. No implication from first-pair draw alone to C was introduced.

Boundary correction: eligibility for C does not itself make every first-pair position drawable.
P_3 = ({3},1) wins, kernel-certified here. P_0 has empty support and positive deficit, hence loses.
These do not refute C, whose initial roots differ. The substantive proposed first-pair draw is
for eligible N >= 7, with the separate small draw P_4. The canonicalization theorem holds for all N.

## Kernel regressions, adversarial tests, and a failed stronger rule

- `first_pair_four_checks` and `first_pair_seven_checks` replay both increasing-turn nonloss checks
  with `decide +kernel`. These validate the new classifier on already-known small cases; they do
  not extend the previously reported finite frontier.
- The stronger rule 'take the smallest available counter' fails at P_7. From representative scores
  (0,1), legal picks [3,7,4,5,6] end at (12,14). Friendly picks 3,4,5 are all least available at their
  actual friendly nodes. The turn [4,5] is a same-player continuation. The Lean regressions prove
  the full legal trace, friendly identities/minimality, and terminal loss by two.
- The independent Python probe checks 13,312 owner/state claims over every subset of 1..9, deficits
  0..12, and either protected-player perspective. It checks 4,564 least-safe continuations and all
  10,719 safe next choices, with no violation of the strict-increase theorem.
- At N = 4,7,8,11,12, for both protected players, the least-safe strategy graph contains 1,635 nodes
  and 1,167 friendly edges. The traversal explicitly expands all 1,263 available opponent edges;
  it is not a principal variation or a favorable sample. N11/N12 exercise larger counter labels outside the exhaustive nine-counter sweep.
- 1,664 executable Lean checks on irregular states and ten root/owner checks agree with a separate
  absolute-score minimax implementation. These runtime observations are computational evidence;
  the universal theorem and small kernel regressions provide the formal assurance.

## Verification and accounting

Run from `research/catchup`:

```sh
python3 first_pair/verify.py lean
python3 first_pair/verify.py experiments
python3 verify.py sources
```

The strict build includes both the main `CatchUp` target and `CatchUp.IncreasingAudit`. All 23
new audits allow only `propext`, `Classical.choice`, and `Quot.sound`. No unfinished conjecture,
custom axiom, native computation result, or external solver answer appears on their proof paths.
The three additional reused modules are preserved verbatim apart from import/category handling;
`first_pair/SOURCES.json` pins their Git blobs at the same research commit as the earlier session.
Lean 4.27.0 and the pinned Mathlib revision are unchanged.

`benchmark.json` records new and reused source bytes separately, compiled-module bytes, commands,
wall-clock checking cost, and measured peak child RSS. The finite probe has a 100-second internal
limit; subprocesses have 120-second limits. The optional-state search work from the previous
session is preserved and remains in the default build. No frontier computation or Turing-machine
optimization was attempted.

Adversarial self-review checked: both catch polarities in the commutation identity; distinctness
of reordered legal counters; impossibility of early termination after a continuing pick; owner
identity before each recursion; unrestricted opponent quantification; positivity at lower zero;
exact empty-preparation handling; reachable deficit bound; and the hypotheses retained in the
pair-deletion bridge. Source transformations and transitive axiom audits are independently
executable. This is self-review, not a separate model referee.

## Single next mathematical obligation

Attack the interval-geometry statement

    N >= 7, Even(N*(N+1)/2) -> value(Position(Icc 4 N,2)) != win.

It would make pick three nonlosing in P_N. Exact independent checks at N7,8,11,12 give a draw for
that child, while the analogous N4 child wins; the N >= 7 restriction matters. The new normal form
can restrict the protected player's continued picks in that child, but still supplies no uniform
safe-choice rule. Nonwinning of P_N and the other lower pair-deletion states remain separate open
obligations. Do not replace 'least safe' with an arithmetic rule without a fresh closure proof.
