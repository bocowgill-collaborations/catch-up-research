> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Catch-Up: full mandatory atomic-two-buffer controller

Run started September 28, 2026, 08:34:26 EDT. Hard cutoff: 09:34:26 EDT.
Base: `c81982ef681b36dd08bc8ea7429c853935308d69`.
New local branch: `codex/catchup-two-buffer-20260928`.
Checkout: `HISTORICAL_TMP/catchup-score-debt-20260928`.
The `collaboration` remote is `the historical private research remote`.
No push or merge. All previous reports and certificates are unchanged.
The full proof, replay, and axiom checks passed by 09:07 EDT, within the hour.

## Verdict

**Yes: the full mandatory instance admits a uniform causal controller in the
specified atomic-two-buffer language**, using raw repository remaining sets.
The policy covers every actual-opponent move and every strict-win-preserving
reply of an arbitrary supplied shadow winning strategy. Both games terminate,
and every resulting pair satisfies

    completedMargin(actual) >= completedMargin(shadow) - 2.

This is a Lean-certified finite result, not just successful simulation.
The main theorem is `CatchUp.TwoBuffer.mandatory_protocol`.
The scalar gate passes sharply: `m(U)=0`, `m(V)=2`.

A new parametric two-pick preparation and copied-pair repair explains the previously
uncovered actual prefix `[2,11]`. These are structural transition/trace lemmas,
not a general adjacent-hole translator. **Catch-Up remains open in this
repository; no interval certification frontier was advanced.**

## Exact roots and quantifiers

Protect `p1`; its identity never changes when turns switch:

    U = GamePosition({2,5,6,9,10,11}, 1, p1)
    V = GamePosition({2,5,6,7,10,11}, 1, p1)

The absolute-score implementation starts both games with scores `(0,1)`.
Python player `0` means Lean `p1`; Python player `1` means Lean `p2`.

At each paired state the controller commits to one nonterminal game:

- Actual protected turn: the controller commits to one legal pick.
- Actual opponent turn: all legal picks are universal branches.
- Shadow opponent turn: the controller commits to one legal pick.
- Shadow protected turn: all legal strict-win-preserving picks are universal
  branches, not just margin-optimal picks.

No move is observed before selecting its game. No hypothetical query to the
supplied strategy can be rejected. Different winning strategies, including
history-dependent ones, are covered by universal branching at every reached
shadow protected turn. The winning reply set must be nonempty; the Lean
protocol includes this requirement explicitly.

Each atomic move removes one counter. Total remaining cardinality decreases
strictly, from twelve initially; no stuttering, waiting, or fairness premise is
needed. A leaf succeeds only when **both** games are terminal and the inequality
holds.

The shadow outcome predicate restricts the supplied strategy. It is not claimed
to be an ownership invariant or a structural proof of repayment. Search uses
exact outcome calculations for this permitted restriction and solves a finite
AND/OR game. The extracted arithmetic repair does not use outcome lookups.

## Scalar gate and completion

For a normalized current-mover state `(S,d)`, the exact recurrence is

    m(S,d) = sum(S)-d                         if terminal;
    m(S,d) = max over x in S of
               m(S\{x}, d-x)                 if x<d,
              -m(S\{x}, x-d)                 if x>=d.

A normalized mover is behind or tied. At a nonempty terminal state, `sum(S)<d`;
awarding all remaining counters to that mover leaves the player behind. Empty
support gives the actual final margin, including zero at a tie. A pick below
the deficit retains mover and payoff orientation. A pick at or above the
deficit switches movers, including equality, and negates the child's margin.
Induction on remaining cardinality justifies the recurrence.

The existing `GamePosition.completion_sign` proves winner preservation.
Existing parity and ledger lemmas are reused. Root effective totals are `44`
and `42`, both even. Thus a terminal shadow win has margin at least two, and
the two-point certificate implies actual nonloss.

An independent absolute-score recurrence plays until support is empty, without
the early-terminal shortcut. If catching up is impossible, the trailing player
takes every remaining counter, in any order. Comparison with the normalized
recurrence passes **4,352** tested states: every subset of `{1,...,7}`, deficits
zero through `sum(S)+2`, and both mover identities. This is a computational
regression check, not a parametric theorem.

The exact root values are additionally certified in Lean by matching strategy
bounds (`mandatory_scalar_bounds`):

- Actual `p1` can ensure protected margin at least zero.
- Actual `p2` can ensure protected margin at most zero.
- Shadow `p1` can ensure protected margin at least two.
- Shadow `p2` can ensure protected margin at most two.

These quantified guarantees certify exact minimax margins without trusting
Python or relying on a sign-only outcome table.

### Necessary condition, even without buffers

Choose an actual opponent strategy enforcing margin at most `m(U)`, and supply
a shadow protected strategy enforcing margin at least `m(V)>0`. Finite backward
induction attains these bounds. The supplied shadow strategy is strictly winning,
so any universal translator must handle it. Its completed plays must satisfy

    m(U) >= completedMargin(U) >= completedMargin(V)-2 >= m(V)-2.

Hence `m(U)>=m(V)-2` is necessary independently of buffers, but not sufficient.
Here it holds with equality.

The formal `protocol_necessary_bound` proves this for `Protocol`, using arbitrary
actual upper and positive shadow lower strategy bounds. Its proof never uses
buffer assumptions. Positivity is essential to admit the chosen shadow reply
through the strict-win filter. No separate buffer-free protocol API was added.

## Controller, ownership, and full-instance evidence

`two_buffer_controller.py` uses bit `x-1` for counter `x`, exact scores, fixed
player identities, and permanent owner masks. Search evaluated 1,061 paired
states. The exploratory cache contains 251 successful nonterminal policy states
and 590 unsuccessful explored states; these are not coverage counts.

The exported reachable policy has **87 nodes**: 76 nonterminal and 11 terminal
paired states. Independent replay unfolds merged states along every history
and checks **17 terminal histories**, including every actual second pick
`{5,6,9,10,11}`. At two reached shadow nodes the supplied strategy has three
strictly winning choices `{7,10,11}`; all are included.

Terminal margin pairs are exactly

    (0,2), (2,2), (2,4), (4,2), (4,4), (8,10), (10,10).

Every pair satisfies the certificate. Intermediate debt need not be bounded by
two. The historical difference ledger is

    D = (actual protected score - actual opponent score)
        - (shadow protected score - shadow opponent score).

An actual protected pick adds its counter; an actual opponent pick subtracts it.
Shadow signs are reversed. Entries keep their original owner. Completion adds
each remainder once with its trailing player's sign. Existing
`signed_picks_balance` and `completed_margin_ledger` connect this history to
the Lean payoff.

The separate replay checker does **not** import the synthesis implementation.
It uses tuple supports, absolute scores, ordered ownership histories, and the
previous independent ternary recurrence to check every winning-shadow reply.
It checks legality, child states, all universal edges, decreasing cardinality,
atomic buffers, ledger increments, completion ownership, and terminal margins.
Four corruptions are rejected: wrong initial pick, omitted universal edge,
falsified terminal margin, and reassigned owner.

Lean's `Protocol` exposes the same controller/adversary quantifier order.
`run_check_sound` proves the executable checker sound.
`mandatory_policy_checked` uses `decide +kernel`, not `native_decide`, to check
the root with budget twelve. The search and JSON parser are not trusted.

### Terminal-buffer convention

Buffers count the differences of the repository's raw `remaining` fields after
every atomic pick. Early-terminal completion is payoff accounting, **not an
extra erase transition**.

For example the legal scheduled prefix

    U2, V5, V2, U5, U11, V7, U9, U10

leaves actual scores `(23,15)` and raw remaining `{6}`, terminal because the
opponent cannot catch. Shadow remaining is `{6,10,11}`. Raw widths are `(0,2)`.
Erasing the actual terminal remainder immediately would instead give `(0,3)`.
This policy fails that different convention. This does not refute existence
of another controller under that convention; it was not tested or proved here.

## New repair after actual prefix [2,11]

The old global-maximum rule loses on this branch. The new rule uses a two-pick
protected turn:

    Actual [2,11] -> ({5,6,9,10}, deficit 10, p1).
    Take 5, then 9 -> ({6,10}, deficit 4, p2).

    Shadow [5,2] -> ({6,7,10,11}, deficit 2, p2).
    Choose opponent 7; the supplied winning strategy must take 11.
    This gives ({6,10}, deficit 6, p2).

The actual preparation picks belong to the same protected player. The first
does not catch up; the second does. Copy the actual opponent's revealed pick
6 or 10 in the shadow; both singleton protected replies are forced. The final
margin pairs are `(8,10)` and `(0,2)`.

The saved atomic schedule covers both branches:

    U2, V5, V2, U11, U5, U9, V7,
    U(x), V11, U(z), V(x), V(z),   where {x,z}={6,10}.

The schedule need not finish shadow preparation before observing the next actual
pick. Its buffer bounds hold at every intermediate state, not just endpoints.

The actual second-pick `5` branch still reaches the old terminal gadget:
actual `[2,5,11]` gives `({6,9,10},7,p2)`, while shadow `[5,2,7,11]`
gives `({6,10},6,p2)`. These are the previously proved `actualRoot 2`
and `shadowRoot 2`. The new full policy retains that branch's maximum-pick
actual repair and small-margin shadow reply; the old certificates are reused
and unchanged. The new preparation is needed for the distinct `[2,11]` branch.

### Parametric structural lemmas

For every natural `k`, the actual state

    ({k+3,k+4,2k+5,2k+6}, deficit 2k+6, p1)

has legal completed turn `[k+3,2k+5]`, ending at

    ({k+4,2k+6}, deficit k+2, p2).

The shadow state `({k+4,k+5,2k+6,2k+7},2,p2)` permits the legal bridge trace
`[k+5,2k+7]`, ending on the same support with deficit `k+4`. After the first
bridge pick, every strict-win-preserving protected reply is `2k+7`: either
smaller pick permits an explicit opponent drawing reply.
`bridge_forced_parametric` proves **conditional uniqueness**, not existence
of a winning reply by itself.

The core `copied_pair_repair` is more general. For distinct natural `x,z` and
`d+2<=x<=d+z`, both states

    ({x,z},d,p2),   ({x,z},d+2,p2)

have legal traces `[x,z]`, with completed protected margins

    d+z-x >= 0,   d+2+z-x = (d+z-x)+2.

The inequalities justify every switch and preclude premature terminal moves.
The singleton reply is forced. For `d=k+2` and pair `{k+4,2k+6}`, **both**
opponent choices satisfy the inequalities (`repaired_pair_all_choices`).
Equality includes the shadow tie after the smaller pick and actual final tie
after the larger pick. The family is valid at `k=0`.

`preparation_turn` provides actual legality via `CompletedTurn.pick_trace`;
`shadow_preparation_trace` supplies legal shadow steps.
The two `mandatory_*_preparation` declarations identify the mandatory prefixes
with `k=2` by endpoint equality. Their prefix legality is covered by the full
finite protocol and replay, not by those equalities alone.

These are parametric transition and trace lemmas, not a complete parametric
`Protocol` construction or a proof that other branches reach these families.

## Artifacts and verification

New files under `scripts/catch_up/`:

- `TwoBufferProtocol.lean`: causal quantifiers, atomic buffers, sound checker.
- `TwoBufferMandatory.lean`: full policy and kernel root certificate.
- `CompletedMarginBounds.lean`: strategy guarantees, necessary condition, root bounds.
- `TwoPickDebtRepair.lean`: preparation, forced bridge, copied-pair repair.
- `TwoBufferAudit.lean`: transitive standard-axiom-only audit.
- `two_buffer_controller.py`: scalar recurrence and AND/OR synthesis;
  `--certificate` regenerates JSON and `--lean-entries` regenerates the Lean table.
- `check_two_buffer_policy.py`: independent full-history replay and mutation tests.
- `two_buffer_policy_20260928.json`: 87 reachable policy nodes.
- `two_buffer_replay_20260928.json`: all 17 histories, owners, and ledger events.
- `two_buffer_results_20260928.json`: scalar, regression, and search metrics.
- `two_buffer_verification_20260928.txt`: saved build and axiom-audit output.

Reproduction commands, from the checkout:

    python3 -B scripts/catch_up/two_buffer_controller.py
    python3 -B scripts/catch_up/two_buffer_controller.py --certificate
    python3 -B scripts/catch_up/two_buffer_controller.py --lean-entries
    python3 -B scripts/catch_up/check_two_buffer_policy.py scripts/catch_up/two_buffer_policy_20260928.json --full
    lake --wfail build catch_up.TwoBufferProtocol catch_up.TwoBufferMandatory catch_up.CompletedMarginBounds catch_up.TwoPickDebtRepair catch_up.TwoBufferAudit

Only affected modules were built, not the whole repository. The axiom audit
covers all 27 new public theorems and allows only `propext`, `Classical.choice`,
and `Quot.sound`. No `sorryAx`, new assumption, compiler-trust axiom, or
conjecture placeholder is allowed. Policy regeneration and agreement between
the JSON and Lean action table are also checked.

One independent reviewer was used after a complete candidate existed. The same
reviewer audited the scalar and parametric additions. No mathematical error was
found. Independent checks included all finite replay branches, `k=0,...,50`,
and 440 small copied-pair cases. These bounded checks supplement general proofs;
they are not separate formal certificates. The review's qualifications about
raw buffers, conditional uniqueness, and endpoint equalities are included above.

## What changed, and what remains

Previously, one favorable repair branch was known and the full mandatory instance
was unresolved in this controller language. It is now resolved positively.
Neither margin debt nor atomic width two obstructs this instance.

The new mechanism is **multiple picks within one protected preparation turn**,
followed by shadow opponent replies based only on observed actual moves.
Repayment is secured by forced ownership of the remaining singleton, not an
unassigned pool of unmatched counter values.

The main gap remains uniform structural closure for arbitrary admissible
`(N,b,y)`: no invariant proves that every adversarial branch reaches these
repair families while maintaining the buffers and margin guarantee. The finite
policy table is not such an invariant. The earlier arbitrary-adjacent-pair-erasure
counterexample still blocks that broader relaxation.

Even a general adjacent-hole transfer would only exclude interior winning
openings with both neighbors present. Boundary candidates
`{2,b-2,b+1,N} intersect R`, the other required outcome direction, and the
global Catch-Up induction/shifted-tail obligations remain. No reduction is
presented as a complete solution.

A useful next bounded task is to classify the remaining branches of this policy
structurally, covering each actual second pick, and determine whether those repairs
belong to a finite parametric family. Do not enlarge the buffer or assume global
repayment succeeds merely to obtain closure.
