> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Catch-Up completed-turn invariant investigation — September 28, 2026

## Verdict

**The endpoint and the general conjecture remain open. No substantive affirmative
step toward the endpoint was obtained.**

This was a conceptual investigation, not an outcome-table campaign. It produced
one precise negative theorem: a particular prepaid pairing-reserve invariant,
even with an arbitrary unpaired pool, can be initialized immediately after an
opening from `Position(Icc 3 N,1)` only when **N=7 and the opening is three**.
This classification is proved parametrically in Lean. No parity assumption is
needed for the obstruction.

The invariant has a complete paper-level preservation argument. Its failure is
at initialization, not at an unproved claim that repayment will work. The
preservation argument was independently reviewed, but is **not formalized**.
Only the initialization classification is a new Lean theorem.

This does not exclude other invariants, delayed entry into this reserve region,
or more adaptive use of interval geometry. The reserve inequalities were chosen
as sufficient conditions for one strategy; they are not necessary for nonloss.

## Scope and unchanged target

- Start: **11:08:19 EDT**, September 28, 2026.
- Hard cutoff: **12:08:19 EDT**.
- Base: `fb94555a`, the latest local branch containing the requested commit.
- Branch: `codex/catchup-turn-invariant-20260928`.
- Checkout: `HISTORICAL_TMP/catchup-score-debt-20260928`.
- Initial working tree was clean. The existing checkout was reused. The main
  `formal-conjectures` checkout and its unrelated untracked file were not changed.
- No push, merge, conjecture assumption, new outcome table, controller synthesis,
  or computational counterexample search was performed.

The research target remains

\[
N\ge7,\quad \operatorname{Even}(N(N+1)/2)
\quad\Longrightarrow\quad
\operatorname{value}(\langle\{3,\ldots,N\},1\rangle)\ne\mathrm{loss}.
\]

An opening `a` switches immediately to the opponent, leaving support
`(Icc 3 N).erase a` and protected-player lead `a-1`. This interpretation agrees
with `FirstPairDescent.first_pick`. Values remain current-mover-relative.

The completed-turn API was checked, not reproved: at positive deficit `d`, a
chosen nonempty subset `A` is playable as a completed turn exactly when
`d <= sum(A) < d + max(A)`. The endpoint switches players and has deficit
`sum(A)-d`. `CompletedTurnReflection` separately establishes the singleton rule
at deficit zero. Early inability-to-catch termination is not a completed turn.

## The selected invariant and one refinement

The older reports already reject unconditional fixed pairings, mate queues, and
static balanced partitions. This session did not retest those conjectures. It
examined whether explicit score and availability inequalities could supply the
missing legality argument, and whether they could fit an actual interval opening.

At an opponent-turn boundary, fix the protected player's actual lead `L`.
Partition the remaining counters into a paired reserve `P` and an unpaired pool
`B`. All counters are positive and distinct. Let

- `D` be the sum of the absolute gaps of the pairs;
- `W = sum(B)`.

The initial candidate has `B` empty. The sole refinement allows an arbitrary
unpaired pool, with no cardinality bound. Require

\[
D+W\le L,\qquad L+D+W\le x\quad\text{for every }x\in P. \tag{R}
\]

This pays for every adverse pair orientation and all unpaired counters in
advance. The second inequality ensures that the first paired counter selected
by the opponent ends that turn. Neither condition uses an outcome lookup.

The protected-turn phase remembers the actual preparation `T subset B`, its
total `t`, the opponent's selected paired counter `x`, and its remaining mate
`z`. The protected response is `z`, with no retrospective ownership changes.

## Why preservation works

If a pair remains, `D>=1`, hence `W<L`. The opponent cannot catch using only
unpaired counters; its turn consists of some preparation `T subset B` followed
by exactly one paired counter `x`. A paired counter remains available throughout
preparation and guarantees catchability. Every preparation prefix is below `L`.

Set `delta=z-x`, `g=abs(delta)`. Replying with the mate is legal and catches:

\[
L-t+\delta\ge L-W-g\ge D-g\ge0.
\]

The macro updates the actual quantities to

\[
L'=L-t+\delta,\qquad D'=D-g,\qquad W'=W-t.
\]

The two preservation identities are

\[
L'-D'-W'=(L-D-W)+\delta+g\ge L-D-W,
\]
\[
L'+D'+W'=(L+D+W)-2t+\delta-g\le L+D+W.
\]

Thus both inequalities persist on the remaining reserve. Every macro removes
one pair. When no pairs remain, `L>=W`; even assigning the entire remaining
pool to the opponent cannot make the protected player lose. If equality holds,
positivity forces exhaustion before the opponent can tie. A certified state
with `L=0` is already empty. These observations cover ties, both terminal
conditions, and the well-founded induction.

The complete argument is in `research/turn-invariant-20260928/ARGUMENT.md`.
This is a restricted strategy theorem, not a strategy for all requested roots.

## Exact Lean theorem: initialization is possible only at seven

Every genuine pairing satisfies `card(P) <= 2*D`, since each distinct integer
pair has gap at least one. Forget the pairing and retain the weaker envelope

```text
BudgetEnvelope S L :=
  exists B subset S, exists natural D,
    card(S \ B) <= 2*D
    and D + sum(B) <= L
    and forall x in S \ B, L + D + sum(B) <= x.
```

This envelope is only a necessary numerical condition; it is not asserted to
be a sufficient safety certificate. The new theorem is exactly:

```lean
theorem budget_envelope_initialization_iff (N a : ℕ)
    (hN : 7 ≤ N) (ha : a ∈ Finset.Icc 3 N) :
    BudgetEnvelope ((Finset.Icc 3 N).erase a) (a - 1) ↔
      N = 7 ∧ a = 3
```

The proof uses interval geometry through its least paired counter:

1. The paired reserve cannot be empty: the entire residual interval has more
   mass than the opening lead `a-1`.
2. Let `m` be its minimum. The envelope gives `a+W<=m`, with `D>=1`.
3. If `m>=a+2`, counter `m-1` is available and below the reserve, so it lies in
   `B`. Then `W>=m-1`, contradicting `a>=3`. Thus `m=a+1`.
4. If `a>3`, counter three similarly lies in `B`, contradicting `W<=1`.
   Therefore `a=3`, `m=4`, and positivity forces `B` empty.
5. Now `D<=2` and `N-3=card(P)<=2D<=4`, so `N=7`.

Sharpness uses the pairs `{4,5}` and `{6,7}` after opening three at seven:
`L=D=2`, `W=0`. This does not add a new game-outcome certificate at seven;
that endpoint was already certified.

## What this changes, and what it does not

The result retires this exact immediate-entry mechanism for all larger N,
including every larger admissible N. It is not a small counterexample extrapolated
to infinity: the obstruction is an algebraic proof for arbitrary N, arbitrary
opening, arbitrary pool, and arbitrary possible pairing.

It nevertheless remains a negative result about a conservative sufficient
condition. It does not show that interval strategies must be complicated or
that every pairing-based argument is impossible. No positive endpoint family,
new interval certificate, or general Catch-Up theorem was proved.

The unresolved target implication is an entry/initialization mechanism. One
could seek a strategy reaching this reserve later, but this session supplies
no such strategy and no evidence that this would simplify the original problem.
It would be misleading to package later entry as a routine closure lemma.

**Next-run judgment:** do not spend another session changing constants or adding
unpaired counters to this prepaid budget. A new attempt would need a specific
mechanism allowing useful counters to be contested without prepaying all their
possible losses, or a genuinely simpler entry theorem. None was found here.

All larger obligations remain: this first-pair nonloss endpoint, its separate
nonwin direction, `B(N,3)`, lower-ray interiors, and the `TA`/`TB` nonwin
obligations. Existing upper-endpoint results and the conditional antepenultimate
endpoint are unchanged; all original certificates through 28 are preserved.

## Checks and evidence boundary

- Lean source: `scripts/catch_up/TurnReserveInitialization.lean`.
- Axiom audit: `scripts/catch_up/TurnReserveInitializationAudit.lean`.
- The only new public theorem is the parametric initialization classification.
  Its three private proof lemmas are not separate research milestones.
- The scoped strict builds passed, including the final source after formatting
  and the audit file after its trailing-blank-line cleanup.
  Each invocation targeted only `catch_up.TurnReserveInitializationAudit`; the
  source and its audit were the two rebuilt modules, with dependencies cached.
- The transitive whitelist contains only `propext`, `Classical.choice`, and
  `Quot.sound`; no conjecture, new axiom, `sorryAx`, or native-evaluation axiom
  is allowed. The module imports `FormalConjecturesUtil`, not the Catch-Up
  conjecture statement.
- One independent reviewer accepted the paper argument, checking actual player
  identities, arbitrary preparation, exact ties, early completion, subtraction,
  the pairing-to-envelope implication, and the scope of the negative theorem.
- The same reviewer then checked the final Lean statement against the paper and
  returned PASS. The bridge from genuine pairings to the numerical envelope is
  paper-level, not an additional formalized theorem.
- No mathematical falsification computation was needed. Lean's concrete
  seven-point arithmetic witness is not a game-tree computation.

Skills influenced the work by requiring one explicit mechanism, stopping at its
exact obstruction after one refinement, checking the statement independently,
and distinguishing the bounded investigation from solving the conjecture.

## Verification record before committing

By **11:33 EDT**, the mathematical argument, formalization, both strict builds,
and both passes by the single reviewer were complete. No numerical search was
run. The route was retired at its proved initialization obstruction rather than
using the remaining hour for another guess.

The source has one public theorem and three private lemmas. All four are covered
transitively by the audit of the public theorem. Source SHA-256:

```text
0fd4cbf6985c4554144186ade6812be6ec106f10974984213d78e488a5b7e483
```

The build processes returned successful exits, and the one review agent is
completed. No search or research process was left running. Shared Lean tool
servers were not terminated. Process-list access was unavailable in the sandbox;
process accounting here is based on the completed handles launched in this run.

Post-commit preservation checks are appended below.
