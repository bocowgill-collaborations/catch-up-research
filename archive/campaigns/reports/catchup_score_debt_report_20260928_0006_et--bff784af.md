> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Catch-Up: causal terminal score-debt repair

Run started September 28, 2026, 00:06 EDT. Hard cutoff: 01:06 EDT.
Final proof, replay, and axiom checks completed before 00:42 EDT, within the one-hour limit.
Base: `f373d9ac`. New local branch: `codex/catchup-score-debt-20260928`.
No push or merge. Previous reports and certificates are unchanged.

## Result and limitation

A structural, parametrically proved terminal repair survives exact checks and independent
review. It covers one reachable branch of the mandatory adjacent-hole example. It does
**not** establish `value(V) = win → value(U) ≠ loss` in general, and does not refute the
two-unmatched-counters-per-side representation.

For every natural `k`, write `a=k+4`, `b=2k+5`, `c=2k+6`. Protect player one in

- actual `A_k = GamePosition({a,b,c}, a+1, p2)`;
- shadow `B_k = GamePosition({a,c}, a, p2)`.

The actual policy takes the largest remaining counter on protected turns, while the
actual opponent may take **any** legal counter. Every terminal actual play completes
to protected-player margin zero or two. In the shadow, choose opponent counter `c`;
the protected reply `a` is the sole legal move, and completes to margin two. Thus every
such paired play satisfies `completedMargin(actual) ≥ completedMargin(shadow) - 2`.

This is the theorem `CatchUp.ScoreDebtRepair.repaired_margin_bound`; the well-founded
strategy conclusion is `actual_can_avoid_loss`. Both are parametric Lean proofs, not
extrapolations from bounded searches.

## Files and verification status

- `scripts/catch_up/CompletedMargin.lean`: completion, fixed-player historical ledger,
  parity preservation, and the two-point transfer theorem.
- `scripts/catch_up/ScoreDebtTerminalRepair.lean`: explicit phase invariant, universal
  adversary closure, causal max policy, nonvacuity, shadow trace, and buffer bound.
- `scripts/catch_up/ScoreDebtRepairCertificates.lean`: initial adjacent-hole parity,
  exact reachability, forced shadow bridge reply, and failed-policy certificates.
- `scripts/catch_up/score_debt_repair_probe.py`: independent absolute-score replay,
  persistent ownership records, asynchronous scheduling, and bounded regressions.

All three theorem modules and `ScoreDebtRepairAudit.lean` have passed warning-strict
scoped builds. The executable transitive axiom audit passes for all 31 new public
theorems, allowing only `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`,
new assumptions, or compiler-trust axioms occur. Saved replay output is in
`scripts/catch_up/score_debt_repair_results_20260928.jsonl`.

## Completion, parity, and fixed-player accounting

Use player one as the protected player; player names never change when turns switch.
Write `M(p)` for protected score minus opponent score. If the terminal state is empty,
completion changes nothing. Otherwise the trailing mover has deficit `d > sum(S)`.
Giving the trailing mover all remaining counters still leaves that player behind by
`d-sum(S)>0`. Hence completion preserves win, draw, and loss. A terminal tie must have
empty support. `GamePosition.completion_sign` proves these assertions for either
protected-player identity and every terminal state, including zero deficit.

Let `T=N(N+1)/2`. The two initial effective totals are

```
1 + sum(U.remaining) = T - 2*b - 2*y + 2
1 + sum(V.remaining) = T - 2*b - 2*y
```

The requested membership assumptions ensure the erased counters are distinct. The
Lean proof uses the exact erase-sum identities rather than truncated-subtraction
heuristics: erase `1`, then pairs `(b-1,b)` and either `(y-1,y)` or `(y,y+1)`.
Both totals are even. Effective parity is invariant under each legal pick, including
ties and same-player continuation. A completed winning shadow margin is consequently
at least two. The theorem `completed_margin_transfer` proves that the proposed
two-point completed-margin inequality suffices for nonloss at paired terminal states.
It does not supply the translator or its invariant.

The historical ledger is not the normalized deficit. Each actual pick `x` contributes
`+x` if taken by the protected player and `-x` otherwise; a shadow pick contributes
the negative of that signed amount to the difference ledger. Once made, an entry
retains its original owner. `signed_picks_balance` and `completed_margin_ledger`
prove the exact telescoping identity. Terminal completion adds the remaining counters
once, with the actual trailing player's sign. The Python replay retains every
counter's player identity and whether it was picked or notionally completed.

Existing APIs inspected and reused include `CompletedTurn`, `GamePosition.PickTrace`,
`SimulationSoundness`'s `p1_score_balance_after_pick`, and the one-sided strategy
semantics. `AggregateSimulationLedger` was inspected; its specialized four-lift
geometry was not relabeled as an adjacent-hole invariant.

## The ownership-sensitive terminal invariant

At entry, the protected margin is `a+1` in the actual game and `a` in the shadow.
The structural invariant `Phase k p` is a finite list of explicit supports, deficits,
and mover identities. It contains no game value, strategy-existence predicate, or
global repayment assumption. `phase_closed` proves closure for every actual opponent
move and every legal protected maximum move. The exact branches are:

| Actual picks | Owners (O = opponent, P = protected) | Completion | Completed margin |
|---|---|---|---:|
| `a,b,c` | `O,O,P` | Empty | `a+1-a-b+c = 2` |
| `a,c,b` | `O,O,P` | Empty | `a+1-a-c+b = 0` |
| `b,c` | `O,P` | Award remaining `a` to O | `a+1-b+c-a = 2` |
| `c,b,a` | `O,P,O` | Empty | `a+1-c+b-a = 0` |

After the first pick `a`, the opponent remains behind by one and may choose either
top counter. After first `b`, the protected deficit is `k`, including the tie `k=0`;
the protected max pick `c` leaves the opponent at deficit `a+2` with only `a`, so
early termination is mandatory. After first `c`, the protected player takes `b`,
leaving the opponent's forced tie with `a`. Thus the branch list is exhaustive,
not a list of cooperative opponent choices. Taking a maximum is always legal before
termination. Remaining-cardinality induction proves `CanAvoidLoss p1 (actualRoot k)`.

In the shadow, opponent pick `c` leaves `{a}`, protected deficit `k+2`, protected
player to move. The only legal reply is `a`; the final protected margin is
`2*a-c=2`. Every supplied legal strategy, in particular every winning strategy,
must make this reply. Shadow choices do not consult future actual adversary moves.

The asynchronous schedule is important:

1. Observe one actual opponent pick.
2. Run shadow opponent pick `c`, followed by the supplied strategy's forced `a`.
3. Resume the actual max controller until termination.

Before the first pick the unmatched actual set is `{b}`, with no unmatched shadow
counter. After the first actual pick, each remaining support has at most two counters.
Every subsequent actual/shadow legal continuation therefore has at most two unmatched
counters per side; `buffer_after_first_pick` proves this parametrically. Running
both shadow picks first would violate this bound, leaving three actual counters
against an empty shadow. Every atomic step decreases the sum of remaining cardinalities;
the entire repair uses at most five picks. There is no waiting loop or retrospective
assignment of a counter's owner.

Intermediate ledger debt need not stay above minus two. Repayment here is secured by
the enumerated legal ownership phases, not by treating the sum of available unmatched
counters as guaranteed credit. The margin guarantee is a **terminal** invariant.

## Mandatory instance and exact failed extensions

The old report already proves the forced first pair: actual `2`, shadow `5`.
The resulting unmatched sets are `{5,9}` and `{2,7}`, with opponent to move in both.
On the actual adversary branch choosing `5` next, take actual protected `11`.
In shadow choose opponent `2`, then `7`; the supplied protected winning strategy
must take `11`. The theorem `shadow_bridge_forced` certifies that choosing `6` or
`10` instead allows the opponent a nonloss; no winning strategy can choose those.
The exact prefixes are:

```
actual: [2,5,11]     -> ({6,9,10}, deficit 7, p2)
shadow: [5,2,7,11]   -> ({6,10},   deficit 6, p2)
```

These are exactly `(A_2,B_2)`. Both prefix traces are Lean-certified legal. A width-two
entry schedule is actual `2`, shadow `5`, actual `5`, shadow `2,7`, actual `11`,
shadow `11`. The positive repair then handles **every** remaining actual adversary
branch, including same-player multiple picks and early termination. Original-prefix
ownership is retained in `full_history_schedules`, not reset at the repair entry.

Two stricter controllers fail:

1. **Resume common-counter copying at the repair entry.** The legal full paths
   actual `[2,5,11,6,9,10]`, shadow `[5,2,7,11,6,10]` complete to margins `2` and `10`.
   Thus `2 < 10-2`. The shadow still wins; copying has needlessly increased the
   margin the actual game is obliged to match. `copied_suffix_margin_obstruction`
   certifies legality, terminality, both margins, and the failed inequality.
2. **Always take the maximum after the forced actual opening `2`.** The legal
   actual path `[2,11,10,5,9,6]` follows that protected policy and completes to
   protected margin `-2`. `global_max_policy_obstruction` certifies the policy
   predicate as well as the loss. This blocks extending the small repair unchanged
   to the root; it does not refute a richer two-buffer controller.

The constructive distinction is to choose the shadow opponent's response to keep a
small, forced winning margin, rather than mechanically mirror the actual opponent.
This is permitted: the supplied shadow strategy must win against every opponent,
whereas the actual opponent's actions remain universally quantified.

## Exact computation and trust boundary

`score_debt_repair_probe.py` uses integer scores, actual player identities, and tuples
of distinct counters. A pick is legal only from a nonterminal state with that counter
present. Ties switch players. Each branch records permanent ownership. The controller
uses only maximum selection on protected turns and explicit shadow picks; it never
queries minimax to select a repair transition.

The old exact recurrence and independent unpruned recurrence are used only to recheck
the mandatory root move profiles. Regression replays cover all four actual leaves for
each `k=0,...,100` (404 leaves). A separate exhaustive completion/parity check covers
386 terminal states with support contained in `{1,...,6}`, both mover identities,
and deficits from zero through `sum(S)+3`. Every replay asserts legality, persistent
ownership, exact ledger updates, atomic width-two bounds inside the repair, and the
final inequality. These checks support the encoding; the parametric theorem rests
on Lean, not these finite samples. No large tables were regenerated.

Finite Lean certificates use `decide +kernel` and the existing proved classifier.
The structural repair and completion proofs do not use outcome lookup tables.
Although the repository's conjecture statement is imported transitively for its
definitions, collecting all transitive axioms rejects its `sorryAx`; it is not used
as a premise or through a circular reduction.

## Exact remaining gap

The main unresolved obligation is a causal structural controller from every admissible
initial adjacent-hole pair, covering every actual opponent choice, that reaches this
or another proved repair family while remaining consistent with an arbitrary supplied
shadow winning strategy. No general closure or repayment-success assumption is added.
The original root's branches other than the displayed actual second pick `5` remain
outside this repair proof. Even the displayed branch is not a parametric interval-entry
theorem. Boundary openings and the other direction needed for tied residual draws remain
separate obligations.

## Reproduction and handoff

From this checkout:

```bash
python3 -B scripts/catch_up/score_debt_repair_probe.py
lake --wfail build catch_up.CompletedMargin catch_up.ScoreDebtTerminalRepair catch_up.ScoreDebtRepairCertificates catch_up.ScoreDebtRepairAudit
git diff --check
```

The next bounded task should try to derive a **new structural entry/repair phase**
for the mandatory actual branch beginning `[2,11]`, using this max-policy obstruction
as the first falsification test. Keep the current three-counter terminal gadget as
a proved leaf. Do not promote it to a global invariant or enlarge the unmatched
buffer without a concrete new mechanism. A general construction would still need
arbitrary-`N,b,y` entry and transition closure, not just a solution of the finite root.

## Independent review

Exactly one independent reviewer was used, after a complete candidate existed. The
same reviewer checked the completed follow-up additions. Final verdict: **PASS**,
with no remaining required fixes. The reviewer independently rebuilt all four
modules, ran the 31-theorem axiom audit and Python replay, and checked arbitrary
strictly winning shadow-strategy consistency. The wording above retains its scope
caution: the counterexample is to **pick 2 first, then always take the maximum**.

The first review caught an imprecise schedule comment and requested preservation of
the original ownership prefixes. Both were corrected before the final pass. No
other research agent was launched. Local commit metadata is recorded in Git. No push,
merge, or remote repository mutation was performed. All seven additions are new files;
no previous report, certificate, or source file was modified. There are no unfinished
Lean experiments in the committed sources.

The checkout is `HISTORICAL_TMP/catchup-score-debt-20260928`. The local branch and commit
are stored in the shared Git repository at `SOURCE_CHECKOUT`,
so the committed report and proofs remain recoverable even if the temporary checkout
is later removed. No cleanup of unrelated worktrees or user files was performed.
