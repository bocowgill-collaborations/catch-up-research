> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Catch-Up shifted-reply cycle investigation — September 28, 2026

## Verdict

**The endpoint and the general Catch-Up conjecture remain open.**

This run gives reproducible, Lean-certified obstructions to two specific local
cycle-breaking mechanisms. It does not prove full-interval acyclicity, refute it,
or extend the original interval certificate frontier.

1. **A full cycle span is insufficient.** There are legal directed two-cycles
   even when all integers between the cycle vertices are available. One witness
   is itself a losing deficit-one root. A second has an unused intermediate
   counter and directly refutes sliding the minimum cycle vertex through it.
2. **The tied-root maximum-companion exchange fails on an intact interval.**
   At `N=7`, vertex seven has exactly one winning reply. A parametric identity
   explains the obstruction: the critical counter `c-1` changes the relevant
   reply from winning to losing when the order is reversed.
3. **The bridge is correct.** A hypothetical endpoint loss forces an outgoing
   shifted reply at every vertex, hence a nonempty closed directed walk. This
   elementary reduction is not counted as closing the mathematical target.

The distinction between local span and global interval geometry is essential.
The sparse counterexamples below are not full intervals. The size-seven interval
example has no directed cycle and is not a hypothetical losing root.

## Scope and preservation

- Start: **10:21:12 EDT**, September 28, 2026. Hard cutoff: **11:21:12 EDT**.
- Base: `24e3488d`, the latest local branch containing the requested commit.
- Branch: `codex/catchup-shifted-cycles-20260928`.
- Checkout: `HISTORICAL_TMP/catchup-score-debt-20260928`.
- Read the previous first-pair report/review, August reply-graph and blocked-route
  notes, and the actual first-pick, reply-digraph, and completed-turn APIs.
- Existing reports, certificates, and tracked sources are preserved. This run
  adds new files only. No push or merge is authorized or performed.
- Only one independent reviewer is permitted, after this complete candidate.
  Final verification and preservation status is recorded at the end of this report.

## Exact graph and reduction

For a finite positive support `S`, define

\[
C_S(a)=\langle S\setminus\{a\},a-1\rangle.
\]

`Edge S a b` means all four conditions hold:

1. `a` belongs to `S`;
2. `b` belongs to `S.erase a`;
3. `C_S(a)` is nonterminal;
4. `C_S(a).moveOutcome b = win`.

The explicit terminal condition matters because `moveOutcome` is a total raw
update function, not itself a legality predicate. Values and move outcomes are
measured from their respective current movers.

For `P_N = Position(Icc 3 N,1)`, every available first pick catches and switches.
For `N >= 7`, its effective total is `1 + sum(Icc 3 N) = N(N+1)/2 - 2`,
so the requested triangular parity is exactly the even effective-total parity.
The previous `deficit_one_loss_child_win` therefore makes every `C_S(a)` winning
under a root loss. A win cannot be terminal: an empty normalized position is a
draw or loss, and an uncatchable position loses. The best-move recurrence supplies
a legal winning pick, yielding an outgoing edge at every vertex.

The new `loss_forces_closed_walk` and `interval_loss_forces_closed_walk` formalize
the finite-graph conclusion using `Relation.TransGen` on the finite subtype of
available counters. The latter requires `N >= 7`, but does not need parity.

**Formal scope:** these theorems produce a nonempty closed directed walk, not a
Lean `SimpleGraph` cycle. To extract a simple directed cycle mathematically,
choose a closed walk of least positive length. An internal repeated vertex would
give a shorter positive closed subwalk. Thus only the endpoints repeat. The
proved `edge_irrefl` excludes length one; length two is allowed and indispensable.

These vertices represent alternative initial branches. None of these cycles is
a cyclic sequence of actual play; actual play always removes counters.

## Candidate tested before search

Candidate H, recorded in `research/shifted-cycles-20260928/PLAN.md`, asserted:

> For a finite support with all counters at least three and even deficit-one
> effective total, a simple shifted-reply cycle cannot have its entire integer
> span contained in the support.

This is stronger than the intact-interval target. It isolates the proposed local
justification that all intermediate counters between the cycle extrema are
available. A proof would apply to every cycle on `Icc 3 N`. Its failure only
rejects this stronger local-span mechanism. H retains the effective-total parity,
not a separate triangular-total restriction on the maximum of a sparse support;
it must not be confused with the original full-interval hypotheses.

The associated proposed exchange slides the minimum vertex `a` of a two-cycle
`a → c → a` to the available counter `a+1`, preserving both edges. This would
reduce the span while preserving cycle length. It too is false.

## Obstruction 1: shortest two-cycle, even under a root loss

Let

\[
T_0=\{9,16,17,18,26,28,31,37\},\qquad S_0=\{3,4\}\cup T_0.
\]

Lean proves all of the following:

\[
\begin{aligned}
\operatorname{value}(T_0,0)&=\mathrm{loss},\\
\operatorname{value}(T_0,2)&=\mathrm{loss},\\
\operatorname{value}(S_0,1)&=\mathrm{loss},\\
3&\longrightarrow4\longrightarrow3.
\end{aligned}
\]

The support has minimum three, sum 189, and effective total 190. Its cycle span
`[3,4]` is fully present. Since there are no self-edges, this is a shortest possible
directed cycle. It refutes H even with an additional root-loss hypothesis; all
first-pick children consequently win as well.

The adjacent reversal identities explain why there is no contradiction. For
`a >= 1`, writing `T = (S.erase a).erase (a+1)`, Lean proves

\[
C_S(a).\operatorname{moveOutcome}(a+1)
  =-\operatorname{value}(T,2),\qquad
C_S(a+1).\operatorname{moveOutcome}(a)
  =-\operatorname{value}(T,0).
\]

Both orders switch: the reverse one catches exactly. Losses at deficits zero
and two give winning edges in both directions. The tied-root antisymmetry law
does not apply.

This witness has no strictly interior integer between its cycle vertices. The
next witness addresses that limitation separately; the two witnesses must not
be combined into one stronger claim.

## Obstruction 2: an actual intermediate counter does not provide the exchange

Let

\[
S_1=\{3,4,5,6,9,19,24,26,29,38\}.
\]

Its sum is 163, effective total 164, and the entire block `[3,6]` is present.
Lean certifies

\[
3\to5,\quad5\to3,\quad
C_{S_1}(5).\operatorname{moveOutcome}(4)=\mathrm{draw},\quad
C_{S_1}(4).\operatorname{moveOutcome}(5)=\mathrm{loss}.
\]

Thus the available intermediate counter four supplies neither required
replacement edge for sliding the minimum of `3 → 5 → 3` upward. The incoming
replacement draws and the outgoing replacement loses. This is the exact failed
transition, not an unspecified global compatibility gap.

The parametric `nonadjacent_reversal` identity gives, for `a+1 < b`,

\[
C_S(a).\operatorname{moveOutcome}(b)=-\operatorname{value}(T,b-a+1),\qquad
C_S(b).\operatorname{moveOutcome}(a)=\operatorname{value}(T,b-a-1).
\]

For the witness, `T = S_1 \\ {3,5}` wins at deficit one and loses at deficit three.
Independent absolute-score calculations give margins `+2` and `-2` respectively.

**Limitation:** exact computation gives `value(S_1,1) = draw`; that root outcome
is not a new Lean theorem here. This witness refutes the unconditional full-span
slide, not a slide restricted both to intact intervals and hypothetical root loss.
It also illustrates why cycle existence alone does not imply root loss.

## Obstruction 3: maximum-companion migration fails on the intact interval

For `S = {3,4,5,6,7}`, the exact move profile from `C_S(7)` is:

| Reply | Outcome | Computed completed margin |
|---|---|---:|
| 3 | win | +2 |
| 4 | draw | 0 |
| 5 | draw | 0 |
| 6 | loss | -2 |

Lean proves the edge `7 → 3` and the absence of every distinct companion edge.
It also certifies the following failed exchange. After `[7,3]`, the remaining
position is `({4,5,6},3)`; picking six wins. Reversing the order of these two
replies, `[7,6]`, instead reaches `({3,4,5},0)`, which wins for the new mover.
Thus six is a losing reply from `C_S(7)`, not a companion winning reply.

The precise parametric theorem is `critical_reply_inversion`. If `a ∈ S`,
`a+1 < c`, and

\[
\operatorname{moveOutcome}(\langle S\setminus\{c,a\},c-a-1\rangle,c-1)
 =\mathrm{win},
\]

then

\[
C_S(c).\operatorname{moveOutcome}(c-1)=\mathrm{loss}.
\]

Proof: the first displayed move outcome equals the outcome of taking `a` from
the tied residual `S \\ {c,c-1}`. In both orders the three-deletion state has
deficit `a` and its value is negated. That tied residual still contains `a`,
so it is nonterminal and the exhibited winning move makes its value win.
Taking `c-1` directly from `C_S(c)` catches exactly and switches to this winning
residual. Its move outcome is therefore loss. Every sign and terminal condition
in this deduction is checked in Lean.

The general theorem concerns raw move outcomes; membership of `c` and `c-1`
and nonterminality of `C_S(c)` must additionally be supplied when interpreting
it as legal play. All such conditions hold in the certified size-seven example.

The interval root at seven draws and its shifted graph is acyclic. This is not
a counterexample to a stronger exchange assuming that the maximum belongs to
a cycle or that the root loses. It refutes the unconditional companion step.

## Computation and reproducibility

`cycle_probe.py` uses the existing exact completed-margin recurrence and checks
edge signs independently with a tuple-based three-outcome recurrence. The latter
checks all edges for the six requested sizes and both new obstructions. Principal
residual margins are also replayed with absolute scores and no early cutoff.

| N | Winning edges | Cycles | Interpretation |
|---:|---:|---:|---|
| 7 | 4 | 0 | Nonvacuous |
| 8 | 5 | 0 | Nonvacuous |
| 11 | 6 | 0 | Nonvacuous |
| 12 | 0 | 0 | Vacuous |
| 15 | 0 | 0 | Vacuous |
| 16 | 0 | 0 | Vacuous |
| 19, holdout | 0 | 0 | Vacuous |

All seven endpoint margins are zero computationally. These are not seven new
Lean endpoint certificates. The holdout used 1,224,093 memoized margin states;
no table was exported or added to the existing frontier. The holdout graph did
not receive the separate tuple-recurrence check, unlike the six training sizes.

The mandatory controls are verified: `4 → 6` at `N=7`, and
`3 → 14 → 7 → 3` on the previous sparse support. All three sparse-cycle edges
and the single upward interval edge are checked against the actual Lean definitions.

The initial deterministic prefix-plus-two/three-tail scan found no filled-span
cycle in 6,585 eligible supports. This is weak bounded evidence, not a theorem.
The subsequent replayable searches found the decisive tails at zero-based trials
2197 (seed 928) and 530 (seed 92835). Neither witness is claimed minimal.

Reproduce the saved result and discoveries:

```bash
python3 -B research/shifted-cycles-20260928/cycle_probe.py \
  --discover-adjacent --output research/shifted-cycles-20260928/results.json
lake --wfail build catch_up.ShiftedReplyCycleAudit
```

Add `--search` only to replay the initial 6,585-support negative scan.
`discovery.json` preserves that earlier scan; `results.json` preserves the final
obstructions, profiles, graphs, holdout, and discovery seeds. The checker never
uses an outcome-derived rank as a structural invariant.

## Exact remaining gap and next-run judgment

No interval-sensitive cycle-breaking exchange survived this run. The following
claims remain unproved:

1. Acyclicity of the shifted graph on every admissible `Icc 3 N`.
2. Even the weaker condition actually needed: not every vertex has an outgoing
   winning reply on those intervals.
3. A local exchange using the full interval outside the cycle span, or using
   additional consequences of a hypothetical interval-root loss.

The certified counterexamples retire the local-span prohibition, its unconditioned
minimum-slide rule, and unconditional maximum-companion migration. They do not
retire every reply-graph proof. Merely assuming acyclicity, a compatible reply
selection, or a rank remains theorem-strength work, not progress toward a proof.
The next attempt would need an operation that genuinely uses counters outside
the cycle span or stronger simultaneous-branch information. No such operation
was discovered here; this report does not recommend another generic graph run.

Closing the first-pair nonloss endpoint would still leave its separate nonwin
direction, the `B(N,3)` nonloss obligation, the lower-ray interiors, and the
`TA`/`TB` nonwin obligations from the August normal form. The existing upper
endpoints and conditional antepenultimate endpoint are unchanged. All original
interval certificates through 28 are preserved.

## Final verification and preservation

- All **25 public theorems** passed the scoped warning-strict build and transitive
  axiom audit. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted;
  there is no `sorryAx`, new mathematical axiom, native-evaluation axiom, or
  transitive use of the unproved Catch-Up conjecture. The imported statement
  module is not itself a proof dependency on the conjecture.
- A source-to-audit inventory verified that all 25 public theorem names are
  audited exactly once. No placeholder or unfinished experiment was added to
  production Lean sources.
- The exact checker and both seeded discoveries replayed successfully. Saved
  artifacts are `results.json`, `discovery.json`, and `verification.txt`.
- The one independent reviewer returned **PASS** with no mathematical repairs,
  replayed the build/checker, and regenerated all ten saved graph records and
  both seeded discoveries. See `research/shifted-cycles-20260928/REVIEW.md`.
  The two requested documentation corrections were applied.
- Discovery stopped before the halfway point once the selected mechanisms were
  obstructed. The remaining work was verification and preservation. No affirmative
  endpoint proof is claimed by this report or its acceptance gates.

Local commit and final clean-state check: pending the final preservation step.
