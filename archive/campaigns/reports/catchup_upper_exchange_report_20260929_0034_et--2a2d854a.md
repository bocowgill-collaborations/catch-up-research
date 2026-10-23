> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Catch-Up upper exchange and fourth-from-top endpoint

## Verdict

**Target B is proved, in a stronger form than requested. Target A and the
general Catch-Up conjecture remain open.**

The new Lean theorem proves

\[
N\ge15\quad\Longrightarrow\quad
\operatorname{value}\bigl(Q_N(N-3)\bigr)\ne\mathrm{loss}.
\]

This statement needs neither even triangular total nor a smaller-instance
draw hypothesis. Four small kernel checks cover the additional admissible
sizes 11 and 12. Consequently,

\[
N\ge11,\quad \operatorname{Even}(N(N+1)/2)
\quad\Longrightarrow\quad
\operatorname{value}\bigl(Q_N(N-3)\bigr)\ne\mathrm{loss}.
\]

The requested implication from a draw after opening one in size N-4 therefore
follows immediately, but its draw hypothesis is unnecessary. The audit module
states that implication verbatim in set-difference notation.

The proof also establishes all three upper-opening exclusions in Target A
when **b=N-3**. It does not establish Target A for general b.

## Repository and scope

- Base: `d016a035`, the newest local descendant located at the start.
- Branch: `codex/catchup-upper-exchange-20260929`.
- Checkout: `HISTORICAL_TMP/catchup-score-debt-20260928`.
- Start: September 29, 2026, **00:09:27 EDT**.
- Maximum deadline: **02:39:27 EDT**; the substantive proof and its review
  completed well before that limit, and the session moved to preservation early.
- The initial research checkout was clean. No existing report or certificate
  was edited. The separate main checkout and its unrelated untracked file were
  left untouched. No push or merge was performed.
[Administrative account detail omitted.]
- One independent conceptual helper and one subsequent independent reviewer
  were used, sequentially. At most root plus one agent was active.

The selected prior reports and August closure obligations were consulted, not
the entire archive. The old reserve-budget mechanism was not reopened.

## Proof mechanism

Put m=N-5 and

\[
R=[2,m]\cup\{m+3,m+4,m+5\}.
\]

A hypothetical loss of Q_N(N-3) has the available exact-deficit counter N-4.
The existing `DeficitWinningBound` API forces a winning tied opening in R,
strictly above N-3. It must be one of the three displayed top counters.

The new argument rules out each one using a finite **exact-sum forcing tree**.
At a losing position (S,d), choose a positive block A contained in S with
sum(A)=d. `ExactSumLossObstruction` forces a losing post-opening state
after deleting A, whose opening w exceeds every member of A. The support and
this strict bound leave only the branches listed below.

This does not compare winners on different supports. It follows each forced
support separately until reaching a contradiction. At a terminal proof-tree
node, an exact-deficit block contains the largest remaining counter, leaving
no possible forced larger opening.

### Symbolic tree for m>=11

1. **Opening m+5:** choose `{2,m+3}`. The only forced opening is m+4.
   The remaining support is `[3,m]`, deficit m+4; the dominating block is
   `{4,m}`.

2. **Opening m+4:** choose `{4,m}`. The forced opening is m+3 or m+5.
   - At m+5, `{2,m+3}` is a dominating exact block.
   - At m+3, choose `{5,m-2}`. The forced opening is m-1 or m+5.
     - At m+5, `{6,m-1}` is a dominating exact block.
     - At m-1, choose `{2,m-3}`. Only m+5 can be forced next.
       Its support is `[3,m-4]` minus `{4,5}`, deficit m+5.
       The dominating block is `{3,6,m-4}`.

3. **Opening m+3:** choose `{3,m}`. The forced opening is m+4 or m+5.
   - At m+4, choose `{5,m-1}`, forcing m+5. The support is
     `[2,m-2]` minus `{3,5}`, deficit m+5, with dominating block `{7,m-2}`.
   - At m+5, choose `{6,m-1}`, forcing m+4. The support is
     `[2,m-2]` minus `{3,6}`, deficit m+4, with dominating block `{2,4,m-2}`.

Interval geometry enters through the actual availability of these small
complements and the short, fully enumerated upper tail. Every claimed sum,
distinctness condition, support membership, and remaining upper alternative
is checked parametrically in Lean.

### Boundary repair and small cases

The last branch of the middle-opening tree cannot use `{3,6,m-4}` at m=10:
it would repeat counter 6. Instead, before the next exact-sum choice, the state
is `({2,3,6,7,15},9)`. Take **2, then 6, then 15**. The preparation sum is
8<9, so neither first pick catches. The final pick transfers the move at
deficit 14 with only `{3,7}` remaining. Its sum 10<14 makes it a terminal loss
for the opponent. This repair uses `CompletedTurn`, not an assumed strategy
or retrospective score assignment. It extends the parametric result to N=15.

The first/last opening proofs already work at m>=10/m>=6 respectively. For
11<=N<15, even triangular total leaves only N=11 and N=12. The first and middle
openings at these two sizes use the existing `CanAvoidLossClassifier` soundness
theorem and **four `decide +kernel` checks**, each with at most eight remaining
counters. The last opening remains symbolic.

Existing certificates were considered first. The inspected N11 interval certificate
uses native evaluation, which was not imported into the new theorem's dependency closure. No enlarged table,
new controller, or assumed numerical annotation appears in this proof.

## Target A: exact remaining gap

Alternative exact-sum blocks do not themselves yield winning openings of the
same tied position. I examined the natural common-support repair: take disjoint
blocks A and B of sum d, and suppose a forced winning opening w after A lies
outside A union B and exceeds d. Delete B as a subdeficit preparation.

Writing H=S minus (A union B), the resulting loss is at

\[
(H\setminus\{w\},\,w-d).
\]

Thus w is a winning catching move of **(H,d)**, not a winning opening of (H,0).
If the initial post-opening state can catch, the preparation is legal; if it
cannot, subtracting d from both available sum and deficit proves the derived
state terminal and losing directly. The value inference is valid in both cases.

The tied-root uniqueness theorem cannot be used on this positive-deficit parent.
For example, `({6,7,8},3)` has even effective total 24 and all three catches win.
Their two-counter children `({7,8},3)`, `({6,8},4)`, and `({6,7},5)` all lose.
This is a reviewed paper-level diagnosis, not a formal counterexample to Target A:
the example is not claimed to have Target A's dense ancestry.

What is missing is an actual transfer to a common **tied** support, or a closed
parametric family for a decreasing exact-sum forcing argument when the upper
tail has arbitrary length. No such transfer or closed family was proved here.
The proof tree above closes the three-top-counter family instead.

The independent helper also considered odd unions of actual adjacent pairs
at deficit one. That auxiliary invariant remains unproved. Its dominant-pair
terminal-utility observation is saved, explicitly unformalized and outside the
certified result, in `research/upper-exchange-20260929/SIDE_IDEA.md`.

## Verification and review

Production files:

- `scripts/catch_up/LowerRayFourthEndpoint.lean`
- `scripts/catch_up/LowerRayFourthEndpointAudit.lean`

Warning-strict affected-scope commands passed:

```text
lake --wfail build catch_up.LowerRayFourthEndpoint
lake --wfail build catch_up.LowerRayFourthEndpointAudit
```

The audit checks all new public theorems transitively, including the exact
set-difference statement, requested transfer, and upper-opening specialization.
Every axiom list contains only **propext, Quot.sound, Classical.choice**.
There is no `sorryAx`, native-evaluation axiom, new axiom, or dependency on the
open conjecture. As a negative control, applying the same whitelist to the
repository's existing open conjecture failed with `Unexpected axiom ... sorryAx`.

The independent reviewer approved the statement, every symbolic branch,
terminal cases, small-case coverage, polarity, and source dependency paths.
Its full findings are preserved in `research/upper-exchange-20260929/REVIEW.md`.

One targeted Python diagnostic checked the exceptional endpoint claims and the
specific m=10 intermediate state, reusing the existing exact recurrence. It
ran in about 0.04 seconds. The intermediate state was cross-checked against
absolute-score play. Its checker and output are preserved alongside the report.
Together with the helper's small diagnostics, new exploratory exact computation
used far less than one minute of the fifteen-minute allowance. These diagnostics
are evidence only; the theorem rests on Lean proofs and kernel checks.

## Effect on the campaign and next action

This closes one previously open lower-ray nonloss endpoint and does so without
an induction hypothesis. The old certified interval frontier through N=28 is
unchanged; the result is an infinite parametric theorem, not a frontier extension.

Remaining obligations include:

- The first-pair endpoint `Position(Icc 3 N,1)` and its required outcome directions.
- Lower-ray interior nonloss for b from 3 through N-4, subject to the campaign's
  exact hypotheses. The b=N-2 endpoint still has its earlier smaller-draw transfer;
  the top two endpoints already have unconditional nonloss results.
- The other ray and the nonwinning obligations in the August closure package.
- General Target A. Neither these partial exclusions nor the new endpoint prove
  that every punctured residual draws or that Catch-Up is solved.

**Recommended next action:** investigate whether this finite exact-sum forcing
tree has a uniform upper-tail induction. Write the family as
`[2,m] union [m+3,m+k+2]`; k=3 is now certified. Use k=4 as the next concrete test,
but seek an explicit support class closed under the exchanges and a decreasing
rank. Every terminal leaf must have a proved exact-block obstruction or a legal
completed-turn repair. Do not substitute a global residual-nonloss assumption
or enlarge outcome tables. The difficult lower-b region must remain an explicit
separate obligation unless that induction genuinely reaches it.

Completed work is preserved on the new local branch. No push or merge is part
of this session.

Main proof/report commit: **3b7e47fd**, created at approximately 00:44 EDT,
about 35 minutes after the session began. It adds ten files and changes no prior
report, certificate, or source. The working tree was clean immediately afterward.
Final gate/preservation notes are recorded in a subsequent local commit.
