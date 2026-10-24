> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Catch-Up: uniform descent and adjacent-pair geometry

## Verdict

Catch-Up remains open. This run proves a new unbounded endpoint and a small,
parametric geometric repair theorem. It does not prove uniform exact-sum descent,
the arbitrary-odd-pair candidate, or the unbounded first-pair draw. The interval
certificate frontier remains 28.

The strongest new lower-ray conclusion is

\[
 N\ge23\quad\Longrightarrow\quad
 \operatorname{value}\left(\operatorname{Position}
   (I_N\setminus\{1,N-4\},N-5)\right)\ne\mathrm{loss}.
\]

This has no parity assumption, smaller-instance hypothesis, or conjecture dependency.
It is a **single endpoint**, not a uniform theorem in the deleted counter.

The positive pair result is also genuinely parametric:

\[
 a\ge3,\quad b\ge a+2,\quad c\ge b+2,\quad b\ge2a-1
 \quad\Longrightarrow\quad
 \operatorname{value}(\{a,a+1,b,b+1,c,c+1\},1)=\mathrm{draw}.
\]

Without the separation hypothesis, this six-counter state is proved nonwinning.
In particular, every support \(\{3,4,b,b+1,c,c+1\}\), with \(b\ge5\) and
\(c\ge b+2\), draws at deficit one. Counter sizes and gaps are unbounded;
**the number of pairs is exactly three**. This covers only the already-known
\(P_8\) among the first-pair interval states.

## Session and preservation

- Start: September 29, 2026, **08:43:29 EDT** (12:43:29 UTC).
- Hard deadline: **12:13:29 EDT** (16:13:29 UTC), 210 minutes after start.
- Base: `faad9dccf6723b46fc252cbdaebf337427809044`, the latest available local
  descendant of the requested commit. The research worktree was initially clean.
- Branch: `codex/catchup-uniform-descent-20260929`.
- Checkout: `HISTORICAL_TMP/catchup-score-debt-20260928`.
- Prior reports, certificates, and tracked sources are preserved unchanged.
  The unrelated main-checkout untracked file was not touched.
- One bounded conceptual helper was followed by one independent reviewer. The
  reviewer was reused for completed candidates; at most root plus one helper
  were active. Review artifacts are retained in the research directory.
- All work is local. **No push or merge was performed.** Final commit and
  clean-state evidence are recorded in the preservation ledger and final reply.
- Research artifacts were committed as `e293017b`; a following documentation
  commit records the clean-state checks. Preservation concluded around
  **10:15 EDT**, approximately 92 minutes after start and before the maximum.
  Both targets were investigated; the run ends with the precise recursive gaps
  below. Administrative stopping details are omitted.

Read the requested upper-exchange, certificate-complexity, and first-pair reports
and the August exact-closure section. Inspected the requested exact-sum,
completed-turn, winning-bound, exact-deficit, and pair-deletion APIs. The explicit
strategy-DAG lower bound was not interpreted as a symbolic proof-length bound.

## Parent proof accounting

The existing closure theorem is
`value_Icc_eq_draw_of_lower_pair_deletion_nonloss`:

\[
 \bigl[\forall b\in[2,N],\ \operatorname{value}(Q_N(b))\ne\mathrm{loss}\bigr]
 \ \land\ \operatorname{value}(Q_N(2))=\mathrm{draw}
 \quad\Longrightarrow\quad \operatorname{value}(I_N)=\mathrm{draw}.
\]

Here \(Q_N(2)=P_N=([3,N],1)\). Upper-opening exclusion establishes only the
nonloss part for the applicable \(b\ge3\), through
`pair_deletion_position_value_ne_loss_of_upper_residuals`. It does not supply
the extra first-pair draw. No use is made of the open Catch-Up theorem itself.

The August normal form still has these unbounded obligations, for admissible
\(N\ge31\):

1. \(A(N,2)\) is nonlosing.
2. \(\operatorname{value}(TA(N,b))\ne\mathrm{win}\) for \(3\le b\le N-2\).
3. \(B(N,3)\) is nonlosing.
4. \(\operatorname{value}(TB(N,x))\ne\mathrm{win}\) for \(4\le x\le N-2\).

The notation and sufficient closure are unchanged from the August report. The
new endpoint proves a particular \(A\)-state nonloss directly; it does not prove
the whole tied-residual condition in item 2. None of these four full families
is closed by this run. Both first-pair outcome directions remain open uniformly,
and the \(N\equiv3\pmod4\) first-pair class is not covered by the odd-pair bridge.

## Target A: what the exact-sum trees prove

For

\[
 F_{m,4}=[2,m]\cup\{m+3,m+4,m+5,m+6\},
\]

all four upper openings are proved nonlosing for every \(m\ge17\).
The four public theorems are `upper_quadruple_first_opening_ne_loss`,
`upper_quadruple_second_opening_ne_loss`, `upper_quadruple_third_opening_ne_loss`,
and `upper_quadruple_last_opening_ne_loss`.

At each node, a hypothetical loss and an available positive exact-sum block
force a losing post-opening position at some counter strictly above the block's
maximum. The proof handles **every** remaining counter satisfying that bound.
Leaves use exact blocks whose maxima dominate all remaining possible witnesses.
All block memberships, distinctness, subtractions, and outcome polarities are
checked in Lean. No comparison of different tied residuals by uniqueness occurs.

The saved forest has 35 exact-sum nodes, 14 dominating leaves, and maximum depth
five. Its blocks consist of small counters at most 11 and affine large counters
at least \(m-5\). The bound \(m\ge17\) separates these strictly: \(m-5\ge12\).
The symbolic replay verifies this arithmetic for all such \(m\), not just sample
values. At \(m=16\), a potential collision between a small 11 and a large
\(m-5=11\) invalidates this certificate. It does not refute the outcome theorem
below the stated bound.

Putting \(N=m+6\), \(b=m+2=N-4\), the residual is exactly
\(R_{N,b}=F_{m,4}\). The exact-deficit bridge therefore proves the displayed
endpoint for \(N\ge23\). `FifthEndpointAudit.set_difference_form` verifies the
statement using the user's explicit set-difference notation.

This is a completed finite forcing forest with a symbolic size parameter. Its
strict deletion of counters gives well-foundedness, but it does **not** provide
a family of certificates closed as \(k\) grows. No such closure was found.

### Uniform obstruction to keeping all witnesses in the upper tail

The formalized obstruction applies to every \(m\ge6,k\ge2\). Define an
upper-only exact block by requiring every witness permitted by membership and
the strict maximum bound to lie in the original upper interval.

After opening \(m+4\):

1. No upper counter can enter an exact block of sum \(m+4\): \(m+3\) would
   require the absent counter 1, and the other upper counters are too large.
2. To prevent the lower maximum \(m\) from being a permitted witness, the
   block must contain \(m\). Its complement must sum to four.
3. With distinct counters at least two, the only such complement is \(\{4\}\).
   The first block is therefore forced to be \(\{m,4\}\).
4. The witness \(m+3\) remains permitted. At that descendant, an upper-only
   block must contain \(m-1\), again requiring a complement of four.
5. Counter 4 has been deleted; two distinct remaining positive counters are
   already too large. The second block cannot exist.

`first_block_forced`, `no_second_upper_only_block`, `forced_branch_available`,
and `no_two_upper_only_steps` establish this parametrically. The quantifier
is over **structurally permitted** witnesses. This does not assert that
\(m+3\) actually loses. A separate theorem excluding that witness would be a
new semantic mechanism, not a contradiction of this obstruction.

Allowing a lower witness can repair a fixed tree. For example, the known
sequence with blocks \(\{4,m\},\{5,m-2\},\{2,m-3\}\) returns to an upper
witness only after widening the gap and deleting the small reserve
\(\{2,4,5\}\). Its support is then

\[
 ([2,m-4]\setminus\{2,4,5\})\cup[m+5,m+k+2].
\]

It is not another member of the original two-hole family, and the same repair
cannot reuse counter 2. `INDEPENDENT_IDEA.md` records this exact transformation
and a paper proof of a sharp disjoint-complement packing bound. Those ancillary
derivations are not additional Lean-certified game-outcome theorems.

**Remaining Target A gap:** a residual family that admits lower intruders and
survives every permitted branch, with a proved resource invariant and terminal
closure. A decreasing counter count alone does not supply either property.
No nonloss theorem is claimed for arbitrary \(k\), nor for all small \(b\).

## Target B: actual geometry supplies a sharp local repair

For \(a\ge2\), \(b\ge a+2\), Lean proves

\[
 \operatorname{value}(\{a,b,b+1\},a+1)=\mathrm{draw},
\]

and the exact threshold

\[
 \operatorname{value}(\{a,b,b+1\},a-1)=\mathrm{draw}
 \quad\Longleftrightarrow\quad b\ge2a-1.
\]

Below that threshold the minus state wins. These are
`orphan_plus_draw`, `orphan_minus_draw`, `orphan_minus_win_of_close`, and
`orphan_minus_draw_iff`.

Taking the orphan \(a\) leaves an adjacent pair at deficit one, hence a draw.
At deficit \(a+1\) this is a **continued pick**; at \(a-1\) it catches and
switches. Taking \(b+1\) in the minus state leaves \(\{a,b\}\) at deficit
\(b-a+2\). This lies in the pair's losing interval exactly when
\(b\le2a-2\); once \(b\ge2a-1\), taking the lower counter is a legal
continued pick giving a nonlosing response. This explains the sharp geometric
threshold rather than merely fitting numerical outcomes.

The resulting proved bridges are:

- Two disjoint actual adjacent pairs form a drawn tied root when their minimum
  is at least two (`two_pairs_tied_draw`).
- At deficit two, two such pairs are nonwinning when their minimum is at least
  three (`two_pairs_deficit_two_nonwin`).
- Three pairs are nonwinning when their minimum is at least three, with arbitrary
  gaps (`three_pairs_nonwin`). Every first pick is covered.
- Three pairs are nonlosing when their minimum \(a\ge2\) and the second pair
  starts at least \(2a-1\) (`three_pairs_nonloss_of_separation`).

For the last claim, choose \(a+1\). The opponent's deficit is \(a\), and every
remaining counter catches it, so there are precisely five single-pick responses.
If the opponent takes \(a\), the residual is the proved tied two-pair draw.
If the opponent takes a higher counter, take its mate: the residual is one of
the proved orphan states at \(a-1\) or \(a+1\). This is a complete, causal
local repair. Its legality follows from the inequalities; it does not license
a fixed mate strategy for arbitrarily many pairs or later deficits.

### Why the tempting induction does not close

A blanket nonwinning orphan premise is false:

\[
 a\ge4\Longrightarrow
 \operatorname{value}(\{a,a+2,a+3\},a-1)=\mathrm{win}.
\]

Worse, for every \(a\ge6\), the smallest-upper pick \(a+1\) from
\(([a,a+5],1)\) loses. The opponent replies \(a+5\), leaving
\(\{a,a+2,a+3,a+4\}\) at deficit five; all four repairs lose.
`AdjacentPairGeometryObstruction.lean` proves this parametrically, including
legality and equality endpoints. It refutes that opening rule, not odd-pair
nonloss, which permits other first moves.

A broader parity/low-deficit induction also fails. Exact independent recurrences
give

\[
 \operatorname{value}(\{4,5,7,8,14,15\},3)=\mathrm{win},
\]

although the support is three actual adjacent pairs, the deficit is strictly
below its minimum, and deficit and pair count have matching parity. Taking 14
wins; 5 and 8 draw. This is reproducible computational evidence, not a newly
formalized theorem. Its role is to reject the specific proposed nonwinning
induction window. The even-pair deficit-two candidate itself was not refuted.

Restricting all pair starts to the same parity does not rescue a *draw* window:
\(\{6,7,10,11\}\) at deficit two loses. A weaker nonwinning version survived
the recorded bounded probe, but no closed proof mechanism was obtained.

Finally, `GapAccounting.lean` proves a precise warning about the proposed
multiple-pair orphan extension. For any finite \(T\), \(a\ge2\), \(a\notin T\),
and \(\sum T\ge1\), if both

\[
 \operatorname{value}(\{a\}\cup T,a-1)\ne\mathrm{win},\qquad
 \operatorname{value}(\{a\}\cup T,a+1)\ne\mathrm{win},
\]

then \(\operatorname{value}(T,1)=\mathrm{draw}\). Pick \(a\): the minus
case switches and forces nonloss of \((T,1)\); the plus case continues and
forces nonwinning. Thus proving both orphan hypotheses for arbitrary odd-pair
\(T\) already entails the desired draw for that family. The conditional theorem
is checked and independently reviewed, but **neither hypothesis is proved**.
They must not be relabeled a routine repayment condition.

## Computation and trust boundary

No interval outcome table or finite controller was expanded. New exact outcome
computation was used only to test named rules and consumed well under the
15-minute cap (under three minutes, including preservation reruns). Symbolic
block search manipulates exact affine sums, not optimal game values.

`PROBE_RESULTS.json` preserves final commands' results and output hashes.
The main odd-pair candidate survived a fixed 691-case baseline. An earlier
timed extension reached 722 cases without a loss; it is exploratory evidence,
not a certificate or proof of the unbounded candidate. Other no-counterexample
counts and exact tested families are stated in their scripts. No absence-of-
counterexample result is used as a Lean premise.

Every decisive Python counterexample is checked against both the existing
normalized recurrence and fixed-player absolute-score play, including its
first moves. Finite probe claims remain computational unless separately listed
above as Lean theorems. The symbolic forest has its own exhaustive witness
replay in `tree_replay.py`; the production Lean theorem remains authoritative.

Final checks:

```sh
lake --wfail build catch_up.LowerRayFifthEndpointAudit \
  catch_up.AdjacentPairGeometryAudit catch_up.UniformExactSumDescentAudit \
  catch_up.AdjacentPairGeometryRepairAudit
lake env lean -DwarningAsError=true research/uniform-descent-20260929/GapAccounting.lean
python3 -B research/uniform-descent-20260929/tree_replay.py
```

All pass. Only affected modules and required dependencies were targeted; the
repository-wide build was not requested. The four production audit modules
check 24 named declarations transitively, and the research accounting theorem
has its own audit. All admit only `propext`, `Classical.choice`, and `Quot.sound`.
There is no `sorryAx`, additional mathematical axiom, native-evaluation trust,
or transitive dependence on the open Catch-Up conjecture.

The intentionally failing `AxiomNegativeControl.lean` applies the same whitelist
to the existing open conjecture and is rejected specifically for `sorryAx`.
Its oracle requires that diagnostic as well as nonzero exit, not merely any
compilation failure. It is outside production sources. An initial ambiguous
monadic return type was corrected before the successful negative-control test.

Independent review passed for the endpoint, the uniform grammar obstruction,
the parametric pair-rule obstructions, all ten positive pair-repair declarations,
and the conditional gap-accounting theorem. See `REVIEW.md`,
`UNIFORM_OBSTRUCTION_REVIEW.md`, `PAIR_REVIEW.md`, and `REPAIR_REVIEW.md`.
The mathematical-research and proof-verification skill workflows enforced this
separation of proved outcomes, controller/grammar limitations, and open hypotheses.

## Next mathematical decision

The endpoint forest is worth retaining, but generating a longer forest for
\(k=5\) is not the best next primary target. The upper-only obstruction already
shows that a uniform proof needs a qualitatively different closure mechanism.

The most concrete positive lead is the sharp orphan threshold and the legal
three-pair repair. The next useful theorem would extend a **precisely stated
adaptive repair to unbounded pair count**, while allowing and handling the
winning deficit-three states rather than assuming them away. Alternatively,
an interval-specific invariant may exclude the sparse counterexamples, but it
must survive deletion of pairs and orphan creation. Both nonloss and nonwinning
must be accounted for; the anchor-three local result alone does not do this.

For upper descent, the corresponding needed theorem is a repeatable lower-
intruder exchange whose changing gap and deleted small counters have a proved
resource invariant. The explicit three-step transformation above gives the
first state that any such proposal must handle.

Do not promote either task to a proof by assuming residual nonloss, successful
repayment, eventual reentry, or the existence of a desired strategy. The current
gap is mathematical closure, not a need for more outcome data or a larger
explicit strategy certificate.
