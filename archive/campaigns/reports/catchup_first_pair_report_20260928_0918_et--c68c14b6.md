> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Catch-Up first-pair investigation — September 28, 2026

## Verdict

The uniform first-pair endpoint remains **open**. This run does not solve Catch-Up,
prove a new unbounded interval family, or advance the certified frontier.

It rigorously diagnoses one attempted loss-derived strategy steal:

1. Removing three gives the correct winning shadow under a hypothetical endpoint loss.
2. A transfer that remembers only the extra counter three, score difference, minimum
   counter, parity, and the simultaneous winning first-pick continuations is false.
   A new eight-counter sparse witness satisfies those conditions and loses.
3. Copying common counters can fail on legal prefixes from the size-eight interval
   positions, before counter three is selected. The exact failure is an ownership
   change at a tie, not a subtraction error or insufficient terminal compensation.

The sparse obstruction excludes a geometry-free transfer even with adaptive choices.
The size-eight obstruction excludes the stated copying rule, not every adaptive or
loss-conditioned coupling. Neither is a counterexample to the requested endpoint.

## Scope and preservation

- Start: **09:18:58 EDT**; hard stop: **10:18:58 EDT** on September 28.
- Base: `fbce0be86588dd31d7423ae1b026b2b618714e3a`, the latest available local
  campaign branch containing the requested commit.
- New branch: `codex/catchup-first-pair-20260928`.
- Checkout: `HISTORICAL_TMP/catchup-score-debt-20260928`.
- Read the September 28 two-buffer report, August exact-closure and blocked-route
  sections, and September 23 endpoint obligations. Inspected the requested transition,
  completed-turn, exact-deficit, and completed-margin APIs before adding code.
- Existing reports, certificates, and tracked sources are unchanged. Only new files
  belong to this run. No controller table was extended and no large table was regenerated.
- One independent reviewer was used after a complete candidate existed. The same reviewer
  checked the final refinement. No other research agents were launched.
- Completed artifacts are committed locally. **No push or merge was performed.**

## Exact target and checked entry point

The target is

\[
 N\ge7,\quad \operatorname{Even}(N(N+1)/2)
 \quad\Longrightarrow\quad
 \operatorname{value}(P_N)\ne\mathrm{loss},
 \qquad P_N=\langle\{3,\ldots,N\},1\rangle.
\]

Lean proves `root_eq_pair`: this is exactly `pairDeletionPosition N 1 2`,
including the small/empty interval boundary cases. It is not the original tied root.

Values are measured from the current mover. Every available first pick `x >= 3`
catches immediately and switches players:

\[
 (I_{3,N},1,p_1)\xrightarrow{x}
 (I_{3,N}\setminus\{x\},x-1,p_2).
\]

The proof of `deficit_one_loss_child_win` checks nonemptiness and catchability using
the available positive counter. It then uses the actual best-move recurrence and
negation. Consequently a losing `P_N` forces **every** first-pick child to win.
This is formalized in `loss_forces_all_first_children_win`.

In particular, taking three gives the normalized shadow
`Position(Icc 4 N, 2)` (`shadow_after_three`). To steal its strategy, the shadow's
winning mover is relabeled as the protected player in the separate actual game.
Player identities are then fixed within each game; they cannot be swapped later.

Direct kernel evaluation proves `P_7` and `P_8` draw. These are endpoint certificates,
not deductions from certificates that only say the original interval root draws.

## Attempted mechanism: suspend counter three

Compare actual `U = (S,1,p1)` and shadow `V = (S.erase 3,2,p1)`, with minimum counter
three. The initial protected score balances are `-1` and `-2`, so actual has a
one-point advantage. The proposed arithmetic/history invariant was:

- remaining supports agree apart from the still-unmatched counter three;
- common counters already selected have the same owners in both histories;
- while movers agree, the protected score-balance difference remains one.

Copying a common counter with the same owner preserves that balance by the existing
`signed_picks_balance` ledger. If common ownership could be preserved through
completion, assigning the extra three to either player would change the difference
to `1+3` or `1-3`. Thus the proposed terminal bound would be
`completedMargin(U) >= completedMargin(V)-2`. An even-total shadow win would suffice
for actual nonloss by the existing `completed_margin_transfer` theorem.

This calculation is conditional. It supplies **no right to control ownership of the
extra three, no repair at a mismatched turn, and no strategy closure proof**.
No outcome lookup was used as the definition of the proposed invariant.

### Swapping opening choices does not remove the debt

The new `raw_two_pick_exchange` theorem records the precise discrepancy. For
`1 <= x` and `x+1 < y`, raw updates from `(S,1,p1)` give:

\[
 [x,y]\longmapsto(S\setminus\{x,y\},y-x+1,p_1),
 \qquad
 [y,x]\longmapsto(S\setminus\{x,y\},y-x-1,p_2).
\]

The deficits differ by two and the movers differ. These are raw-update identities;
the theorem intentionally does not assert that an arbitrary support permits the
second pick before termination. The tied-opening commutation theorem cannot simply
be reused as if these were the same normalized position.

## Decisive obstruction to the geometry-free transfer

Let

\[
 S_* = \{3,7,9,14,17,20,29,34\}.
\]

Its sum is 133, its minimum is three, and its deficit-one effective total is 134.
Lean certifies

\[
 \operatorname{value}(\langle S_*,1\rangle)=\mathrm{loss},\qquad
 \operatorname{value}(\langle S_*\setminus\{3\},2\rangle)=\mathrm{win}.
\]

Moreover, **all eight first-pick children win**, by `sparse_all_first_children_win`.
Thus retaining the simultaneous winning-continuation obligations does not repair an
argument that discards interval geometry. `sparse_has_no_nonloss_strategy` translates
the failure directly into the repository's strategy semantics.

The exact refuted statement is `no_geometry_free_three_reserve_transfer`:

```text
NOT (for every finite S,
  3 in S and every x in S is at least 3 and Even(1 + sum S)
  and value(Position(S.erase 3, 2)) = win
  imply value(Position(S, 1)) != loss).
```

This rules out every purported all-support transfer with only those hypotheses,
regardless of buffering or asynchronous scheduling. It does **not** rule out a
transfer that uses the intact interval or additional inherited history restrictions.
`S_*` is not an interval, and no claim of a smallest counterexample is made.

Independent exact computations give completed-margin minimax values `-2` and `+2`.
These numerical margins are computational evidence; the decisive loss/win outcomes
and absence of an actual nonloss strategy are kernel-certified Lean theorems.

## Exact common-counter failure at size eight

Start the actual and shadow post-opening games at

```text
actual: (Icc 3 8, deficit 1, p1)
shadow: (Icc 4 8, deficit 2, p1).
```

The common legal prefix `[5,7]` reaches

```text
actual: ({3,4,6,8}, deficit 3, p1)
shadow: ({4,6,8},   deficit 4, p1).
```

Both bridge positions win. The only winning shadow pick is eight. Copying eight
loses in the actual game; actual can instead win by taking six.

The earliest failed ownership transition is explicit:

| Common suffix played | Actual state | Shadow state |
|---|---|---|
| `[8]` | `{3,4,6}`, deficit 5, p2 | `{4,6}`, deficit 4, p2 |
| `[8,4]` | `{3,6}`, deficit 1, p2 | `{6}`, deficit 0, p1 |
| `[8,4,6]` | `{3}`, deficit 5, p1; terminal | empty, deficit 6, p2; terminal |

After four, shadow has switched at equality but actual's opponent remains behind
by one. That opponent can take six, rather than the unmatched three. In shadow,
six belongs to the protected player. The proposed repayment cannot be claimed
retrospectively: the counter has opposite owners.

Actual stops early with three still available. Notionally awarding it to the
trailing protected player gives completed margin **-2**; shadow's margin is **+6**.
Hence `6-2 <= -2` is false. `bridge_completed_copy_obstruction` kernel-certifies
both legal traces, terminal conditions, and these exact margins.

**Essential limitation:** actual's bridge wins, and the shadow interval root draws
(`bridge_shadow_root_draw`). This prefix is not certified as a prefix of a supplied
strictly winning shadow strategy from that root. It does not occur as a losing
actual state maintained against a winning opponent. It therefore refutes the
unconditional copying closure, not a refined loss-conditioned coupling.

## Bounded checks and trust boundary

New Lean files:

- `scripts/catch_up/FirstPairDescentObstruction.lean`: 23 public theorems.
- `scripts/catch_up/FirstPairDescentAudit.lean`: transitive axiom whitelist audit.

Verification passed:

```bash
lake --wfail build catch_up.FirstPairDescentAudit
python3 -B research/first-pair-20260928/first_pair_probe.py
```

Only the changed scope and its dependencies were built. Finite certificates use the
existing proved one-sided classifier and `decide +kernel`. The audit allows only
`propext`, `Classical.choice`, and `Quot.sound`: no `sorryAx`, new mathematical axiom,
native-evaluation trust axiom, or transitive use of the Catch-Up conjecture occurs.
Importing the statement module does not itself make its unproved conjecture a dependency.

The saved Python checker compares normalized completed-margin evaluation with an
independent absolute-score recurrence that omits early termination. It verifies every
legal first move at the principal witnesses and directly replays player identities
through the copied suffix. Its use of optimal outcomes is diagnostic only.

Additional bounded evidence, not new general theorems:

- Direct exact endpoint checks at `N = 7,8,11,12` all give margin zero. Only seven and
  eight are newly certified here in Lean.
- All 180 odd-sum intervals `[a,b]` with `1 <= a <= 30` and length at most 12 are
  nonlosing at deficit one. This does not establish the stronger interval conjecture.
- Greedy minimum play fails already at `N=7`: legal play `[3,7,4,5,6]` ends with
  protected score 12 against 14. The first pick three itself is not the problem.
- A general tied-win-to-deficit-two-nonloss shortcut also fails computationally on
  `{1,6,11,14,15,18,23}`. This auxiliary example does not satisfy the minimum-three
  restriction and is not a separate Lean result of this run.

The independent reviewer approved the final statements, exact terminal counterplay,
replay checker, warning-strict build, and all 23 axiom checks. Its qualifications
about the bridge's scope are retained above. See `research/first-pair-20260928/REVIEW.md`.

## Exact gap and next-run judgment

The unresolved target is still the original unbounded statement about `P_N`.
The work above does not transform it into a proved smaller-parameter descent.
No invocation of a least counterexample, `N -> N-4` lift, opening-one draw hypothesis,
or unrestricted punctured-set nonloss was used.

The loss-derived route is not refuted, but **another run on the same geometry-free
score-debt abstraction is not justified**. A new run should begin with a specific
interval/history condition that excludes the sparse witness and survives the exact
ownership transition above. The hypothetical-loss assumption may exclude some bad
prefixes, as it excludes the winning actual bridge; that observation alone is not
an invariant or a legal repair rule. No such new closure mechanism was found here.

The repository's larger obligations remain:

1. **First-pair nonloss:** `A(N,2) = P_N` is still unresolved uniformly.
2. **First-pair draw:** even proving nonloss would leave the separate nonwin direction.
   The general family `B(N,x) = Position((Icc 3 N).erase x, x-1)` controls that direction.
3. **Other endpoint:** `B(N,3) = Position(Icc 4 N,2)` still needs its separate nonloss
   obligation in the August normal form. Nonloss of `P_N` needs some `B(N,x)` to be
   nonwinning; it does not provide this `B(N,3)` nonloss condition.
4. **Interiors:** direct lower-ray nonloss for `3 <= b <= N-3` remains unresolved.
   In the August normal form, `TA(N,b)` nonwin for `3 <= b <= N-2` and `TB(N,x)`
   nonwin for `4 <= x <= N-2` remain open for admissible `N >= 31`. Here
   `TA(N,b) = (Icc 2 N).erase (b-1) |>.erase b` and
   `TB(N,x) = (Icc 3 N).erase (x-1) |>.erase x`.
5. **Upper endpoints:** existing nonloss results at `A(N,N)` and `A(N,N-1)` are unchanged.
   `A(N,N-2)` remains conditional on a proved opening-one draw at size `N-4`; this run
   does not discharge that premise or supply its induction.

The original interval draw certificates through 28 and all previous reports are preserved.

## Reproduction and files

The diagnostic generator has no random choices in its saved replay:

```bash
python3 -B research/first-pair-20260928/first_pair_probe.py \
  --output research/first-pair-20260928/results.json
lake --wfail build catch_up.FirstPairDescentAudit
```

`results.json` records the exact sets, deficits, move margins, fixed-player traces,
and bounded interval sweep. `verification.txt` preserves the scoped build/axiom output.
`GATES.md` records acceptance evidence. No incomplete Lean experiment was added to
production sources, and no existing report was overwritten.
