> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Independent adjacent-pair repair review

Date: 2026-09-29. Reviewer owns only this report.

## Acceptance ledger

- [x] R1: Exact orphan and two-pair claims have the stated parameter coverage.
  EVIDENCE: All ten public statements inspected; no upper bound on the gaps is introduced. The minus threshold and its complement are exactly b≥2a−1 and b+2≤2a under a≥2.
- [x] R2: All continued picks, catches, equality switches, and terminal obligations are valid.
  EVIDENCE: Source audit of the elementary helpers and the orphan case splits; both continued-pick uses and all equality boundaries checked below. Every best-move recurrence receives a nonempty support and sum≥deficit.
- [x] R3: All three-pair replies are covered and the smallest-pair choice is used correctly.
  EVIDENCE: All five opponent replies after a+1, all six first moves in the nonwinning proof, and all four two-pair deficit-two branches checked below.
- [x] R4: Warning-strict affected build and transitive axiom audit pass.
  CHECK: lake --wfail build catch_up.AdjacentPairGeometryRepairAudit
  EXPECT: Build completed successfully
  EVIDENCE: Independent rerun after parent completion; exit 0, expected token matched, no warnings. CWD=HISTORICAL_TMP/catchup-score-debt-20260928; zsh launcher/direct child process; 2076 ms; SHA256(stdout+stderr)=a8dce7b19c2544533a972b9547acc1150f8eb0b9486226f27689c7810090d4f6; 1896 bytes. All ten declarations use exactly propext, Quot.sound, Classical.choice.
- [x] R5: Scope is exactly the stated three-pair endgame, not an arbitrary-pair or frontier theorem.
  EVIDENCE: The supports contain explicitly six distinct counters. The unrestricted result is nonwinning; nonloss/draw needs separation. No statement changes an N frontier or quantifies over arbitrary pair counts.

## Verdict

PASS. No substantive mathematical error or missing proof obligation found
within the stated claims. Five gates met; none unmet or abandoned. The
reviewer edited only this report and ran no new mathematical experiment.

## Exact coverage

For natural numbers `a,b` with `a≥2` and `b≥a+2`, the two orphan statements
are as claimed: `{a,b,b+1}` draws at deficit `a+1`, and at deficit `a−1`
draws exactly when `b≥2a−1`; below that threshold it wins. The stated
close-case condition `b+2≤2a` is exactly the complementary integer range.

Two actual disjoint adjacent pairs form a drawn tied root for `a≥2` and
`b≥a+2`. Their deficit-two state is nonwinning for `a≥3`. For three pairs,
`a+2≤b` and `b+2≤c` ensure that all six counters are distinct and ordered.
The separated nonloss theorem permits `a≥2`; the unconditional nonwinning
theorem and the resulting separated draw theorem require `a≥3`. The
anchor-three theorem has exactly `b≥5` and `c≥b+2`, allowing arbitrary
gaps above the first pair `{3,4}`.

## Elementary helpers, polarity, and terminal conditions

The helpers preserve the minimax quantifiers: one nonlosing move suffices
for nonloss; every nonwinning move is required for nonwinning. At a
catching pick they correctly negate the child value, so a nonwinning child
gives a nonlosing move and a nonlosing child gives a nonwinning move.
Equality is included in catching. A pick strictly below the deficit keeps
the same player's perspective.

Every recurrence application establishes nonemptiness and
`sum remaining≥deficit`, either directly from an available catching
counter or, in the continued-pick pair helper, from the available larger
counter. Thus the immediate-cannot-catch terminal rule is never bypassed.
Singletons at deficit at least their counter are correctly nonwinning:
equality draws and strict inequality invokes the terminal loss. A
singleton at smaller deficit wins by taking its counter.

The arbitrary-gap pair helpers do not misuse the imported close-pair
classification. For `d≤q−p`, taking q leaves singleton p with deficit
`q−d≥p`, which is nonwinning; this gives pair nonloss for any `p<q`.
For `0<p<d≤q`, taking p continues the same turn and leaves singleton q
with `d−p<q`, again giving pair nonloss. The imported close-pair formula
is used only for adjacent pairs or for the close orphan-minus case where
its gap hypothesis follows from the stated assumptions.

## Orphan cases and sharp boundary

At deficit `a+1`, taking the orphan a is a **continued pick**, leaving the
same player an adjacent pair at deficit one. That move draws. Taking b or
`b+1` catches and leaves respectively:

- `{a,b+1}` at deficit `b−a−1`, below its gap;
- `{a,b}` at deficit `b−a`, exactly its gap.

Both child positions are nonlosing, so neither catching move wins. This
establishes the draw and covers the potentially missed continued-pick case.

At deficit `a−1`, taking a catches and leaves the adjacent pair at deficit
one, so it draws. Taking b catches and leaves `{a,b+1}` at its exact gap;
the arbitrary-gap pair lemma proves this child nonlosing, so the move is
nonwinning (it need not draw). Taking `b+1` leaves `{a,b}` at deficit
`d=b−a+2`:

- If `b≥2a−1`, then `a<d≤b`; the pair's lower pick a continues, and its
  singleton remainder is winning. The pair is therefore nonlosing, and
  taking `b+1` cannot win the orphan state.
- If `b+2≤2a`, then `b−a<d≤a`. The close-pair formula gives a loss for
  that pair, so taking `b+1` wins the orphan state.

At the boundary `b=2a−1`, the second deficit is `a+1`, strictly above a;
there is no equality-direction error. At `a=2`, the separation condition
is automatic under `b≥4`, and the pair-middle helper permits `d=b`.
All natural subtractions are supported by the hypotheses. As a consistency
check, substituting `b=a+2` makes the close case hold for every `a≥4`,
exactly matching the earlier orphan-pair winning obstruction.

## Two-pair bridges

The tied-root theorem opens at `a+1`, leaving the proved orphan-plus draw.
It invokes the existing `value_eq_draw_iff_exists_draw_after_opening`,
whose reverse implication was inspected: its crossing argument rules out
another winning opening and includes the sparse terminal case. The new
proof does not infer a root draw merely from a generic safe opening.

At deficit two all four counters catch because the minimum is at least
three. If a lower member p is picked, the opponent can take its upper
partner `p+1`; this catches deficit `p−2` and leaves the other adjacent
pair at deficit three, which loses. If an upper member `p+1` is picked,
the opponent takes p; this catches deficit `p−1` and leaves the other
pair at deficit one, which draws. These are all four cases, so every
initial move is nonwinning. The boundary minimum three is valid: the
adjacent-pair loss at deficit three includes equality with its minimum.

## Three-pair nonloss: causal five-reply coverage

The selected first pick is `a+1`, the upper member of the **smallest**
pair. From deficit one, it leaves the opponent deficit a and support
`{a,b,b+1,c,c+1}`. Every remaining counter is at least a. Consequently
every immediate opponent move catches in one pick; there is no hidden
multi-pick reply branch. This fact would not follow from opening an
arbitrary higher pair, and the proof does not do so.

All five opponent replies are covered:

| Opponent pick | Next deficit | Repair pick, when needed | Result used after repair |
| --- | --- | --- | --- |
| `a` | `0` | none | tied two pairs `{b,b+1,c,c+1}`, draw |
| `b` | `b−a` | `b+1` | `{a,c,c+1}` at `a+1`, draw |
| `b+1` | `b+1−a` | `b` | `{a,c,c+1}` at `a−1`, draw |
| `c` | `c−a` | `c+1` | `{a,b,b+1}` at `a+1`, draw |
| `c+1` | `c+1−a` | `c` | `{a,b,b+1}` at `a−1`, draw |

Each repair is available, distinct from prior removals, and catches. The
minus-one rows use `b≥2a−1` directly or `c≥b+2≥2a−1`; the plus-one rows
need no separation. The first row is the equality switch `a=a`, and the
zero-deficit-to-tied-root identity applies. Thus each resulting child is
nonlosing, the opponent's five-counter state is nonwinning, and the
chosen initial move guarantees nonloss.

## Three-pair nonwinning: all six first moves

From deficit one, each of the six possible first picks catches. If it is
a lower member p, the opponent can take its upper partner `p+1`, catching
deficit `p−1` and leaving the two other pairs at deficit two. That child
is nonwinning by the two-pair theorem, so the opponent has a nonlosing
move. If the first pick is upper member `p+1`, the opponent takes p,
catching **exactly** at deficit p and leaving the two other pairs tied
with value draw. These are the six explicit source branches. The remaining
pair minima stay at least three and preserve their disjointness/order in
every case. Therefore all original moves are nonwinning.

Combining separated nonloss with this unconditional nonwinning yields
the stated draw. For `a=3`, the separation condition is just `b≥5`, already
required for disjointness, so the anchor corollary has no hidden hypothesis.

## Trust and limitations

The independent warning-strict affected-target rerun succeeded after the
parent's original build. Lake replayed the current artifacts. The audit
checks all ten public declarations transitively and reports exactly
`propext`, `Quot.sound`, and `Classical.choice` for each. There is no
`sorryAx`, native-evaluation trust, custom axiom, or conjecture assumption.

The result is not an arbitrary-pair-count invariant. Outside separation,
the three-pair theorem proves only nonwinning; it does not classify all
six-counter states or prove their nonloss. It does not increase a certified
N frontier or settle the unbounded first-pair target. No new game search,
bounded outcome computation, or production edit was performed by the reviewer.

Reviewed SHA-256 snapshots:

- `AdjacentPairGeometryRepair.lean`:
  `1061a4fe35d7bf0efa61511ed1f4f967c913ac49953da1214c188ece4cc47b0b`
- `AdjacentPairGeometryRepairAudit.lean`:
  `ae6a4e7a560ac923a10549acef79bb1f8ec12e7a9cfa03506ef14b6b670aad95`

## Addendum: conditional proof-strength accounting

PASS for `research/uniform-descent-20260929/GapAccounting.lean`.
No substantive error or missing obligation was found.

- [x] R6: The conditional accounting lemma has the exact stated hypotheses and does not claim they have been proved.
  EVIDENCE: Source reviewed and independently checked with `lake env lean research/uniform-descent-20260929/GapAccounting.lean` from HISTORICAL_TMP/catchup-score-debt-20260928; exit 0, no warnings. Its transitive axiom audit reports exactly propext, Quot.sound, Classical.choice. The polarity argument is recorded below.

The theorem assumes only `a≥2`, `a∉T`, `sum T≥1`, and nonwinning of
both `(insert a T,a−1)` and `(insert a T,a+1)`. It concludes that `(T,1)`
draws. T is an arbitrary finite set of naturals: no pair structure,
ordering relative to a, parity, or conjecture hypothesis is hidden.

The counter a is available in both extended supports. Their total is
`a+sum T≥a+1`, so neither parent is terminal under the immediate-cannot-catch
rule. Taking a in the minus state catches and leaves the opponent at
`(T,1)`; nonwinning of that move means the underlying value is nonlosing.
Taking a in the plus state is a continued pick and leaves the same player
at `(T,1)`; nonwinning of that move means the underlying value is nonwinning.
Together these force draw. The helper legitimately derives nonwinning of
each legal move from nonwinning of a nonterminal parent. The erasure is
exactly T because `a∉T`, and both natural differences are exactly one.

This is a valid conditional diagnostic of proof strength. It does not
prove either orphan hypothesis, and therefore gives no additional
unconditional target outcome or new frontier. Proving both hypotheses for
a proposed wider family would already imply the desired deficit-one draw
on that family. No numerical computation was run for this addendum.

`GapAccounting.lean` SHA-256:
`ec7c864a3143aae7b691f449dc7d72ae422ee6b7ad96c7abfcf0b082d3f26a10`.

Including this addendum, six review gates are met; none is unmet or abandoned.

## Final-report scope review

PASS for `CATCHUP_UNIFORM_DESCENT_REPORT_20260929_0843_ET.md`, with one
nonblocking wording correction recommended below. No mathematical overclaim
or parent-closure error was found.

- [x] R7: The final report matches the reviewed proofs, their parameters, the parent closure, and the recorded negative-control evidence.
  EVIDENCE: Report compared with all completed reviews, PairDeletionReduction.lean:166, the August exact-closure section, CHECKS.json, PROBE_RESULTS.json, the probe validation helper, and tree_replay.py. No new mathematical computation was run.

The endpoint is correctly limited to `N≥23`, with no parity assumption and
no uniform conclusion in b or k. The three-pair statements retain their
distinct minimum and separation hypotheses, and the anchor-three family
covers only P_8 among interval first-pair states. Nonwinning outside
separation is not promoted to nonloss. The four August families and the
additional first-pair draw remain explicit unresolved parent obligations.

The two computational counterexamples and their moves agree with the
saved probe outputs. Their scripts call the fixed-player cross-check, which
also checks every first edge. The symbolic replay implements exact affine
block and complete-witness checks for all `m≥17`; the report appropriately
retains Lean as the game-semantics authority. No surviving finite probe is
used as a theorem or Lean premise. Historical timing totals and the earlier
722-case run remain session-record claims, not newly rerun measurements.

`CHECKS.json` records the negative control with exit 1 and the exact diagnostic
rejecting `sorryAx` from the named open conjecture. Its source uses the same
three-axiom whitelist and does not introduce a new axiom. Thus the evidence
is the intended rejection, not merely an arbitrary failed compilation.
The production audit count is correct: 6+4+4+10=24 declarations, plus the
separately checked conditional accounting theorem.

Nonblocking correction: in the final paragraph of Target A, replace
“No theorem is claimed for arbitrary k” with “No nonloss theorem is claimed
for arbitrary k.” The obstruction theorem itself is uniform in k; the
current wording is broader than the intended limitation.

Reviewed report SHA-256:
`2a6b19c67668702cb2e2ced37422d176a2f7ef59e7f74a5eafbdd623213b0426`.
Including this report check, seven review gates are met; none is unmet or abandoned.
