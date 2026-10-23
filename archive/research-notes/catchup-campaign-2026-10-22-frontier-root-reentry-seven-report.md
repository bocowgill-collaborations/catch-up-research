> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.RootUpperReentry](../../CatchUp/RootUpperReentry.lean).

# Uniform seven-opening exclusion: completed Lean integration

Status: compiled and axiom audited; independent review requested from parent.
No general conjecture or unconditional anchor nonloss is claimed.

## Results

New source: `CatchUp/RootUpperReentry.lean`, namespace `CatchUp.RootUpperReentry`.

1. `reserve_five_nonwin_of_seven_loss`: for ANY finite support C containing
   2 and 3, with all labels at least 2, and with 5 and 7 absent,

       V(C,7)=LOSS => V(insert5 C,2)!=WIN.

   This quantifies over every legal opponent TurnSet. No tail structure,
   parity, density, cardinality, or catchability premise on C is assumed.

2. `seven_shadow_nonloss_of_parent_loss`: under the same arithmetic support
   conditions,

       V(insert5(insert7 C),5)=LOSS => V(C,7)!=LOSS.

   Thus the actual parent LOSS is consumed; this is more than a detached
   implication conditioned on a shadow loss.

3. `interval_seven_shadow_nonloss`: for every N>=7,

       V([2,N] minus {6},5)=LOSS
       => V([2,N] minus {5,6,7},7)!=LOSS.

4. `interval_upper_opening_ge_eight`: for every N>=7, a losing parent
   `([2,N] minus {6},5)` has some actual winning residual opening

       w in [2,N] minus {5,6}, w>=8,
       afterOpening([2,N] minus {5,6},w).value=LOSS.

   This strengthens the existing exact-block bound w>=7 to w>=8. The
   remaining exceptional w=8 branch is not proved here. A bound w>=9 would
   reenter the intended four-hole density range; this file does not assert it.

## Proof and opponent coverage

At deficit 2 with every available label at least 2, a legal whole turn is
necessarily a singleton. This is proved as a private helper: any additional
preparation counter would contribute at least 2, contradicting the required
strict preparation mass below 2. This excludes no legal turn and covers
arbitrary support cardinalities.

For the reserve-five endpoint `(insert5 C,2)`, split the arbitrary singleton
turn `{x}` into exactly two cases:

- x=5: the endpoint is `(C,3)`. The new `DeficitCrossing.seven_to_three`
  theorem proves NONLOSS from the high-shadow LOSS at deficit 7. Its legal
  midpoint turn is [2,3], whose sum 5 continues at high deficit 7 and catches
  at low deficit 3; both endpoints have the same support and deficit 2.
- x!=5: x belongs to C and x!=7. The existing arbitrary-turn theorem
  `PairEntranceShadow.endpoint_win_of_total_ne` supplies a winning reply 5.
  Its exceptional equality cannot occur because this turn's total is x,
  while counter 7 is absent.

Every endpoint is therefore NONLOSS for the waiting player. The existing
whole-turn characterization proves the reserve-five position NONWIN.

If the genuine parent were LOSS, its legal singleton turn `{7}` would leave
that same reserve-five position WIN. This contradicts NONWIN whenever the
seven-shadow is LOSS. The interval specialization proves the exact insert/
set-difference identities, including 5 and 7 availability and exclusion of 6.
Finally the existing exact-deficit theorem for block `{5}` supplies an actual
winning residual opening w>5. Its support excludes 6, and the new parent
exclusion rules out 7. Thus w>=8, with the losing post-opening position retained.

The proof uses neither an informal alternating-pick assumption nor a chosen
principal variation. The universal TurnSet bridge covers all ordered legal
opponent turns. Terminal high shadows are handled by the imported
`loss_after_subsum` contract. The reserve endpoint and actual parent are
provably catchable because they contain 5 and 7 respectively.

## Verification and reproducibility

From `research/catchup`:

    python3 -B campaign_2026_10_22/frontier/root-reentry-seven/verify.py

Pinned Lean: `leanprover/lean4:v4.27.0`.
Pinned Mathlib: `a3a10db0e9d66acbebf76c5e6a135066525ac900`.

| Production stage | Exit | Wall seconds |
|---|---:|---:|
| strict scoped Lake build | 0 | 7.352 |
| fresh source elaboration, warnings as errors | 0 | 4.693 |
| four public axiom audits and hypothesis examples | 0 | 4.392 |

All four public transitive closures are exactly
`propext`, `Classical.choice`, and `Quot.sound`. There is no sorry, custom
axiom, native-only evaluator, unchecked solver result, or unfinished-conjecture
dependency. The only local `decide` in the theorem source distinguishes the
Outcome constructors; no game outcome is inferred from experimental tables.

The audit includes an N=7 boundary instantiation and an arbitrary-tail
specialization with every tail label at least 8. Neither needs a parity
hypothesis. The latter retains the actual parent LOSS, and therefore is NOT
an unconditional proof of anchor A.

The full source also passed LeanProbe with no errors, warnings, or sorries.
Two local simplification errors were corrected before production: simplifying
a set difference by a singleton required the explicit erase identity, and
erasing 7 through insert5 required the unequal-insert identity. One initial
wrapper launch used an incorrect path prefix for its working directory and
created no evidence files; the corrected bounded verifier above completed all
three stages. No failed mathematical candidate or counterexample was found.

## Proof-size and resource record

The new source is 140 lines / 6,129 bytes, consisting of one private supporting
lemma and four public theorems. These are source-size figures, not a measured
kernel proof-term size or a lower bound. The proof also depends on the new
separately reported `DeficitCrossing` module and existing whole-turn, shadow,
and exact-block mathematics; their costs are not hidden as a one-line proof.
No serialized strategy certificate or new machine transition table is involved.

Source SHA-256:
`b60d79d69be929f502a853e33ee87f0d28bd843ecebc047a8de997d1ea5f4ddf`.
The imported frozen crossing source SHA-256 is
`e2ca5fd5d4dcd7a2ead9f2b8cc9b32f5ab23a90833a2a3c0bc6cd9345d9c43da`.
Logs, commands, and hashes are retained in `verification.json`.
Recorded platform: macOS 26.6.2 arm64. Maximum cumulative child RSS in the
replay process was 5,448,679,424 bytes; this is not an isolated per-stage peak.
Each production stage had a 120-second timeout. No unbounded experiment ran.

## Exact remaining obligation

The single next root-specific obstruction is the genuine opening w=8. Its
reserve-taking endpoints are `(C,2)` and `(C.erase2,4)` for
C={2,3,4,7} union [9,N], under the actual high-shadow LOSS at deficit 8 and
actual parent LOSS. The simple midpoint pair {2,3} does not itself settle
these endpoints: at deficit 2 it is not a legal completed turn. No closure
for that branch, no unrestricted anchor A/B theorem, H, or C was proved here.
