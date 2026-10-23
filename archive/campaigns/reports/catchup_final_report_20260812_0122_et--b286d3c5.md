> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Catch-Up Campaign Final Report — 2026-08-12 01:22 ET

## Executive result

The general Catch-Up draw conjecture was **not proved** in this run. The run was
ended early at the user's request. All research agents were stopped, the prior reports were preserved unchanged, and
this report records only results that were either formally checked, independently
audited, or explicitly labelled computational/conjectural.

The certified finite frontier is unchanged:

- `value (Finset.Icc 1 N) = .draw` is formally certified for every `N <= 28`
  with even triangular total;
- `DenseThreeHoleNonloss N` is formally certified for `9 <= N <= 25`;
- the concrete certificates retain their previously disclosed
  `Lean.ofReduceBool` / `Lean.trustCompiler` native-evaluation boundary.

The strongest new rigorous reduction is:

> Any parity-admissible counterexample has `N >= 31` and forces a losing
> normalized position in one of two explicit, bounded, top-two-complete
> families.

For `N >= 7`, if `value (Icc 1 N) != .draw`, then either

1. there is `b in Icc 2 (N - 2)` such that
   `pairDeletionPosition N 1 b` is losing; or
2. there is `x in Icc 3 (N - 2)` such that
   `firstPairChild N x = Position ((Icc 3 N).erase x) (x - 1)` is losing.

The two witnesses retain `N-1` and `N`, and satisfy the exact identities

```text
effective(pairDeletionPosition N 1 b) + 2 = sum(Icc 1 N)
effective(firstPairChild N x) + 4 = sum(Icc 1 N).
```

Consequently they inherit even effective total from an admissible interval.
Certification through 28 plus the odd triangular totals at 29 and 30 gives the
sharp currently formal lower bound `N >= 31` for any admissible counterexample.

The proof is warning-strict Lean, has been independently audited for polarity,
endpoints, non-circularity, and axioms, but is not yet integrated because its
scratch source needs the repository header/attributes and an unused-import
cleanup.

## Strongest new formal interfaces

### 1. Minimal-counterexample normal form

Scratch:

```text
HISTORICAL_TMP/CatchUpMinimalCounterexampleWitness.lean
SHA-256 f5a68a00432d2273a67e7724134caa5cb836396726a159336e88113c7fee2586
```

Status:

- standalone `-DwarningAsError=true` PASS;
- independent semantic audit PASS;
- structural results use only `propext`, `Classical.choice`, `Quot.sound`;
- `N >= 31` additionally inherits the existing native-certificate axioms;
- no `sorryAx` and no use of the conjecture;
- integration pending header, `@[category API, AMS 91]`, and import cleanup.

### 2. One common drawn opening suffices for `N -> N+4`

The old root-transfer hypotheses were materially stronger than necessary. It is
enough to transfer both fixed-player nonloss properties at one common old opening
that is drawn in the smaller game. No new-opening transfer, every-opening draw,
or universal old-opening transfer is required.

Artifacts:

```text
HISTORICAL_TMP/OpeningOneTransferFormal.lean
SHA-256 46a3af3427344d263176682d90a29da9f9e28465db43d8fc00a4e63927e93d79

HISTORICAL_TMP/FourLiftRootTransfer.lean
SHA-256 ce0b2f38f90112713590734e16abd4ce3dd73885057321db2427d00b893e9aac

HISTORICAL_TMP/MinimumOpeningRayTransfer.lean
SHA-256 65c3c95f69ed4450e72670cf442b4b9fe500fc6fe3e315b929dfe0bf9e057d34
```

All three core arguments passed warning-strict elaboration after the auditor
stream-injected required repository metadata. Their logical axiom footprint is
the standard three. They still require production-style cleanup before import.

The exact opening-one ray is

```text
Q_N(b) = pairDeletionPosition N 1 b
       = Position ((Icc 1 N).erase 1 |>.erase b) (b - 1),  2 <= b <= N.
```

Opening one draws exactly when every `Q_N(b)` is nonlosing and at least one is
drawn. This is a useful exact interface, not yet the missing strategy.

### 3. Two nonlosing openings force a draw

For any nonempty counter set, two distinct openings whose post-opening values
are not `.win` force the root value to be `.draw`. This follows from the existing
winning-opening uniqueness and draw-opening theorem; a causal two-anchor
interpretation explains precisely why one anchor fails at the collision branch.

The core short theorem elaborated with only the standard three axioms. The larger
scratch file is not integration-ready:

```text
HISTORICAL_TMP/TwoNonlosingOpenings.lean
```

Exact data show at least two such openings for every admissible interval through
28. The statement is false for arbitrary even-total sets, so the remaining work
is genuinely interval-specific.

### 4. Reply-graph common-maximum companion

If the maximum counter has one outgoing reply edge, it has a distinct companion
outgoing edge; its downward outdegree cannot equal one. The proof is
warning-strict and standard-axiom only:

```text
HISTORICAL_TMP/ReplyMaximumCompanion_reply_digraph_global_20260812.lean
SHA-256 35a43317ac22035a3f450ef7088b8ecdfd1a4d59ee4b8025f523563a00210011
```

Finite audit found no all-out reply graph among 94,957 eligible even
interval-minus-at-most-five-hole roots through `N=23`. A six-hole root loss at
`N=13` shows that a density hypothesis is essential.

## Exact remaining closure after the new normal form

Define

```text
A(N,b)  = pairDeletionPosition N 1 b
B(N,x)  = Position ((Icc 3 N).erase x) (x - 1)
TA(N,b) = (Icc 2 N).erase (b - 1) |>.erase b
TB(N,x) = (Icc 3 N).erase (x - 1) |>.erase x.
```

For interior indices, the available exact-deficit move catches, so its child is
negated:

```text
A(N,b).moveOutcome (b - 1) = neg (value (TA(N,b)))  for b >= 3
B(N,x).moveOutcome (x - 1) = neg (value (TB(N,x)))  for x >= 4.
```

Thus the normal form would close if one independently proved, for admissible
`N >= 31`:

1. `A(N,2).value != .loss`;
2. `value(TA(N,b)) != .win` for `3 <= b <= N-2`;
3. `B(N,3).value != .loss`;
4. `value(TB(N,x)) != .win` for `4 <= x <= N-2`.

The endpoint exceptions `b=2` and `x=3` matter: their exact deficit counters
have already been deleted. The unrestricted tied-root claims are false at small
admissible sizes, so the `N >= 31` and interval-density hypotheses cannot be
dropped.

This four-obligation surface is the cleanest restart target produced by the run.
It is a reduction, not a proof, and none of these four statements may be proved
using the main conjecture or the normal-form conclusion itself.

## Lower-ray evidence and sharp boundary

For `b >= 3`, taking `b-1` in `Q_N(b)` reaches the tied punctured root

```text
R_N(b) = Icc 1 N \ {1, b-1, b}.
```

Exact computation on every admissible `N <= 28` found that all these residuals
draw except exactly five winning residuals:

```text
(N,b) = (4,3), (4,4), (7,4), (7,6), (8,3).
```

There were no residual losses. Uniform exact draws hold at
`N = 11,12,15,16,19,20,23,24,27,28` for every `b`.

Reproducer:

```text
HISTORICAL_TMP/lower_ray_residual_exact.cpp
SHA-256 7fa916d740a88a79ce0030054302997063db00dea94418a8e1fdcc15f7164028
```

For `N=15,16,19,20`, a simple adjacent-response policy passed 974 exact local
challenges with every prescribed reply drawing. It is not closed under repeated
play: holes grow, and the analogous layer already has explicit failures at
`N=12`. This is evidence for a richer two-exchange language, not a theorem.

## Certificate-mined structural rule

Across all four N27/N28 owner certificates:

- 1,965,165 nodes;
- 1,524,035 owner decisions;
- 741,762 continuing owner edges;
- 4,877,187 total edges.

Every continuing least-safe decision obeyed the same rule: if the least safe
move `x` remains below the deficit and the next least safe move is `y`, then
`x < y`. An independent exhaustive recurrence through `N=15` checked 737,794
such decisions with zero failures.

The mathematical proof uses commutation of two below-deficit picks and minimality
of `x`. It implies that least-safe completed turns are strictly increasing and
therefore have length `O(sqrt N)`. The Lean proof was interrupted before its
commutation helper was left complete, so this result is proof-ready mathematics,
not yet a banked Lean module.

## Shifted-tail route at shutdown

The prior seven-hole shifted-tail route remains a separate promising route.
New exact computation supports the candidate

```text
3 <= m <= M
R subset Icc (m+1) M
holesAboveM + (m-1) <= 7
1 <= d <= m
Even (d + sum R)
x in R
x-d in R
---------------------------------
value (R.erase x, x-d) != loss
```

with zero failures for `M=19,20,21,22` over 859,331 exact instances. The
threshold is sharp in the tested data: `M=18` has five failures, and dropping
parity or allowing an eighth hole also fails. This is computational evidence,
not a Lean theorem.

The zero-deficit H=7 slice has zero wins for every tested `M=20..28`; `M=19`
has one semantic exception, `R={7,10,11,...,19}`, uniquely won by opening 7.
The exact open structural statement is exclusion of a universal sink in the
dense-tail reply graph.

The low-move branch is not finite in `M`: it reduces to an even H=8 losing child
with deficit at most 15 but linearly growing support. A warning-strict bound
theorem is at:

```text
HISTORICAL_TMP/ShiftedUpperTailLowMoveBounds_20260812.lean
SHA-256 55120e697105d3b7aa693c8c75904491ebff6b9cca8fa995274b92780500a0d8
```

## Routes closed by exact counterexamples

The following should remain marked blocked unless a materially new mechanism is
proposed:

- pointwise, same-history, or ordinary safety-preserving `N -> N+4` lift;
- `N -> N+2` induction (it flips triangular parity, and one-sided safety fails);
- context-free neutrality of the top four counters;
- static exact quotas, balanced partitions, basis exchange, or ordinary Hall/SCD
  arguments;
- bounded-arity dynamic matching, even with complete rematching;
- exact-sum-only endpoint strategies (overshoot is sometimes essential);
- componentwise/WQO monotonicity, translation, reflection, majorization, or
  scalar/quota classification;
- interval composition through fixed finite scalar profiles;
- expectation or balanced-flow arguments that omit recursive endpoint values;
- generic disjoint-union or Sprague-Grundy-style neutral components.

Representative reachable obstruction:

```text
Position({5,6,7,8}, 4) = loss
```

despite an exact balanced final allocation. All legal turns are singletons and
the opponent pairs `5<->6` and `7<->8`.

## Verification and trust status

- Baseline targeted build before the wave:
  `lake --wfail build catch_up.CatchUpCertifiedThrough28
  catch_up.ShiftedUpperTailCatchRankReduction` — PASS, 8,098 jobs.
- Minimal-counterexample scratch — warning-strict PASS and independent semantic
  audit PASS.
- Same-opening transfer scratch — warning-strict PASS.
- Reply companion scratch — warning-strict PASS and temporary target build PASS,
  8,056 jobs.
- A full post-wave build was deliberately stopped during wind-down at
  8,374/9,010 jobs, with no failure observed to that point. It must not be
  reported as a completed build.
- Scratch files explicitly described above as incomplete, appended with `sorry`,
  or containing a final compile error are **not** integration candidates.

## Recommended next bounded run

1. Production-clean and integrate, in this order:
   - `CatchUpMinimalCounterexampleWitness`;
   - the same-opening/four-lift root transfer interface;
   - `ReplyMaximumCompanion`;
   - the two-nonlosing-openings theorem.
2. Run warning-strict per-file checks, axiom audits, the focused Catch-Up CI target,
   and then one complete `lake --wfail build`.
3. Formalize the exact A/B-to-TA/TB move identities and the two endpoint exceptions.
4. Attack the four normal-form closure obligations independently. The best first
   candidates are:
   - tied punctured roots `I_N \ {1,b-1,b}` for admissible `N >= 11`;
   - the endpoint states `A(N,2)` and `B(N,3)`;
   - the two-anchor opening criterion for intervals.
5. In parallel, formalize the least-safe-increasing lemma and test whether its
   `O(sqrt N)` turn bound yields a genuinely closed strategy language.
6. Keep the shifted-tail route alive only through new mechanisms for the
   zero-deficit universal-sink slice or the even H=8 low-deficit child; do not
   reopen pure counting or exact-sum routes.

## Delivery state

- Branch: `codex/catchup-campaign-20260812`
- Pre-wind-down checkpoint: `2ed1eb7a`
- Prior reports remain unchanged.
- New campaign/progress reports are timestamped separately.
- At final report creation, no production-source scratch file remained in the
  worktree.
