> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Catch-Up campaign final report — 2026-08-08 22:06 to 2026-08-09 23:00 EDT

## Executive verdict

The campaign did **not** prove or disprove the full all-`N` Catch-Up conjecture. In the current
uncommitted working tree, it did establish an extended formally certified finite range
and a reusable checked infrastructure:

```lean
theorem value_Icc_eq_draw_le_twenty_eight_of_even_triangular
    (N : ℕ) (hN : N ≤ 28) (heven : Even (N * (N + 1) / 2)) :
    value (Finset.Icc 1 N) = .draw
```

This theorem is in `scripts/catch_up/CatchUpCertifiedThrough28.lean`. In particular, Lean now
proves the four cases `N = 23, 24, 27, 28` for which the source paper reported Monte Carlo tree
search evidence rather than its exact computation through twenty.

This is not a claim of a new computational world record. The
[2015 source paper](https://mpra.ub.uni-muenchen.de/108784/1/MPRA_paper_108784.pdf) reported exact
optimal play through twenty and Monte Carlo exploration at those four larger sizes; a later
[2019 LSE seminar abstract](https://www.lse.ac.uk/Mathematics/assets/documents/Events-Archive/CGO-PhD/PhD-Seminar-on-Combinatorics-2019-update.pdf)
reports exact optimal play through thirty-four. User-supplied August 2026 correspondence from
Bernhard von Stengel reports further computations performed in May 2024, and archived slide
extracts likewise report computation through thirty-eight. Those
sources survive locally at
`SOURCE_CHECKOUT`
and `HISTORICAL_TMP/talk.txt`, respectively. The advance here is therefore
independent formal certification through twenty-eight, together with
reusable proof-producing infrastructure and quantified intermediate theorems—not new game values.

The finite theorem is not a disguised parametric proof: its large endpoints use fully checked
finite strategy certificates. The general theorem
`CatchUp.value_of_even_mul_succ_self_div_two` remains `research open` and still contains `sorry` in
the benchmark problem statement.

## Strongest formal results

### 1. Complete bounded draw theorem through twenty-eight

`CatchUpSearch.CatchUpCertifiedThrough28.value_Icc_eq_draw_le_twenty_eight_of_even_triangular`
proves every parity-admissible interval game through `N = 28` is a draw.

The proof dispatch is exact:

- `N ≤ 24`: the small bases plus the certified dense-three-hole range;
- `N = 25, 26`: the triangular total is odd, contradicting the premise;
- `N = 27, 28`: opening-specific two-owner root certificates.

### 2. Quantified dense invariant through twenty-five

The campaign defined `DenseThreeHoleNonloss N`: every catchable normalized position supported in
`Icc 1 N`, with at most three omitted counters, deficit at most `N`, and even effective total, is
not a loss for the current player.

Lean proves this invariant for every `N = 9,...,25` in
`scripts/catch_up/DenseThreeHoleCertifiedRange.lean`.

This is stronger than checking only the tied interval root. It covers a large finite family of
syntactically qualifying normalized positions at each endpoint, including strategy-relevant
post-opening states; reachability is not required. The range is assembled from:

- proof-backed finite enumeration at `N = 9, 10`;
- a shared partial strategy certificate at `N = 11`;
- the checked `DenseAddTopWindowSafe 11` certificate, composed with the N11 dense invariant to
  derive N12;
- packed target-free one-sided indexed strategy certificates at `N = 13,...,25`.

The generic dense reduction turns `DenseThreeHoleNonloss N` and even triangular total into the root
draw.

### 3. Exact root draws at twenty-seven and twenty-eight

The full dense family became unnecessarily large beyond twenty-five. The campaign proved a sharper
root fact:

```lean
theorem value_eq_draw_iff_exists_draw_after_opening (S : Finset ℕ) (hS : S.Nonempty) :
    value S = .draw ↔ ∃ p ∈ S, (afterOpening S p).value = .draw
```

Therefore it suffices to certify one drawn post-opening state. The new generic
`OpeningPackedIndexedCertificate` checks two complete strategies at the same exact root, one
protecting each player; their conjunction makes that post-opening value draw, and opening-exchange
symmetry lifts it to the whole game.

At both `N = 27` and `N = 28`, opening counter one was used. Every target predicate is constantly
false: no residual state is trusted or discharged externally.

The formal endpoint theorems certify this one drawn opening. They do not assert that every opening
draws; that stronger pattern appears only in the separately audited exact value tables.

### 4. Reusable exact game theory

The campaign also banked warning-strict kernel proofs of the following structural results:

- primitive minimax and fixed-player `CanAvoidLoss` equivalence;
- a root draw iff Player 1 is safe after some opening and Player 2 is safe after every opening;
- the stronger draw-opening equivalence above;
- winning-opening uniqueness and pair-deletion/reply-digraph identities;
- whole-turn minimax flattening over legal completed-turn subsets;
- the exact positive-deficit turn condition
  `d ≤ sum A < d + max A`;
- deficit/excess completed-turn reflection, including the zero-excess singleton boundary;
- exact maximum-counter potential transitions and the zero-potential classification;
- exact-sum loss obstruction and strict-upper residual consequences;
- a sharp seven-hole catch-rank reduction retaining an actual winning-move witness;
- dense-hole successor bookkeeping, including the top-absent and lower-uncatchable cases;
- the catching-window and exact small-gap endpoint normal forms;
- exact effective-total descent along strict upper-winner steps;
- an infinite family of reachable five-consecutive-counter winning traps that refutes naive
  block-clearing policies.

These results remain useful even though they did not close the global induction.

## Certificate and checker architecture

### Semantic layer

`FormalConjectures/Paper/CatchUpConjecture.lean` defines the original score-based evaluator, the
normalized deficit evaluator, exact transitions, game value, and `CanAvoidLoss` semantics. All
certificate soundness ultimately reduces to these definitions.

### Partial certificate layer

The partial certificate checker supports:

- terminal leaves proved safe from the formal terminal semantics;
- owner nodes carrying one checked safe child;
- opponent nodes covering all and only legal children;
- optional target leaves with an explicit, proof-level `TargetSound` obligation;
- strict decrease in remaining-cardinality on every edge.

### Linear indexed layer

`LinearIndexedCertificate.lean` stores nodes in an array and puts the child array index on every
edge. It verifies exact decoded child equality rather than trusting generator annotations. Its
dense coverage enumerates omitted sets of cardinality zero through three, avoiding a full powerset
stack blowup while remaining formally extensionally complete.

### Packed layer

`PackedLinearIndexedCertificate.lean` decodes a decimal CSV string into the indexed DAG. The decoder
rejects malformed digits, bad tags or players, truncated records, and trailing fields. The
subsequent checker validates metadata, every used child index and exact child position, and all
required dense-root coverage; the opening-specific checker additionally requires exactly one exact
advertised root. Packing changed N13 checking from a giant Lean-term bottleneck to seconds without
weakening any mathematical obligation.

### Opening-specific layer

`OpeningPackedIndexedCertificate.lean` retains the full local checker but replaces dense-family
coverage by:

- one legal opening;
- exactly one advertised root index;
- exact decoding to that post-opening `GamePosition`;
- exact game size and protected-player metadata.

Two separately protected certificates at the same root prove a draw. All five generic soundness
theorems depend only on `[propext, Classical.choice, Quot.sound]`.

## Exact endpoint inventory

### Dense-family certificates

| N | Dense roots | Nodes | Edges | Formal interval draw? |
|---:|---:|---:|---:|:---:|
| 13 | 2,646 | 13,759 | 22,997 | total odd |
| 14 | 3,528 | 22,003 | 37,894 | total odd |
| 15 | 4,608 | 34,622 | 61,443 | yes |
| 16 | 5,921 | 53,741 | 98,058 | yes |
| 17 | 7,506 | 82,693 | 155,088 | total odd |
| 18 | 9,390 | 124,705 | 240,889 | total odd |
| 19 | 11,600 | 188,916 | 374,872 | yes |
| 20 | 14,181 | 279,639 | 570,816 | yes |
| 21 | 17,182 | 415,744 | 871,467 | total odd |
| 22 | 20,636 | 612,042 | 1,316,041 | total odd |
| 23 | 24,576 | 903,308 | 1,996,844 | yes |
| 24 | 29,057 | 1,319,099 | 2,987,827 | yes |
| 25 | 34,138 | 1,931,447 | 4,484,168 | total odd |

Every listed strategy has zero target leaves.

### Opening-specific root certificates

| N | Protected | Nodes | Edges | Payload bytes |
|---:|:---:|---:|---:|---:|
| 27 | P1 | 403,358 | 994,478 | 16,211,951 |
| 27 | P2 | 376,208 | 925,985 | 15,080,968 |
| 28 | P1 | 618,700 | 1,542,646 | 25,440,765 |
| 28 | P2 | 566,899 | 1,414,078 | 23,286,653 |

Each pair advertises the same exact opening-one root and contains zero target leaves.

## Independent verification

The large generators are not part of the trusted proof path. They merely propose data that Lean's
checker validates. The campaign nevertheless added separate adversarial audits to reduce correlated
implementation risk.

### N27

- full binary-table Bellman audit: 134,217,728 masks and 3,758,096,384 normalized labels;
- 1,811,939,328 mask/move transforms, zero mismatch;
- one million scalar recurrence samples, zero mismatch;
- exact W/D/L: 2,238,006,556 / 1,415,669,286 / 104,420,542;
- all 7,135,992 fields in both strategies independently rebuilt and matched;
- wrong-owner mutation rejected at field two;
- integrated warning-strict Lean check: 58.04 seconds.

### N28

- full binary-table Bellman audit: 268,435,456 masks and 7,784,628,224 normalized labels;
- 3,758,096,384 mask/move transforms, zero mismatch;
- one million scalar recurrence samples, zero mismatch;
- exact W/D/L: 4,565,496,966 / 3,011,344,704 / 207,786,554;
- every payload field, branch, counter, exact child, and protected-player polarity independently
  checked;
- more than 9.8 million scalar child evaluations over the two strategy DAGs;
- deterministic regeneration byte-identical;
- integrated Lake target passes in 86 seconds.

The W/D/L totals in both audits count normalized table labels, not a collection of distinct initial
games.

### Held-out shifted-tail package

After the report isolated the three exact shifted-tail clauses as a potential structural gate, two
fresh implementations exhaustively evaluated them at the held-out maxima `M = 25,26,27,28`. Across
all twelve predicates they checked 61,746,189 antecedent-satisfying roots and found zero failures:

| M | continuation H7/q1 | catch H6/q1 | catch H7/q3 |
|---:|---:|---:|---:|
| 25 | 8,591,829 | 279,709 | 94,528 |
| 26 | 11,989,664 | 355,786 | 117,358 |
| 27 | 16,514,172 | 448,386 | 144,483 |
| 28 | 22,473,568 | 560,358 | 176,348 |

Independent C++ and Python enumerators agreed on every count and value distribution. The `M=25`
and `M=26` positions were queried as exact smaller-mask subgames in the exhaustively audited N27
table; a second cross-ambient replay against the N28 table agreed. This is exhaustive finite
evidence only: none of the four package instances, and no all-`M` theorem, was proved in Lean. In
this held-out tranche every catch-clause root was a draw, while continuation roots were draws or
wins but never losses.

### Sharp seven-hole catch-rank reduction

The final structural tranche adds a warning-strict kernel theorem for the sharp seven-hole catch
clause. Under its nonempty exact upper-tail, catchability, seven-hole-budget, `deficit ≤ m`, and
even-parity hypotheses, any winning state either has zero deficit or has an explicitly retained
winning move `x` satisfying one of:

- `x ≤ 16`;
- the shifted predecessor `x - deficit` is already a tail hole;
- deleting `x` and `x - deficit` leaves an even tied winning residual with a globally unique
  winning opening `y > x - deficit`.

This is a rank reduction, not a proof of `ShiftedUpperTailCatchNonwin M 7 3`: the zero-deficit,
finite low-opening, predecessor-hole, and tied-residual alternatives remain to be ruled out or
controlled. Exact replay at the sharp failing size `M=19` places all fifteen `q ≥ 3` failures in
three low-boundary states, consistent with rather than closing the theorem's exceptional cases.
An independent post-integration audit rechecked winning-move polarity, natural subtraction,
residual parity, unique-opening scope, the `m ≤ 8` bound, warning-strict compilation, and the exact
standard-axiom footprint, with no blocker.

### Trust boundary

All generic checker/soundness theorems use only:

```text
[propext, Classical.choice, Quot.sound]
```

Concrete large Boolean equalities are proved with `native_decide`, so their certificate and
downstream finite theorems additionally disclose:

```text
[Lean.ofReduceBool, Lean.trustCompiler]
```

There is no `sorryAx`, project-declared axiom, or trusted target leaf in the new certificate
modules. This is the same explicit native-evaluation boundary used by the earlier finite
certificates.

## Approaches that survived

The most useful surviving parametric decomposition is:

1. prove `DenseThreeHoleNonloss N`;
2. reduce the even root draw to that invariant;
3. on an even-top successor, discharge top-absent, maximum-deficit, and lower-uncatchable cases;
4. reduce the unresolved top-present slice to a catching counter in `[d,d+4]`;
5. reduce a broad small-gap nonwin target to exact completed-turn endpoint strata;
6. reduce minimum-move safety for those strata to a sharply quantified shifted-tail package.

This is genuine formal progress, but the last shifted-tail continuation/nonwin package is still
unproved. For the even ambient sizes needed by this successor, exhaustive data found no
endpoint-stratum loss at `M ∈ {16,18,20,22,24}`. The full shifted-tail package fails at each
`M=16,...,19`, with `M = 19` already refuting the C7 minimum-move clause, but exhaustive finite
tests pass every package clause for `M=20,...,28`. The held-out `M=25,...,28` tranche alone covered
61,746,189 roots with zero failures. These bounded observations are not parametric theorems or a
closed induction. The formal seven-hole catch-rank reduction further confines any winning state in
that catch subfamily to a finite low-opening/predecessor-hole boundary or a strictly structured tied
residual, but does not eliminate those alternatives.

## Approaches decisively stopped

The campaign preserved counterexamples rather than repeatedly rediscovering failed proof ideas.
Each item below stops the stated generalization or proof mechanism, not every possible refinement
that might reuse part of it. Several counterexamples are Lean-proved; others were independently
checked by exact recurrences. The chronological ledger records the proof/audit status of each.

- **Universal even-total or equal-partition sufficiency:** false. Five consecutive counters
  `{4,5,6,7,8}` have even total and an equal partition but are a first-player win.
- **Complete subset-sum sequences:** false. An explicit eleven-counter complete sequence with even
  total is a root loss.
- **Fixed matching or unbounded mate queue:** false already at small drawn intervals, even when the
  protected player may choose any pending mate and play optimally when the queue is empty.
- **Wait for zero maximum-potential:** false at reachable `N=7` states; identical scalar signatures
  can have different outcomes.
- **Static adjacent-pair or quota-partition invariants:** false; exact paired-set wins and losses,
  directed reply cycles, and dense balanced-quota losses were found.
- **Quad-block local induction:** nonroot four-counter traps and escapes from the proposed
  draw/deficit-one phase pair destroy hereditary closure.
- **Pure exact-sum iteration:** exact representations can disappear after a winning opening; the
  four-hole small-gap class sharply blocks all canonical exact representations.
- **Raw hole-count hierarchy:** continuing moves add holes; the formal reduction is sound but can
  grow to `floor(N/3)` holes and does not yield bounded complexity.
- **Universal add-top preservation or outcome-only N-to-N+1 rules:** explicit dense-ish transition
  failures show all four W/L behaviors.
- **Fixed minimum, predecessor, bounded adjacent reply, or fixed-low policy:** each has explicit
  small counterexamples. Repairing these policies requires genuine state-dependent adaptivity.
- **Complement/turn-subset duality alone:** a reachable loss at `({3,4},3)` has a perfectly paired
  two-turn hypergraph, yet both endpoints win for the next mover.
- **One scalar effective-total descent:** exact strict descent is true, but hole growth and terminal
  strict-step examples show it does not close the induction.

These failures suggest that a successful proof will need to retain real subset geometry and
adversarial reachability, while avoiding a renamed full minimax grammar.

## What remains open

The campaign has not supplied any theorem of the form

```lean
∀ N, Even (N * (N + 1) / 2) → value (Finset.Icc 1 N) = .draw
```

The obstruction exposed by the current reductions is a uniform strategy invariant that is closed
under every opponent reply, rather than parity or another bounded calculation. Existing reductions
eventually reach shifted upper tails or small-gap endpoints whose next adversarial move can create
an additional free hole. Treating every new shape as another grammar state simply reconstructs the
original minimax recursion.

## Recommended next work

1. **Primary structural gate:** prove the exact three-stratum endpoint nonloss theorem for even
   ambient maximum `M ≥ 16`, with `M=16,18` necessarily treated as separate finite bases or by a
   weaker route. For `M ≥ 20`, the already formal exact sufficient interface is
   `ShiftedUpperTailContinuationNonloss M 7 1`,
   `ShiftedUpperTailCatchNonwin M 6 1`, and
   `ShiftedUpperTailCatchNonwin M 7 3`. The existing exact-sum and maximum-potential routes do not
   prove this package and should remain stopped. The new catch-rank theorem reduces a hypothetical
   seven-hole winning catch tail to zero deficit, a winning move at most sixteen, a pre-existing
   predecessor hole, or an even tied residual with a unique larger winning opening. A credible next
   attack should rule out or rank precisely those four alternatives, starting with the zero/tied
   slice and finite low openings of the sharp `ShiftedUpperTailCatchNonwin M 7 3` bottleneck. Even
   success here would advance only the even-top successor slice, so a complete induction would
   still need a bridge for the other ambient sizes or a two-/four-step formulation.
2. **Certificate-guided invariant mining:** compare the independently checked N27/N28 owner
   strategies and search for a small predicate or well-founded rank stable under all opponent
   edges, using held-out validation between the two sizes. The three shifted-tail clauses have now
   passed the held-out `M=25,...,28` audit; use those 61,746,189 checked roots as a validation corpus
   for a genuinely new dense-upper-tail lemma. Any candidate must be translated to a quantified
   Lean lemma before expanding computation.
3. **Exploit one-opening symmetry:** future root-specific work should certify one drawn opening,
   not every opening or the whole dense family. This reduces N27/N28 data substantially.
4. **Avoid blind frontier expansion:** N29 and N30 have odd triangular total; N31/N32 are the next
   relevant roots beyond this formal frontier. N31 fits the campaign's current packed-table format
   at roughly 16 GiB. N32 needs a widened format because 33 deficit labels no longer fit its two
   32-bit bitsets; a naive two-`uint64` layout is roughly 64 GiB (about 72 GiB peak), while tight
   packing without parity compression would be about 33 GiB and von Stengel's parity-compressed
   layout about 17 GiB. Exact play is publicly reported through N34, and user-supplied
   correspondence reporting May 2024 computations plus archived slide extracts report the same
   computation through N38.
   The next parity-admissible roots without a reported exact computation in that supplied status
   evidence are N39/N40, whose direct tables are in the multi-TiB range. Further computation is
   justified only if it tests a structural hypothesis or uses a new root-directed solver.
5. **Packaging:** if these artifacts are prepared for review, split the computational tranche from
   the structural-lemma tranche. The packed N13–N25 plus N27/N28 sources total about 285 MiB; every
   individual file remains below the 100 MB hard file limit, but the review and CI footprint is
   material.

## Verification summary

Final scoped and repository-wide commands pass:

```text
lake --wfail build catch_up.CatchUpN27PackedRootDraw
lake --wfail build catch_up.CatchUpN28PackedRootDraw
lake --wfail build catch_up.CatchUpCertifiedThrough28
lake --wfail build catch_up.ShiftedUpperTailCatchRankReduction
lake --wfail build CatchUpResearch
lake --wfail build
git diff --check
```

Observed final counts:

- `catch_up.CatchUpN27PackedRootDraw`: 8,064 jobs;
- `catch_up.CatchUpN28PackedRootDraw`: 8,064 jobs;
- `catch_up.CatchUpCertifiedThrough28`: 8,097 jobs;
- `catch_up.ShiftedUpperTailCatchRankReduction`: 8,056 jobs;
- `CatchUpResearch`: 8,161 jobs;
- full repository: 9,010 jobs.

## Delivery state

No files were staged, committed, pushed, or submitted. The shared campaign worktree intentionally
contains inherited user changes and a large untracked research tranche. The final read-only status
must therefore be interpreted as delivery inventory, not as a clean-branch claim.

At the latest readback the checkout is on branch `codex/catchup-experiment` at
`0b67426227811c55db98358c95e99ca5c4465e54`; branch `codex/lennon-pittel-conjecture` points at the
same commit. Branch-only checkouts between these two names occurred in the shared worktree during
consolidation; they changed neither the commit nor worktree content. All principal Catch-Up files
listed below are still untracked in this shared checkout. The final 22:46 EDT readback found five
tracked-but-unstaged modifications, eighty-nine untracked paths, and zero staged paths.

Primary final entry points:

- `scripts/catch_up/CatchUpCertifiedThrough28.lean` — strongest bounded theorem;
- `scripts/catch_up/OpeningPackedIndexedCertificate.lean` — reusable root checker;
- `scripts/catch_up/DenseThreeHoleCertifiedRange.lean` — quantified range theorem;
- `scripts/catch_up/SmallGapShiftedTailPackage.lean` — surviving conditional structural gate;
- `scripts/catch_up/ShiftedUpperTailCatchRankReduction.lean` — sharp catch-gate reduction;
- `scripts/catch_up/CatchUpN27PackedRootDraw.lean` — exact N27 certificate;
- `scripts/catch_up/CatchUpN28PackedRootDraw.lean` — exact N28 certificate;
- `CATCHUP_CAMPAIGN_20260808_2206_ET.md` — chronological experiment ledger.

Frozen SHA-256 hashes for the principal theorem/checker files at final consolidation:

| File | SHA-256 |
|---|---|
| `CatchUpCertifiedThrough28.lean` | `95e1315e3a1e57ea58d60dc7a0d3800875354dcd4e6daf22a983f9afa2eed0e1` |
| `CatchUpN27PackedRootDraw.lean` | `091d5cc3f3fea0774be3b3049640a623ba0e1d6a482129a66d8056e257aaca39` |
| `CatchUpN28PackedRootDraw.lean` | `410cd96932843f001b6d77d042e7fa38881b57114bdea09e00a1a1a420cb21dd` |
| `OpeningPackedIndexedCertificate.lean` | `cb1feb4c7cd027d25bb7aacd0ecbdfae373a768c22fe9af5479692dadf4c0a6c` |
| `DenseThreeHoleCertifiedRange.lean` | `d61e679b5a6d1265d5c7fa633c9e1a0158c3dcc6459c1d64b174c9cfcc8893ed` |
| `SmallGapShiftedTailPackage.lean` | `b113b0b333e4d6fae21b79218fe52e3712a597bdee656536b00a319f523db5f4` |
| `ShiftedUpperTailCatchRankReduction.lean` | `3d0ee96a2d24905980bdea8778cfc6845e3706c6ac6f603e0d185ae96b405173` |
| `LinearIndexedCertificate.lean` | `2c76570a37566b951529cc5970cd100021e08f3985e5317da1b4dade258c05f3` |
| `PackedLinearIndexedCertificate.lean` | `9412511da04822f6b2135480b1c827d6092cbbf66a8fb1db7442e2449f9b70ff` |

### Independent-audit retention warning

The Lean certificate sources above embed all strategy payloads needed for the formal theorems. The
additional independent audit programs, raw full-value tables, and detailed audit reports remain in
`/private/tmp`, which is ephemeral. The principal reproducibility entry points at consolidation
are:

- `HISTORICAL_TMP/audit_n27.cpp`, SHA-256
  `c2957a08d8d183608057bfb8020965758a2159cad7ed18c39b10dde7ded54ca7`;
- `HISTORICAL_TMP/compare_payload.py`, SHA-256
  `85a90ec94b077abfd725040bd3d98fb1717d45bf961753c5061862fe72e59af3`;
- `HISTORICAL_TMP/FINAL_INTEGRATED_AUDIT.md`, SHA-256
  `c540eaa10bd4cfbcd1424f9e7ef735f71051a25b0dc0cf7c2cf90848f4c2d02f`;
- `HISTORICAL_TMP/catchup-n27-v1.bin`, the 1 GiB raw Bellman table, SHA-256
  `88ccc20388d36d14f3045c2f77aa1059a03dc5218b60bf9b57ead7bfaf1515c8`;
- `HISTORICAL_TMP/audit_n28_full_binary_bellman_20260809.cpp`, SHA-256
  `e9747e57cbb287a225084a86f67b26b68b7dda971e7e250eaaa903d51ad0a869`;
- `HISTORICAL_TMP/audit_n28_opening1_two_owner_payloads_20260809.py`, SHA-256
  `2cf29b87e39b50ecdda1f07787af9796ef5e5a3da374a3b794c80d7866697c42`;
- `HISTORICAL_TMP/catchup-n28-v1.bin`, the 2 GiB raw Bellman table, SHA-256
  `75f984ed1cd0152ae835e74b2b6f236e51dd125933a3dfdef75ed746c587506e`;
- `HISTORICAL_TMP/CatchUpN28AndCertifiedThrough28IntegratedAudit_20260809.md`, SHA-256
  `315f59a6f8b7ddf9a7e75cc93df409e4479e2403e1e847e109f5e1362d2c5701`;
- `HISTORICAL_TMP/CatchUpThrough28FinalIntegrationAuditReport_20260809.md`, SHA-256
  `154cfc476044d2f5d0e6928d1fba544870b85dfd2998ecc6d42a56c000c8e734`;
- `HISTORICAL_TMP/CatchUpFinalSurfaceAudit_20260809.lean`, the final warning-strict public-signature
  and axiom readback, SHA-256
  `37284741360eae16b1118d6915c0bf760f219bab2729e7e28ec15f97a2751bd2`;
- `HISTORICAL_TMP/REPORT.md`, the M25–M28 held-out package audit,
  SHA-256 `eaf9b3a35b6086be89b75af28e689585810a18c628ac0c33e84cc2a8bfaf94f7`;
- `HISTORICAL_TMP/heldout_shifted_tail.cpp`, SHA-256
  `320d2687c81c60cb2efeaaba118ae2ca2a3158bc2311ab8b98214b4c4ff47277`;
- `HISTORICAL_TMP/heldout_shifted_tail_crosscheck.py`, SHA-256
  `4b07ea534119183e61c215c69e2cdca1cd7696efadd5d847807696e5e15c3c67`;
- `HISTORICAL_TMP/ShiftedUpperTailCatchRankReductionReport_20260809.md`, SHA-256
  `042d313b27659acf8cda752b9a9a3fba89d8fe166ff76d1b5e331ebc3c6af5aa`;
- `HISTORICAL_TMP/ShiftedUpperTailCatchRankReductionProductionAxiomAudit_20260809.lean`, SHA-256
  `4cf4a9c2fc071d31e6f82fbd1d00e1c0d24264e57290eb110827ec14d2833943`.

The external-status artifacts cited in the executive verdict currently hash to
`e2c068713abad0027342d27612f102644adceb20dfc4948c110f9b0f27f229c3` for the preserved
correspondence and `2c9aa13dfe43f1a56fc54bf3a17df6e18dbe2b3b3c88ab060d126d8633cf7813` for the slide-text
extract.

Copy the files under `/private/tmp` to durable storage before cleanup if independent-audit replay,
beyond the self-contained Lean checks, is required later. The chronological campaign ledger records
the larger raw-table and payload hashes.

## Final mathematical assessment

The conjecture remains credible: no counterexample was found, and every parity-admissible root
through twenty-eight is now formally proved drawn. The campaign's main advance is not a new
computational record or merely four more finite value checks. It produced a proof-backed dense
invariant through twenty-five, a compact and reusable one-opening certification theorem, complete
independent audits of the two largest formally certified roots, and a well-documented map of why
the most tempting parametric strategies fail. Its final structural theorem also compresses the
sharp seven-hole catch obstruction to four explicit alternatives while retaining a formal winning
move witness.

The small-gap/shifted-tail endpoint is a sharply isolated open gate in the surviving even-top
successor route, not the whole remaining conjecture. A full proof would additionally need an
odd-step, two-/four-step transfer, or a different direct-root argument that closes under every
adversarial reply.
