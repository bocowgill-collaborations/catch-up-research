> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Catch-Up campaign — 2026-08-08 22:06 EDT

## RESUME HERE

- **STATUS:** `COMPLETE`
- **Campaign ID:** `20260808_2206_ET`
- **Current timestamp:** 2026-08-09 22:47 EDT
- **Research deadline:** 2026-08-09 23:00 EDT
- **Initial discriminating phase ends no later than:** 2026-08-09 01:06 EDT
- **Pre-consolidation:** 2026-08-09 20:00 EDT
- **Hard consolidation:** 2026-08-09 21:30 EDT
- **Final process-stop/readback phase:** 2026-08-09 22:45 EDT
- **Worktree:** `SOURCE_CHECKOUT`
- **Latest checkout readback:** `codex/catchup-experiment` at
  `0b67426227811c55db98358c95e99ca5c4465e54`; `codex/lennon-pittel-conjecture` points at the same
  commit. Branch-only checkouts between those names occurred in the shared worktree during
  consolidation without changing the commit or worktree content.
- **Current strongest-result override (supersedes the older narrative immediately below):** Lean now
  proves `value (Icc 1 N) = draw` for every `N ≤ 28` whose triangular total is even. The dense
  quantified invariant `DenseThreeHoleNonloss N` is certified for every `N = 9,...,25`; exact
  opening-specific two-owner certificates separately close `N=27` and `N=28`. This advances exact
  formal verification beyond the source paper's exact-through-20 computation and replaces its
  MCTS-only evidence at 23, 24, 27, and 28 with checked theorems. The general all-`N` conjecture is
  still open; no uniform successor or parametric strategy was proved. This is a formal-certification
  advance, not a new computational world record: a 2019 LSE seminar abstract reports exact optimal
  play through `N=34`, and user-supplied August 2026 correspondence reporting computations performed
  in May 2024 plus archived slide extracts report the same computation through `N=38`.
- **Strongest verified state:** the exact Catch-Up draw criterion, literal Lean/native-checked
  draw certificates at `N = 11, 12, 15, 16`, the relevant-range symbolic top-four classification,
  and a sound semantic width-three one-residual simulation/basin framework with executable
  reflection of individual advances. This campaign additionally Lean-proved the odd-weight
  no-draw theorem, an independent finite product-DAG checker, literal checked old-root basins at
  `7 → 11` and held-out `8 → 12`, and a uniform new-opening entry theorem. The root-generated initial-turn history and
  its strategically selected liftability predicate are Lean-proved; finite native-checked
  regressions prove the complete player-two new-opening transfer at `7 → 11` and `8 → 12`. The
  canonical dense endpoint now has Lean-verified exact turn classification, a four-counter
  `N ↦ N - 4` packet decomposition, and legal balancing responses for both surviving-top and
  restored-low packet catches. Lean now proves the complete semantic simulation advance for every
  explicitly safe mirrored common-old move, including history, support, and value preservation.
  A separate aggregate ledger with a persistent integer resolved value is now Lean-verified: its
  finite history checker reflects the exact pointwise visible history plus deterministic aggregate
  resolution, its advance checker is sound, and any locally closed aggregate relation transfers
  player safety by well-founded induction.
  Lean also now proves arbitrary-finite-set winning-opening uniqueness, the exact unique-existence
  characterization of a first-player win, and reachable interval support/deficit/cardinality and
  parity invariants. Most recently, Lean reduces the interval draw conjecture to a one-parameter
  lower pair-deletion ray: if every state obtained by deleting `1` and `b`, with deficit `b - 1`,
  is nonlosing and the `b = 2` state draws, then the full interval root draws. Lean also proves
  that a nonempty finite Catch-Up root draws exactly when at least one post-opening position draws.
  The retained finite development now proves the stronger statement that every one of the twelve
  openings at `N=12` draws, by combining independently checked shared player-one and player-two
  certificate DAGs. Lean now also proves the exact conditional symmetric four-lift theorem:
  every-opening draw at `N`, together with old- and new-opening safety transfers for both fixed
  players, implies every-opening draw at `N+4`; the same statement is available directly from four
  explicit basin families. The exact maximum-counter potential transition and its complete zero-potential
  boundary classification are also Lean-proved. Lean now also flattens primitive-pick minimax
  exactly across a whole completed turn: friendly safety is existential over legal turn subsets,
  waiting-player safety is universal, positive-deficit legality is the half-open condition
  `d ≤ sum(A) < d + max(A)`, and draw is equivalent to every endpoint being nonlosing plus one
  drawing endpoint.
  Lean now also proves the exact deficit–excess reflection law for completed turns, including its
  zero-excess singleton boundary. Separately, five consecutive counters beginning at least at four
  are a first-player win; more strongly, the normalized five-counter position wins whenever its
  bottom is at least six and its deficit is at most one above that bottom. Every interval game of
  size `4 * k`, `k ≥ 2`, has an explicit legal
  history after opening `3` that reaches the tied top five with player one to move. This is an
  infinite reachable trap for block-clearing policies, not a forced line under optimal play.
  Preliminary paired computation found one affine 24-macro vocabulary closing all 120
  first-generation packet challenges at both `12 → 16` and held-out `15 → 19`, with successor old
  discrepancy at most one. A full stable-phase audit also isolated a bounded aggregate-residual
  obstruction to the old one-residual representation. The dense program has now advanced one full
  endpoint farther: an independently checked 2,350-node literal certificate proves the exact
  five-counter catching-window property at lower endpoint `11`, and Lean combines it with the
  quantified `H_11` theorem and the successor reduction to prove
  `DenseThreeHoleNonloss 12`. The generic window theorem shows that every witness child has at most
  four holes and deficit at most four. No unconditional parametric draw theorem is proved.
- **Current objective:** exact completed-turn minimax flattening and deficit reflection are
  integrated, as is the infinite reachable tied-top-five trap. Two broader parametric routes have now stopped:
  complete distinct even sets can themselves be root losses, and a joint four-residue/add-one
  induction requires uncontrolled loss-to-win and win-to-loss endpoint flips. Unbounded obligation
  memory has also received a strong computational stop verdict. Complement duality has a smallest
  reachable obstruction: `Position({3,4},3)` is loss even though its two legal completed turns are
  perfectly paired. The reflection and top-five audits have passed. The bounded `N=15` all-opening
  extraction did not complete within 1,139.5 seconds and was stopped without a certificate or a
  claimed failure. The dense prefix scout proved exact canonical shapes for the remaining
  deficit-one/two branches and found no losses through `N=22`. A new kernel proof now eliminates
  the entire deficit-two prefix branch in the even-triangular target: its three forced holes have
  total `d+3`, so its parent effective total is odd. In the first deficit-one branch, evenness
  forces the optional third parent hole to exist and be odd, giving an exact four-hole child. The
  other surviving deficit-one branch is a rigid consecutive-triple deletion and parity forces
  `d` odd. The upper-residual branch is now connected end-to-end: from an actual dense
  three-hole witness Lean constructs the losing child, proves it has at most six anchored holes,
  chooses its greatest lower counter, and obtains a strict next upper step, gap at most four, or
  new deficit at most twelve. The strict next exact block may contain three counters, so this is a
  rigorous one-step trichotomy rather than a closed induction. A separate proof-backed finite
  checker establishes the complete dense-three-hole nonloss invariant at endpoints `N=9` and
  `N=10`; its generic soundness theorem uses only standard axioms, while those two concrete test
  theorems explicitly use native reduction. A second independent checker now permits one shared
  partial-strategy DAG to cover every quantified dense root. At `N=11`, one memoized solve produced
  1,392 qualifying roots and a 3,154-node shared DAG; independent local-obligation and exact formal
  root-coverage checks pass, yielding a Lean theorem `DenseThreeHoleNonloss 11`. A separate
  catching-window checker now covers the same 1,392 roots with a 2,350-node literal player-one DAG:
  each root has a certified catching counter in `[d,d+4]`. Its independent check passes and the
  resulting theorem closes the successor step, yielding the stronger quantified theorem
  `DenseThreeHoleNonloss 12`; the finite all-opening theorem at `N=12` also remains complete. Lean
  now also gives an exact successor characterization: for even `N+1` and
  known `H_N`, `H_(N+1)` is equivalent to preservation of nonloss when that new maximum is
  adjoined; every top-absent, maximum-deficit, and lower-uncatchable case is already discharged.
  The add-top premise itself is now reduced to `DenseAddTopWindowSafe N`. Exact independent
  recurrence found zero window failures among 69,510 qualifying roots for odd
  `N=11,13,15,17,19,21,23`, and width four is sharp. Lean further proves that the single structural
  predicate `SmallGapFourHoleNonwin (N+1)` implies the window, add-top preservation, and the full
  successor invariant when the new top is even. This small-gap predicate is false at endpoints
  `12,14` but has no wins at every tested even endpoint `16,18,20,22,24`; it is the principal
  parametric target. The principal objective is still parametric rather than table expansion.
- **Exact next action:** finish the independent audits of the literal window certificate and its
  two generic proof modules, then attack `SmallGapFourHoleNonwin M` for even `M≥16`. Prefer a
  strategy/product-DAG invariant for this exact four-hole, deficit-at-most-four family; do not grow
  another response grammar. The universal descendant nonloss/nonwin diamond is formally blocked by
  singleton descendants and by a legal descendant of a qualifying `H_9` root, so it is not a
  substitute for the existential window. Do not merely extend the already clean raw window table
  past `N=23`. The four exact
  small-gap child families, their conditional continuing-pick reduction, and exact effective-total
  descent are integrated; both explicitly record that hole growth prevents raw iteration. Attack
  only a genuinely semantic survivor, since
  parity/counting iteration has stopped at four realizable gaps. The apparent
  universal move-`3` rule for the surviving triple-deletion family is already false at
  `(N,d)=(12,9)`; retain its exact child identity but do not grow a response grammar. Do not blindly
  iterate the dense upper residual branch, which loses the three-hole hypothesis. Accept a
  macro-subset strategy only if it supplies quantified closure and a genuine well-founded decrease;
  preserve the complete-set, add-one, obligation-memory, and complement-duality falsifiers. Do not
  expand the capped quad computation to seven blocks.
- **Files modified or created by this campaign:** this checkpoint;
  `scripts/catch_up/Parity.lean`; `scripts/catch_up/FourLiftCertificateChecker.lean`;
  `scripts/catch_up/ReachableBounds.lean`; `scripts/catch_up/WinningOpening.lean`;
  `scripts/catch_up/DrawOpening.lean`; `scripts/catch_up/PairDeletionReduction.lean`;
  `scripts/catch_up/LowerRayTransfer.lean`; `scripts/catch_up/LowerRaySuccessor.lean`;
  `scripts/catch_up/LowerRayExactDeficit.lean`; `scripts/catch_up/DeficitWinningBound.lean`;
  `scripts/catch_up/LowerRayEndpoints.lean`;
  `scripts/catch_up/LowerRayInteriorReduction.lean`;
  `scripts/catch_up/ReplyDigraphReduction.lean`;
  `scripts/catch_up/AdditiveTripleReduction.lean`;
  `scripts/catch_up/ExactSumLossObstruction.lean`;
  `scripts/catch_up/MaximumCounterPotential.lean`;
  `scripts/catch_up/DenseHoleReduction.lean`;
  `scripts/catch_up/DenseHoleHierarchy.lean`;
  `scripts/catch_up/DenseMinimumShiftedReduction.lean`;
  `scripts/catch_up/DenseLossInjection.lean`;
  `scripts/catch_up/PrefixBlockedDenseEndpoints.lean`;
  `scripts/catch_up/DenseUpperGapPipeline.lean`;
  `scripts/catch_up/DenseThreeHoleFiniteChecker.lean`;
  `scripts/catch_up/DenseThreeHoleCertificateChecker.lean`;
  `scripts/catch_up/DenseThreeHoleN11Certificate.lean`;
  `scripts/catch_up/DenseHoleSuccessor.lean`;
  `scripts/catch_up/DenseAddTopWindow.lean`;
  `scripts/catch_up/DenseAddTopWindowCertificateChecker.lean`;
  `scripts/catch_up/DenseAddTopWindowN11Certificate.lean`;
  `scripts/catch_up/SmallGapChildFamilies.lean`;
  `scripts/catch_up/EffectiveTotalDescent.lean`;
  `scripts/catch_up/CompletedTurn.lean`;
  `scripts/catch_up/CompletedTurnReflection.lean`;
  `scripts/catch_up/FiveConsecutiveTrap.lean`;
  `scripts/catch_up/N12EveryOpeningCertificate.lean`;
  `scripts/catch_up/FourLiftN7P2Old1Certificate_20260808.lean`;
  `scripts/catch_up/FourLiftN8P2Old1Certificate_20260809.lean`;
  `scripts/catch_up/EveryOpeningFourLiftTransfer.lean`;
  `scripts/catch_up/NewOpeningEntry.lean`; `scripts/catch_up/NewOpeningHistory.lean`;
  `scripts/catch_up/NewOpeningHistoryRegression.lean`;
  `scripts/catch_up/NewOpeningImmediate.lean`; `scripts/catch_up/NewOpeningRepair.lean`;
  `scripts/catch_up/AggregateSimulationLedger.lean`; and
  additive diagnostic/extractor changes to the inherited
  `scripts/catch_up/SimulationBasinMain.lean`.
- **Active campaign process:** no uncontrolled expensive computation is running. The original
  repeated-classifier `N=11` probe was stopped after 1,180.60 seconds with no output; the replacement
  shared-DAG gate passed in 198.46 seconds, and its production target build passed in 101.16 seconds.
  The failed direct `H_12` shared-solver probe was stopped after 359.50 seconds without output; the
  replacement literal window generator completed in under a second, and its full independent Lean
  check passed. Two read-only subagents are independently auditing the new generic modules and
  literal certificate. The symmetric
  every-opening transfer, end-to-end upper-gap trichotomy, small-gap structural bank, exact
  effective-total descent, and generic shared dense-certificate checker are integrated and have
  passed warning-strict target builds and root or independent axiom checks. The
  rigid deficit-one fixed-low response audit and the held-out `8 → 12` product literal
  has completed its independent audit. The
  configured ceiling in `HISTORICAL_TOOL_PATH` is 64, but this
  already-running goal experimentally exposes four active threads total, so all three non-root
  slots are recycled rather than restarting the campaign. A fresh attempt at 12:35 EDT to start the
  complementary upper-residual scout was rejected at the live-agent limit despite only two exposed
  non-root workers; the campaign recorded the limitation and will recycle the next completed slot
  without troubleshooting or restarting. The full unchanged-root matrix
  `D_11(b)→D_15(b)`, `b=2,…,10`, passed for both protected players, but remains exact finite
  evidence rather than a theorem.
- **Unresolved soundness concern:** finite product extraction is independently checked, and the
  preserved `7 → 11` and held-out `8 → 12` old-opening literals are now kernel-connected checked
  certificates; other held-out roots remain computational evidence. The history/liftability theorem is fully symbolic, but `LiftableNewOpeningRoots` is a
  proof-carrying sufficient condition, not an existence theorem derived from small safety. The 30
  low-hole states and the 120 selected first-generation paired responses are exact computational
  evidence, not certificates. The broad predicate `ledger-valid ∧ old discrepancy ≤ 4` is false,
  and even immediate discrepancy reduction fails at many safe owner nodes. Directly matching an
  old extra to a debt also exceeds the current single-residual representation in 15 stable phases;
  its combined value is nevertheless one of four bounded constants in the first generation. A
  concrete second-generation path can grow the resolved affine coefficient from magnitude two to
  four, but corrected enumeration shows that growth is avoidable. Multi-seed reruns confirm the
  CEGIS failure independently of the iterator bug: it reaches 101 macros and still leaves 25
  occurrences unresolved. The complete-even-set conjecture is false, and the canonical one-hole
  small-deficit tail class is forced open within two adversarial rounds at `C_12(3)`. These reject
  the bounded table, complete-set, and one-scalar tail mechanisms, not every richer root-specific
  four-lift relation.
- **Shortest recovery:** read this section; run `date`, `git status --short --branch`, and a
  process check; inspect any completed route-audit messages; continue from the exact next action.
- **Last completed verification:** a fresh post-window-integration full
  `lake --wfail build` passed all 9,010 jobs. Immediately before it,
  `lake --wfail build CatchUpResearch` passed all 8,135 jobs. The dedicated literal target
  `lake --wfail build catch_up.DenseAddTopWindowN11Certificate` passed all 8,075 jobs in 407 seconds.
  The new generic core and checker target passed all 8,069 jobs. Concrete window and `H_12` theorem
  axiom audits disclose exactly `[propext, Classical.choice, Lean.ofReduceBool,
  Lean.trustCompiler, Quot.sound]`; the two generic modules use only the standard logical axioms.
  Before this tranche, the prior
  `lake --wfail build CatchUpResearch` passed all 8,132 jobs, and the subsequent full
  `lake --wfail build` passed all 9,010 jobs with the newest dense modules. The dedicated
  `catch_up.DenseThreeHoleFiniteChecker` target then passed all 8,056 jobs, including native proofs
  at `N=9,10`, and `catch_up.DenseUpperGapPipeline` passed all 8,059 jobs. A fresh checker axiom
  audit confirms the generic soundness theorem has only `[propext, Classical.choice, Quot.sound]`,
  while the two finite test theorems additionally disclose `Lean.ofReduceBool` and
  `Lean.trustCompiler`. The new `catch_up.DenseThreeHoleCertificateChecker` target passed all 8,062
  jobs, `catch_up.SmallGapChildFamilies` and `catch_up.EffectiveTotalDescent` each passed all 8,052
  jobs, and the shared `catch_up.DenseThreeHoleN11Certificate` target passed all 8,067 jobs in
  101.16 seconds. Another final readback remains due after the current structural research wave.
  `git diff --check` is clean. The
  earlier all-opening `N=12` certificate and maximum-potential API remain warning-clean.
  The all-opening certificate's proof-relevant native trust boundary is explicitly audited; every
  theorem in the maximum-potential module has only the standard axioms. The reply-digraph
  target warning-strict build passes and all nineteen
  public theorem axiom audits show only `[propext, Classical.choice, Quot.sound]`. An earlier
  target build of the new `AdditiveTripleReduction.lean` passes all 8,056 jobs, and each of its
  eleven public theorem axiom audits has the same standard list. An earlier
  target build of `DenseHoleReduction.lean` passes all 8,054 jobs; its final bridge theorem uses
  only `[propext, Classical.choice, Quot.sound]`. An earlier
  post-extension build of `catch_up.DenseHoleHierarchy` passes all 8,055 jobs; its three public
  theorems and the new minimum-move bridge audit to the same standard axiom list. An earlier
  independent adversarial audit passed `LowerRayInteriorReduction.lean`. Its three theorems show only
  `[propext, Classical.choice, Quot.sound]`; the four-candidate classification, perspectives, and
  final quantifiers were independently checked. No `sorry`, `admit`, `axiom`, or `unsafe` occurs
  in either new module; `git diff --check` and the index check are clean.

## Baseline repository ownership manifest

At campaign start the Git index was empty. There were five inherited tracked modifications and
seventeen inherited untracked files. All are user-owned and must be preserved.

### Inherited tracked modifications

- `FormalConjectures/Paper/CatchUpConjecture.lean` —
  `71516f3a8a50346e7c41cd58db7a46f29252ca740ca43a464d4602a20f3bffd9`
- `scripts/catch_up/CommonOpeningTurnMain.lean` —
  `5c24db584b73c785f586480cb02b17980f2fbd54f0dc691b4f8f89e979617ec5`
- `scripts/catch_up/ExplicitTargetSoundness.lean` —
  `f062d280d6c4c36821286c4283460d1af4fe01281b1237efc7c173634f256377`
- `scripts/catch_up/FourCounterAttractor.lean` —
  `8fb781118abbda490aa9bbc35b82d25b13e124695e6becb8858d67d2b805d27a`
- `scripts/catch_up_compare.lean` —
  `a829df44ef7dba789a28c66afeaae5ed32d4aa3d0060f37c25c443746d18c111`

### Inherited untracked artifacts

- `CATCHUP_PROGRESS.md` —
  `b21c58ab1cfb3feae9f7e68f6644db380478df451490d1c6fc871972745e4236`
- `research-targets-2026-08-07.md` —
  `b40ad1881ccec109d6b8c81bc94886eb2e4bd888d7bda3a9c837e76394354807`
- `scripts/catch_up/AllReplyTurnMain.lean` —
  `d44a83874307274e59534bcb7f17cd8d82e934e418414a88e2dbd83b7e908dec`
- `scripts/catch_up/N11Certificate.lean` —
  `4fe0d76485aa022074386758ea0991e8c0cf3a1dd43331c16d394ebd2bb9a5da`
- `scripts/catch_up/N12Certificate.lean` —
  `8779dfb7010cbed7719ebbb3b383cf82e63833d46d545be830feed8739ba07d9`
- `scripts/catch_up/N15Certificate.lean` —
  `bb90ec85b7c9160ef53d89e39ba31f921f084e5b824451b7e5b9125d1138d010`
- `scripts/catch_up/N16Certificate.lean` —
  `0c2d2a40cc76a4e0c5558d74efb7402f676d51157d7271e097229b48a1a26304`
- `scripts/catch_up/PartialCertificateChecker.lean` —
  `44f0167123b313bc1bc8df71e5056cc8d310d6744ae61f7045f560af010782aa`
- `scripts/catch_up/PartialCertificateMain.lean` —
  `747272cea0bad6a23831ea94dbc7b9b56d8946b64f5454199f24cade51f51a4c`
- `scripts/catch_up/PartialCertificateSoundness.lean` —
  `0993d012852f2c4b523b63b90ef09d819568abf0c55cea968cdeea9c886e942d`
- `scripts/catch_up/PartialCertificateTargets.lean` —
  `676646955d5af82c591de0b00cb5f894c8e7eb96a88378b8cf310acfb3dc30ed`
- `scripts/catch_up/PartialStrategyExtraction.lean` —
  `29fe800617bb3dcce549ab286cf5f776b76ec10f5fcd2fc3a1e41dc47e1eac3e`
- `scripts/catch_up/SimulationBasinMain.lean` —
  `9b68a15a1860c35e8d882b350585b6042c435e1f69f26abcb10bfa5b219e00d6`
- `scripts/catch_up/SimulationLedger.lean` —
  `ed9656fd9afcd9ba55e0174db507239442846bfea1b91a11813b072294e67f42`
- `scripts/catch_up/SimulationSoundness.lean` —
  `3da1bda151339cd2478960d9f782ef28ba082a4bb9ddb6dd9b4460e949e7411f`
- `scripts/catch_up/TopFourClassification.lean` —
  `397a4eeb6e2cba91b983042928cd35bf9cf46a5da750c83a38d5fa5e5ff4cd6a`
- `scripts/catch_up/TopOnlyRegressionMain.lean` —
  `540a7eab14761bede17d22b00c8822b7682dbf3c26a2f55541249bce911b4211`

## Launch audit — 2026-08-08 22:06 EDT

- Exact checkout and branch matched the authorization.
- Other worktrees were inspected read-only and remain untouched.
- No staged changes, Git locks, active Lean/Catch-Up jobs, or recent writers were found.
- The prior checkpoint was read and its strongest claims, failures, trust boundaries, and next
  product-reflection gate were reconstructed without rerunning expensive computations.
- Three bounded read-only audits were launched: Route A diagnostics, Route B theoretical
  parity/uniqueness analysis, and Routes C/D feasibility. The primary agent remains the sole writer.

## Current approach-family registry — 2026-08-09 11:31 EDT

- **Exact four-counter product simulation:** finite checker/reflection and one literal basin are
  verified. Broad static width/ledger closure, universal fixed-width new-root transfer, and the
  tested consecutive-hole boundary pairings are blocked by exact counterexamples or failed roots.
  Reopen only for a new root-generated invariant, not by widening or table growth.
- **Root-generated new-opening packets:** the entry/history theorems are verified, but universal
  endpoint safety is false and a 24-macro/aggregate-ledger grammar proliferates under the second
  generation. Blocked unless a symbolic repair mechanism replaces exact-mask CEGIS.
- **Pair-deletion / tied consecutive-hole ray:** exact Lean reductions isolate canonical
  `A_N`/`B_N(b)` children, dense interior deficit-one nonloss, and four boundary openings. Every
  attempted bounded two-move, equal-sum, adjacent, complement-reflection, and one-hole-tail policy
  accumulates arbitrary punctures or fails on an exact child. Suspended unless a qualitatively new
  interval-specific invariant appears; do not reopen with a response table.
- **Parity, reachability, opening uniqueness, and draw-opening structure:** verified and banked.
  These sharpen certificates and reductions but do not alone decide the even-total conjecture.
- **Complete-set, one-hole small-deficit tail, abstract counter monotonicity, fixed equal-sum
  pairing, and generic reachable-position `+4`:** stopped by explicit counterexamples or forced
  escape from the proposed class. The complete-set failure now includes an exact subset-sum-
  complete even root loss, so even the weakened one-sided safety claim is false. Do not reopen
  under renamed predicates.
- **Direct exact frontier at `N=39/40`:** stopped as infeasible for this campaign without a compact
  strict-win signal/certificate; no such signal exists. No large dense solve is authorized.
- **Simpler interval-tail family `value(Icc 2 n)`:** blocked. Its first opening leaves the scalar
  family, descendants acquire arbitrary punctures, and adding a top block of four or a balanced
  bridge triple fails on explicit native-checked counterexamples.
- **Reply digraph on openings:** banked structural interface. A universal sink encodes a winning
  opening, while a loss forces a directed cycle; numeric edge decrease plus one neutral partner for
  opening `1` proves the interval draw. A drawn noninterval finite set with an induced directed
  cycle disproves generic cycle exclusion, and the all-pair premise is stronger than the lower-ray
  reduction. Suspended absent a new interval-specific rank mechanism.
- **Dense-hole hierarchy:** banked reduction, no longer an active primary gate. Lean proves that nonloss for every
  catchable even position with at most three holes implies the interval draw, and reduces the
  broader `3h≤N` hierarchy to saturated or prefix-blocked states. Exact independent checks find no
  loss in the three-hole target through `N=28`, but minimum, predecessor, short-block, and direct
  hereditary strategies all fail. Exact-sum injection terminates at explicit prefix-blocked
  deficit-one/two families. Reopen only with a non-hole-grammar saturated contradiction; any route
  that merely grows the hole set is blocked.
- **Exact-sum exchange and maximum-counter potential:** both yield clean verified local theorems.
  Exact-sum loss forces a larger unique residual winner relative to the chosen subset maximum;
  zero maximum potential has a complete draw/win classification. Neither gives a scalar chain:
  exact representability can disappear after one forced opening, and reachable states with the
  same maximum-potential signature have opposite values. Both standalone induction routes are
  stopped.
- **Finite all-opening certificates:** the shared checked DAG at `N=12` now proves every opening
  draws. This is strong finite infrastructure and a possible induction base, not evidence that the
  parametric transfer relation closes. Avoid duplicating the same expensive certificate at other
  sizes unless it directly supports a new symbolic transfer theorem.
- **Joint four-residue/add-one transfer:** blocked. Lean forces opposite values on the same
  endpoint pair state when the proposed winning opening changes, and exact dense states realize
  all four `W/L` behaviors under adjoining the top counter. This is generic add-one minimax, not a
  stable outcome transfer.
- **Completed-turn subset minimax:** exact warning-strict flattening is integrated and independently
  audited.
  This is a useful semantic/API theorem, but the reachable loss `({3,4,7,11},7)` proves that
  multiple exact subsets need not yield a safe endpoint. It is not yet a strategy.
- **Unbounded obligation/queue memory:** stopped. Even optimal arbitrary service of live mates for
  every fixed matching fails on `I_8`; dynamic same-quad service and exact-catch stacks also fail,
  while queue depth can grow arbitrarily without decreasing. Reopen only with an independent
  signed-residue endpoint theorem; encoding history or restating universal minimax is not progress.
- **Unprimed alternative mechanisms:** one independent scout remains active in each wave. Promote
  only exact quantified lemmas or independently checkable counterexamples.

## Launch-state formal verification — 2026-08-08 22:09 EDT

- `lake exe cache get` completed successfully and found no dependency files to download; it only
  refreshed the existing build cache.
- `lake --wfail build catch_up.SimulationLedger catch_up.PartialCertificateSoundness
  catch_up.N11Certificate catch_up.N12Certificate catch_up.N15Certificate
  catch_up.N16Certificate` passed all 8,073 jobs.
- A source scan found every expected theorem at its recorded location and no `sorry`, `admit`, or
  declared `axiom` in the audited proof/certificate modules.
- `#print axioms` reports exactly
  `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]` for each of the
  four finite draw theorems. This records the finite `native_decide` trust boundary accurately.
- `FourLiftGhost.exists_advance_check_eq_true_iff` and
  `ExplicitFourLiftLocallyClosed.to_basin` report only
  `[propext, Classical.choice, Quot.sound]`.
- Evidence label: the four finite draws and semantic bridge are `Lean-verified` under the stated
  trust assumptions. The residual search roots remain only `exact computational evidence` because
  the product-DAG reflection layer is absent.

## Experiment RA-1: missing player-one new-opening roots — 2026-08-08 22:11 EDT

- **Exact claim under test:** for each `k ∈ {1,2,3,4}`, if player one can avoid loss after opening
  `k` in the size-eight game, the current width-three, one-residual product relation contains the
  paired size-twelve root opened at `8+k`, initialized with the proved new-opening ledger.
- **Why it matters:** these are exactly the untested player-one new-root obligations needed before
  `EveryOpeningDraw` can be treated as a credible induction strengthening. The existing theorem for
  the main draw conjecture needs only one player-one opening, so failure would reject the stronger
  route, not the conjecture.
- **Current interface audit:** `runResidualOpeningOwner` is owner-generic, but both public new-root
  CLIs hardcode player two. Add a new wrapper/CLI rather than changing prior command semantics.
- **Possible outcomes:** all four required roots true supports further all-opening diagnostics; a
  required false root is to be minimized and freezes the stronger route; a root with
  `smallSafe=false` is vacuous and must not be counted as a transfer failure.
- **Expected runtime:** each root solves the size-eight and size-twelve opening graph. Based on the
  prior targeted player-two run, the full eight owner/root checks should be a bounded small-size
  computation, expected under ten minutes.
- **Hard stop:** ten minutes of computation or unexpected state growth; no solver refactor.
- **Planned command:** a newly added warning-clean CLI equivalent to
  `--async-residual-new-roots-all-owners 3 8`.
- **Artifacts:** only the additive wrapper in the inherited
  `scripts/catch_up/SimulationBasinMain.lean` and the present campaign ledger.

### RA-1 result — 2026-08-08 22:12 EDT

- Added `--async-residual-new-roots-all-owners LIMIT N` without changing the existing commands or
  recurrence. `lake --wfail build catch_up.SimulationBasinMain` passed all 8,062 jobs.
- Exact command:
  `lake env lean --run scripts/catch_up/SimulationBasinMain.lean
  --async-residual-new-roots-all-owners 3 8`.
- The run completed in under thirty seconds. Every small root was safe and every initial ledger was
  valid.
- Player two passed all four roots, reproducing the inherited result.
- Player one results:
  - `1 ↔ 9`: false after 1,755 searched labels;
  - `2 ↔ 10`: false after 49,354 labels;
  - `3 ↔ 11`: false after 3,128 labels;
  - `4 ↔ 12`: true after 150,730 labels, 18,482 winning.
- Each false trace ends when an adversarial sequence with a stuttering small guide grows pending
  old support from size three to four. The ledger equation remains valid; the width bound is the
  immediate obstruction.
- **Interpretation:** width three is not a symmetric all-opening invariant. This rejects the current
  relation as a proof of `EveryOpeningDraw` transfer, not `EveryOpeningDraw` itself and not the
  main Catch-Up conjecture. The main asymmetric draw reduction remains unaffected because it does
  not require player-one new-opening basins.
- **Evidence label:** exact computational evidence; the solver cache is not a formal product
  certificate.

## Experiment RA-2: smallest corrected pending width — 2026-08-08 22:12 EDT

- **Claim:** width four, with the otherwise unchanged one-residual relation, contains every
  player-one new-opening root at `8 → 12` whose small premise is safe.
- **Purpose:** distinguish a one-unit boundary correction from evidence that pending width continues
  to grow with the opening/root geometry.
- **Command:** `lake env lean --run scripts/catch_up/SimulationBasinMain.lean
  --async-residual-new-roots-all-owners 4 8`.
- **Expected runtime/hard stop:** under one minute expected, ten minutes maximum.
- **Outcome rule:** a pass is only corrected finite evidence; any failure is preserved and the
  symmetric route is suspended rather than widening repeatedly without a parametric explanation.

### RA-2 result — 2026-08-08 22:14 EDT

- The exact width-four command completed in under thirty seconds. Every small premise remained safe
  and every ledger was valid.
- Player-one `3 ↔ 11` and `4 ↔ 12` passed, but `1 ↔ 9` and `2 ↔ 10` remained false.
- The two failure traces extend the same stuttering adversarial pattern until pending support has
  cardinality five, where the width-four guard fails. Thus increasing the bound by one merely moves
  the obstruction by one step.
- Per the preregistered rule, no width-five sweep was run. The stronger symmetric all-opening route
  under this relation is **suspended**. This is evidence against a fixed small discrepancy bound for
  these roots, not evidence against `EveryOpeningDraw` or Catch-Up.
- The asymmetric ordinary-draw reduction and its player-two root evidence are unaffected.
- Source change retained from the diagnostic: the additive, warning-clean
  `--async-residual-new-roots-all-owners` wrapper. No recurrence, solver semantics, or existing CLI
  behavior changed.

## Initial portfolio review — 2026-08-08 22:19 EDT

- **Symmetric `EveryOpeningDraw` relation:** suspended. Width three failed three player-one new
  roots; width four still failed two and only moved the pending-width obstruction.
- **Parity/opening uniqueness:** mathematically clean and bankable, but no noncircular transformation
  currently converts one winning opening into a distinct winning opening. Natural complementation
  fails to preserve turn changes already at `N=4`.
- **Direct N=39/40 counterexample:** lowest expected value. Estimated exact payload is multiple TiB,
  no signal suggests a counterexample, strict-win certificate infrastructure is absent, and the
  available experimental C++ source is outside the authorized checkout.
- **Odd-total opening two:** parity would reduce it to one-sided safety, but it is outside the main
  conjecture and a meaningful `22 → 26` pilot requires new scalable C++ product infrastructure.
- **Leading directly relevant route:** the asymmetric root-specific width-three relation matching
  the exact draw criterion: one player-one old root and every player-two old/new root.
- **Bankable fallback:** prove odd weight excludes draw, with opening and one-sided-safety
  corollaries; then prove winning-opening uniqueness with its missing terminal branch if it supports
  a new strategy transformation.

## Experiment AR-1: held-out new player-two root at `12 → 16` — 2026-08-08 22:19 EDT

- **Claim:** the unchanged width-three, one-residual relation contains the paired new-opening root
  `1 ↔ 13` for protected player two, whose size-twelve small root is safe.
- **Why:** this is a required root of the exact asymmetric draw reduction and a next-size test not
  covered by the prior opening-one runs.
- **Command:** `lake env lean --run scripts/catch_up/SimulationBasinMain.lean
  --async-residual-new-root 3 12 1`.
- **Expected runtime:** one to five minutes based on prior size-twelve opening-one searches.
- **Hard stop:** ten minutes; no recurrence or solver refactor.
- **Outcome rule:** `smallSafe=true;root=false` suspends the relation and requires a minimized trace;
  `smallSafe=true;root=true` supports testing `k=2,3,4`. Either outcome remains exact computational
  evidence until product-certificate reflection is implemented.

### AR-1 result — 2026-08-08 22:26 EDT

- The root completed normally in roughly six minutes including compilation/polling overhead.
- Result: `smallSafe=true;required=true;root=true;ledgerValid=true`.
- Search size: 3,786,468 product labels, 305,506 winning.
- This is the first held-out next-size new-opening success for the exact asymmetric player-two
  obligation. It supports, but does not prove, a fixed width-three relation.
- Evidence label: exact computational evidence; no product certificate was emitted or checked.

## Experiment AR-2: remaining new player-two roots at `12 → 16` — 2026-08-08 22:26 EDT

- **Claim:** the unchanged width-three relation contains the required `k ↔ 12+k` player-two root
  for each `k=2,3,4` with a safe small premise.
- **Commands:** three sequential invocations of
  `--async-residual-new-root 3 12 K` for `K=2,3,4`.
- **Expected runtime/hard stop:** one to ten minutes per root; stop an individual process at ten
  minutes and do not begin the next until memory is released.
- **Outcome rule:** the first false required root suspends the relation and is minimized; all three
  true roots justify treating product-certificate reflection as viable verification infrastructure
  while old-root coverage is audited separately.

### AR-2 result — 2026-08-08 22:33 EDT

- All three roots completed normally and passed with safe small premises and valid ledgers:
  - `2 ↔ 14`: 369,079 searched / 44,813 winning;
  - `3 ↔ 15`: 1,347,285 searched / 134,833 winning;
  - `4 ↔ 16`: 284,188 searched / 36,719 winning.
- Together with AR-1, every required new protected-player-two root at `12 → 16` lies in the
  unchanged executable width-three relation. This is strong held-out evidence for the asymmetric
  reduction and sharply contrasts with the failed player-one symmetric strengthening.
- Evidence label: exact computational evidence, not formal basin membership.

## Bankable parity proof status — 2026-08-08 22:26 EDT

- A scratch module in `HISTORICAL_TMP/CatchUpParity.lean` now proves without `sorry`:
  - `Outcome.best_ne_draw_of_forall`;
  - perspective negation preserves non-draw;
  - legal picks preserve `deficit + remaining.sum` modulo two;
  - `Position.value_ne_draw_of_odd` by strong induction on remaining-cardinality.
- Direct Lean compilation is warning-free. This has not yet been integrated into a repository
  module or extended to opening/root corollaries.

### Bankable parity result integrated — 2026-08-08 22:33 EDT

- Added `scripts/catch_up/Parity.lean` as a separate research module; the upstream-facing conjecture
  file was not enlarged.
- Public Lean-verified results include:
  - legal picks preserve parity of deficit plus remaining sum;
  - `Position.value_ne_draw_of_odd`;
  - every opening of an odd-total game is non-drawing;
  - the whole odd-total game is non-drawing;
  - one player-one `CanAvoidLoss` opening in an odd-total game implies strict root value `.win`.
- `lake --wfail build catch_up.Parity` passed all 8,052 jobs. No placeholder or declared axiom occurs
  in the module. The two principal parity theorems report only
  `[propext, Classical.choice, Quot.sound]`.

## Route-selection gate — 2026-08-08 22:33 EDT

- **Principal route (approximately 65%):** the asymmetric, root-specific, width-three
  one-residual relation matching the exact draw quantifiers. First complete the held-out
  player-two old-root falsification gate; then implement product-DAG reflection only if it passes.
- **Adversarial workstream (approximately 20%):** search each required old root independently and
  stop/minimize at the first failure; audit any checker against solver/extractor independence and
  the formal quantifier order.
- **Bankable fallback/integration (approximately 15%):** the now-proved parity package; winning-
  opening uniqueness only if it supports a noncircular transformation or an independently useful
  theorem.
- **Suspended:** symmetric `EveryOpeningDraw` under fixed small pending width, direct exact N39/N40
  solving, and a new C++ opening-two product implementation.

## Experiment AR-3: protected-player-two old roots at `12 → 16` — 2026-08-08 22:33 EDT

- **Claim:** for each legal old opening `x ∈ [1,12]`, protected-player-two safety transfers from
  the size-twelve root to the same opening at size sixteen inside the width-three relation.
- Opening one already passed in the inherited `--async-residual 2 12` run. Test openings `2..12`
  one at a time to permit early falsification and bounded memory.
- **First command after adding a focused CLI:** equivalent to
  `--async-residual-old-root 3 12 2`.
- **Hard stop:** ten minutes per root; no simultaneous solves. A false required root is preserved
  and stops the sequence. If all pass, the finite relation covers every exact theorem root at the
  first next induction pair, justifying product-certificate reflection.

### AR-3 opening-two result — 2026-08-08 22:37 EDT

- Added the focused, additive diagnostic CLI
  `--async-residual-old-root LIMIT N OPENING`; it calls the existing owner-generic recurrence for
  protected player two and does not change the recurrence, target predicate, or solver.
- `--async-residual-old-root 3 12 2` completed normally with
  `smallSafe=true;required=true;root=true;ledgerValid=true`.
- Search size: 1,283,785 product labels, 135,342 winning.
- Evidence label: exact computational evidence, not formal basin membership. Continue sequentially
  with opening three; retain the same ten-minute hard stop and stop at the first false root.

### AR-3 opening-three result — 2026-08-08 22:41 EDT

- `--async-residual-old-root 3 12 3` completed normally with
  `smallSafe=true;required=true;root=true;ledgerValid=true`.
- Search size: 1,429,610 product labels, 180,466 winning.
- Continue with opening four under the unchanged stop rule.

### AR-3 opening-four result — 2026-08-08 22:44 EDT

- `--async-residual-old-root 3 12 4` completed normally with
  `smallSafe=true;required=true;root=true;ledgerValid=true`.
- Search size: 393,147 product labels, 47,016 winning.
- Continue with opening five under the unchanged stop rule.

### AR-3 opening-five result — 2026-08-08 22:49 EDT

- `--async-residual-old-root 3 12 5` completed normally with
  `smallSafe=true;required=true;root=true;ledgerValid=true`.
- Search size: 330,146 product labels, 47,163 winning.
- Continue with opening six under the unchanged stop rule.

### AR-3 opening-six result — 2026-08-08 22:54 EDT

- `--async-residual-old-root 3 12 6` completed normally with
  `smallSafe=true;required=true;root=true;ledgerValid=true`.
- Search size: 406,620 product labels, 57,971 winning.
- Continue with opening seven under the unchanged stop rule.

### AR-3 opening-seven result — 2026-08-08 23:00 EDT

- `--async-residual-old-root 3 12 7` completed normally with
  `smallSafe=true;required=true;root=true;ledgerValid=true`.
- Search size: 363,849 product labels, 54,943 winning.
- Continue with opening eight under the unchanged stop rule.

### AR-3 opening-eight result — 2026-08-08 23:02 EDT

- `--async-residual-old-root 3 12 8` completed normally with
  `smallSafe=true;required=true;root=true;ledgerValid=true`.
- Search size: 329,061 product labels, 49,765 winning.
- Continue with opening nine under the unchanged stop rule.

### AR-3 opening-nine result — 2026-08-08 23:04 EDT

- `--async-residual-old-root 3 12 9` completed normally with
  `smallSafe=true;required=true;root=true;ledgerValid=true`.
- Search size: 242,372 product labels, 32,552 winning.
- Continue with opening ten under the unchanged stop rule.

### AR-3 opening-ten result — 2026-08-08 23:05 EDT

- `--async-residual-old-root 3 12 10` completed normally with
  `smallSafe=true;required=true;root=true;ledgerValid=true`.
- Search size: 151,859 product labels, 19,860 winning.
- Continue with opening eleven under the unchanged stop rule.

### AR-3 opening-eleven result — 2026-08-08 23:07 EDT

- `--async-residual-old-root 3 12 11` completed normally with
  `smallSafe=true;required=true;root=true;ledgerValid=true`.
- Search size: 165,671 product labels, 23,563 winning.
- Continue with opening twelve, the final old-root obligation.

### AR-3 complete result — 2026-08-08 23:08 EDT

- `--async-residual-old-root 3 12 12` completed normally with
  `smallSafe=true;required=true;root=true;ledgerValid=true`.
- Search size: 64,273 product labels, 8,977 winning.
- Openings `2..12` all passed; opening one had already passed in the inherited width-two run and
  therefore also satisfies width three. Together with AR-1/AR-2, the unchanged width-three,
  one-residual executable relation contains every protected-player-two old and new root required
  at `12 → 16`.
- This is a decisive held-out finite validation of the asymmetric root family. It remains exact
  computational evidence until certificates for those roots are independently checked; it is not
  a symbolic closure theorem.

## Product-certificate soundness core — 2026-08-08 22:49 EDT

- A scratch module now compiles a minimal independent product-certificate contract whose key is
  `(small State, large State, FourLiftLedger)` and whose edges contain a large counter, an optional
  ghost counter, and an exact child key.
- The checker independently requires bounded encoded states, root/node containment and key
  uniqueness, parent `Related`, proof-backed targets or safe terminals, one legal owner edge or
  exhaustive opponent edges, exact large children, strict progress, and `advanceCheck = true`.
- Lean proves `DAGValid → ExplicitFourLiftLocallyClosed` and
  `checkCertificate = true → root ghost safety → ExplicitFourLiftBasin`.
- This is a scratch-validated theorem shape, not yet a repository artifact; it has not checked any
  emitted executable witness. The generator and literal-certificate path remain the next gate.

### Product-certificate soundness integrated — 2026-08-08 22:54 EDT

- Added `scripts/catch_up/FourLiftCertificateChecker.lean` as a new module, leaving the semantic
  ledger module unchanged.
- `lake --wfail build catch_up.FourLiftCertificateChecker` passed all 8,067 jobs.
- The checked contract uses a single independently classified leaf constructor, exact child keys,
  exhaustive decoded opponent counters, and the proved `advanceCheck` bridge. The solver and
  residual updater are not imported.
- A one-node terminal product certificate was checked end-to-end in `/private/tmp` with
  `native_decide`, and its basin theorem elaborated. This smoke test carries the normal Lean native
  compiler trust boundary; the general soundness theorems themselves do not use `native_decide`.

### First nontrivial extracted product certificate — 2026-08-08 23:08 EDT

- Command: `lake env lean --run scripts/catch_up/SimulationBasinMain.lean
  --check-four-lift-old-root 3 7 1 p2`.
- The residual search examined 5,404 labels. The selected product certificate has 464 nodes.
- Independent results: `dagCheck=true`, `rootSafeCheck=true`, and `rootMatches=true` against a
  separately encoded opening-one key.
- This closes the executable edge/branch/root verification loop in memory: the untrusted extractor
  selected the data, while the new checker recomputed all proof obligations and its Lean theorem
  converts acceptance to basin membership.
- The artifact is not yet durable or directly importable as a theorem because the 464-node DAG has
  not been serialized. The immediate next action is deterministic literal emission, a
  `native_decide` check of that literal, and a root-decoding bridge theorem.

### First Lean-verified product-basin certificate — 2026-08-08 23:13 EDT

- Emitted the deterministic 464-node DAG to the new, uniquely named module
  `scripts/catch_up/FourLiftN7P2Old1Certificate_20260808.lean` (516 lines, 117,660 bytes after the
  root-bridge correction).
- The first compile exposed two packaging issues only: `FourLiftGhost` has no blanket
  `DecidableEq`, and the old-opening basin abbreviation had to be unfolded before rewriting. The
  componentwise root proof and explicit unfolding fixed both; the certificate data itself was
  accepted unchanged.
- `lake --wfail build catch_up.FourLiftN7P2Old1Certificate_20260808` passed all 8,068 jobs.
- Lean theorem
  `CatchUpSearch.FourLiftN7P2Old1Certificate.old_opening_basin` proves
  `ExplicitFourLiftOldOpeningBasin 7 .p2 1` from the literal data and the independent checker.
- The theorem and its Boolean certificate check have exactly
  `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`, accurately
  recording the `native_decide` trust boundary. No `sorry`, `admit`, or declared `axiom` occurs.
- SHA-256 of the checked literal module:
  `80e61a08942e4ed638b3761952cec7545ac222df2740e836b313b8f5632e8c5d`.
- After rebuilding the emitter, a second generation to a unique `/private/tmp` path produced the
  identical SHA-256 and `cmp` reported byte-for-byte equality. This checks deterministic
  reproducibility without overwriting the preserved artifact.
- Evidence label: **Lean-verified** finite basin membership under Lean's standard native-code
  checking trust model. This is a rigorous new finite simulation result, not yet a parametric
  transfer theorem.

## Parametric relation refinement — 2026-08-08 23:07 EDT

- The failed symmetric new-root tests have a structural, not merely finite, explanation. At a
  player-one-protected new root the large player two can make an arbitrarily long sub-deficit old
  sequence while the small ghost can advance at most once; therefore no fixed pending-width
  symmetric relation can cover all such opponent sequences as `N` grows.
- The asymmetric player-two roots instead have a uniform entry construction. For opening
  `k ∈ [1,4]`, mirror one complete safe small player-two turn, then let the large game take
  `N+j`, where `j=2` for `k=1` and `j=1` otherwise. Both games then have player one to move; the
  large state is the small state plus an explicit three-counter packet, its deficit differs by
  `j ≤ 2`, pending old support is `{k}`, and the original new-opening ledger remains exact.
- An independent mathematical audit confirmed the construction under `1 ≤ k ≤ 4`, `k ≤ N`,
  and small player-two safety. It is an entry/path-reduction lemma only: safety of every resulting
  three-packet state remains the genuine parametric gate.
- After the first nontrivial product certificate is checked, the highest-value symbolic target is
  to formalize this entry lemma and falsify/prove closure of the three-packet descendant family,
  rather than mining an unrestricted exact-mask controller.

### Uniform three-packet entry reduction formalized — 2026-08-08 23:34 EDT

- Added `scripts/catch_up/NewOpeningEntry.lean` as a separate research module; no core conjecture
  or upstream-facing API file was enlarged.
- Defined explicit mirror, ready, and three-packet phase predicates. Lean proves the paired
  new-opening roots begin in the mirror phase; every below-deficit old pick preserves it; the
  small catching pick enters the ready phase; and a distinct top reply `N+j` enters the exact
  three-packet phase.
- Lean theorem `NewOpeningMirrorPhase.can_avoid_loss` is uniform in `N`: a safe player-two small
  mirror state transfers to the large state provided all safe three-packet endpoints transfer.
  Its well-founded induction follows an arbitrarily long safe small turn and therefore uses no
  bounded move list or finite-size enumeration.
- Lean proves the endpoint identities `pending = {k}` and
  `consumedTop = {N+k, N+j}` and then proves
  `NewOpeningThreePacket.consistent_new_opening_ledger`. Thus the packet relation satisfies the
  exact semantic score ledger, with represented gap `-j`.
- `lake --wfail build catch_up.NewOpeningEntry` passed all 8,066 jobs. Both principal theorem
  axiom audits report exactly `[propext, Classical.choice, Quot.sound]`; there is no native-code,
  solver, `sorryAx`, or generated-certificate dependency.
- **Evidence label:** Lean-verified conditional parametric reduction and ledger relation. The
  endpoint safety implication remains the exact research gate; no unconditional `N → N+4` result
  follows yet.

## Experiment TP-1: exhaustive safe first-turn endpoints — 2026-08-08 23:55 EDT

- Added `--three-packet-endpoints N [N ...]`. For each `k=1..4`, it traverses every exact-solver
  child annotated safe for player two while the first post-opening turn continues, stops when the
  mover first becomes player one, constructs the endpoint for each `j∈[1,4] \ {k}`, and queries
  the corresponding large solved graph.
- Scope is explicitly `all-safe-small-first-turn-endpoints`. The traversal uses exact-solver
  annotations and an unchecked-but-audited bitmask construction; results are discovery evidence,
  not proof-backed exhaustive endpoint theorems. Missing constructed states are reported
  separately and none occurred.
- `7 → 11`: the universal endpoint premise fails for canonical `j` at `k=1,4`; all `j` fail for
  some safe endpoint at `k=4`. Nevertheless every `(k,j)` has at least one safe immediate endpoint,
  and the simple catch move `x=k+1` is safe in both small and large states for every valid `j`.
- `8 → 12`: the universal endpoint premise fails for every `j` at `k=1,2,3`; `k=4` passes for
  `j=2,3`. Again `x=k+1` is a safe immediate small/large endpoint for every `(k,j)`.
- `11 → 15`: every one of 75 safe first-turn endpoints is safe for all three valid replies;
  equivalently all 225 tested endpoint pairs pass. Every `x=k+1` immediate endpoint passes.
- `12 → 16`: endpoint counts by `k` are `11,20,28,39`; all 98 endpoints are safe for all three
  replies, so all 294 endpoint pairs pass. Every `x=k+1` immediate endpoint passes.
- The false `NewOpeningThreePacketTransfer` premise is therefore too broad at the small bases, but
  the entry strategy remains viable through endpoint selection. A theoretical audit explains the
  correct finite history: if `A` is the set of old counters already mirrored before the catch,
  then `A.sum < k ≤ 4`, so only eleven preparation sets are possible across all four roots. The
  catch counter and `N` remain parameters. This root-generated family is the selected primary
  relation for the next phase.
- **Evidence label:** exact computational evidence with an independently Lean-verified entry
  theorem. No universal endpoint-transfer theorem or unconditional new-opening transfer is proved.

## Root-generated selected-turn reduction — 2026-08-09 00:08 EDT

- Added `scripts/catch_up/NewOpeningHistory.lean`. Its phase records the exact set `A` of old
  counters mirrored before the first catch-up pick, with
  `A.sum + small.deficit = k`, `A.sum < k`, and exact dense remaining support. Lean proves the
  paired roots have empty history and that every below-deficit mirrored pick inserts its counter
  while preserving the phase.
- For valid `k ≤ 4`, every preparation counter belongs to `{1,2,3}`; in fact the mathematical
  audit sharpens the currently proved cardinality bound from three to two. The exact possible
  histories are `∅`; `{1}`; `{2}`; `{3}`; and `{1,2}`, subject to `k`.
- Defined `NewOpeningLiftableTurn`, an explicit proof-carrying selected strategy. Its `step`
  constructor chooses a safe below-deficit old pick; its `finish` constructor chooses a safe
  catching old pick and a distinct added-counter reply with a safe large endpoint. Lean proves a
  liftable selected turn makes the large root safe and that liftability at all four roots implies
  `FourLiftNewOpeningTransfer N .p2`.
- An independent read-only proof audit found no soundness gap. The generic history and transfer
  theorems build warning-strict and use only `[propext, Classical.choice, Quot.sound]`.
- Important scope: liftability is a sufficient selected-mirroring template, not a consequence of
  small safety and not a necessary condition for the underlying transfer. The endpoint safety is
  still supplied as certificate data.

### Finite selected-turn regressions

- Added `scripts/catch_up/NewOpeningHistoryRegression.lean`. At each `k=1..4`, it chooses the
  immediate catching old counter `x=k+1`; the large game then uses reply offset `j=2` for `k=1`
  and `j=1` otherwise.
- The exact proof-backed `CanAvoidLossClassifier` verifies every small and large endpoint. Lean
  therefore proves `FourLiftNewOpeningTransfer 7 .p2` and
  `FourLiftNewOpeningTransfer 8 .p2`, despite the already-minimized failures of the stronger
  universal-endpoint statement.
- `lake --wfail build catch_up.NewOpeningHistoryRegression` passed all 8,068 jobs.
- SHA-256: `NewOpeningEntry.lean`
  `715fab2a22702b1d4c0ca428bdcb6b29523e1c931dc63f048895d48372dfd46b`;
  `NewOpeningHistory.lean`
  `96a29d42d97df961a5792ec3133239b578c4d3e25b4a6a518d3f10da75b729a8`;
  `NewOpeningHistoryRegression.lean`
  `37547d2d8ecd6cf734382209f7d8e4bd9c8904e2696d13e902bdda68cf2722c0`.
- The four finite regression theorems have axioms
  `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`, accurately
  recording their `native_decide` trust boundary. The structural reduction remains kernel-checked
  without native evaluation.
- **Evidence label:** Lean-verified finite new-opening transfers at `7` and `8`, plus a
  Lean-verified conditional parametric selected-turn reduction. This is meaningful progress on
  the exact player-two quantifier, but not yet a uniform `N ↦ N+4` theorem.

## Dense immediate endpoints and balancing responses — 2026-08-09 00:37 EDT

- Added `scripts/catch_up/NewOpeningImmediate.lean`. For `k < N`, define the state reached after
  large opening `N+k`, immediate old catch `k+1`, and distinct top reply `N+j`. Lean proves its
  exact normalized form:
  `remaining = Icc 1 (N+4) \ {k+1,N+k,N+j}`, `deficit = j+1`, and `toMove = p1`.
- Defined `ImmediateNewOpeningEndpointsSafe N`: for each `k=1..4`, some valid `j` makes this dense
  endpoint safe for player two. Lean proves that this single concrete family implies the complete
  `FourLiftNewOpeningTransfer N .p2` for every `N ≥ 5`. The conclusion is unconditional large-root
  safety; it does not need or hide a small-root premise.
- Proved a generic completed-turn balancing macro. If the opponent prepared total `s`, caught with
  `y`, and left deficit `y+s-d`, then replies `s+t` and `y-t`, for `t<y-d`, score exactly the same
  total and restore deficit `d` and the original mover. The additive high/middle/low triple is a
  direct corollary.
- For a surviving top `N+h` and `N≥11`, proved a finite arithmetic choice theorem: one restored
  offset `a∈{k,j}` makes `t=4+h-a`, first reply `s+t`, and second reply `N-4+a` have the required
  ranges, avoids the fixed old hole `k+1`, avoids repeating the second counter, and satisfies the
  balancing inequality. A formal legal-move corollary is being checked independently.
- Exact-solver policy mining found that every opponent complete turn has form `[y]` or `[1,y]`.
  A small normalized response policy covered `88/88` branches at `N=11` and `96/96` at `N=12`;
  it intentionally fails some branches at the smaller finite bases (`45/56` at `N=7`, `56/64`
  at `N=8`), so the pattern is not a tautology or solver-order artifact.
- The sole multi-pick nearest-neighbor exception is `k=3`, opponent `[1,N+4]`, reply `[N+2,2]`.
  An independent focused exact recurrence verified every intermediate state and final safety at
  `N=7,8,11,12`; final state is `Icc 3 N \ {4}`, deficit `1`, player one to move.
- A direct `E_N → E_{N-4}` pairing is false. The high response instead leaves a bounded low-hole
  plus one-extra-packet phase. Direct catches at `y=d` or `d+1` also prove that no single
  equal-score phase can be closed: player two must enter a shifted-deficit boundary phase.
- `lake --wfail build catch_up.NewOpeningImmediate catch_up.NewOpeningHistoryRegression` passed
  all 8,069 jobs. `NewOpeningImmediate.lean` is 208 lines, SHA-256
  `7ca7f08d7218516543ebe73dae88111804551abf9186a83811306d2ae8498345`.
  Its principal theorems use only `[propext, Classical.choice, Quot.sound]`.
- **Evidence label:** the endpoint reduction, balancing arithmetic, and finite choice are
  Lean-verified parametric results. Policy coverage and endpoint safety remain exact computational
  evidence. The low-hole/one-packet closure is the remaining research gate.

## End of initial discriminating phase and route decision — 2026-08-09 01:02 EDT

- The symmetric fixed-width `EveryOpeningDraw` route remains suspended: protected-player-one new
  roots produced a parametric stuttering obstruction, and increasing width merely delayed it.
  Exact N=39/40 solving and the odd-total opening-two route remain too indirect or too expensive.
- The asymmetric protected-player-two route survived every required held-out new root at
  `12 → 16`. A sound product checker and one literal `7 → 11` old-root product certificate now
  establish that finite product witnesses can be independently reflected into the semantic basin.
- The initial product relation was then sharpened theoretically. Lean now proves that the canonical
  new-opening strategy reaches the dense endpoint
  `Icc 1 (N+4) \ {k+1,N+k,N+j}` with deficit `j+1` and player one to move, where the canonical
  reply is `j=2` for `k=1` and `j=1` otherwise. Canonical endpoint safety at all four offsets is a
  named sufficient condition for the complete player-two new-opening transfer.
- Every completed player-one turn from this endpoint is Lean-classified as either `[y]` or
  `[1,y]`. Relative to the size-four-smaller endpoint, the support is exactly that endpoint plus a
  four-counter packet: two restored near-top counters and two surviving new top counters.
- For a catch on either kind of packet counter, Lean constructs a legal two-pick player-two
  balancing response and proves that it restores the endpoint deficit and player one as mover.
  The trace-to-state theorems connect actual legal turns to the symbolic records used by these
  response theorems; no external state formula is trusted.
- Exact structural enumeration shows that high-packet responses land in 30 normalized child types
  for every `N ≥ 12` (27 at `N=11` because of three benign counter collisions). All types are
  exact-solver safe at `N=11,12,15,16`; the proof-backed classifier independently confirms all 27
  types at `N=11`. These are computational results, not general safety theorems.
- A pure equal-score strategy is decisively not recursive. Minimal common-counter obstructions are
  identical across `N=11,12,15,16`. The meaningful relation must mirror common moves through a safe
  smaller position and use balancing only on packet extras.
- In the resulting paired phases, a restored-low balance has one old large-only credit and two old
  small-only debts; a high balance has one of each. The apparent five-counter difference includes
  two fixed top slots, so the variable old discrepancy is at most three. However, the broad static
  predicate `ledger-valid ∧ discrepancy ≤ 4` is already false. The missing strategic invariant is
  `Repairable`: at aligned owner nodes there is a safe paired edge reducing old discrepancy, and
  opponent/common/skew transitions preserve that repairability.

### Selected portfolio

- **Primary route (about 65%):** synthesize and prove the root-generated hybrid `Repairable`
  relation. First complete the exact falsification gate on the 30 stabilized types; then state only
  the smallest surviving relation and prove its local owner/opponent closure in Lean.
- **Adversarial route (about 20%):** search all paired common moves and skew transitions, compare
  `N=11,12` with held-out `15,16`, and minimize the first failure. Do not widen the ambient ledger
  relation or add exact-mask cases without a human-readable parametric explanation.
- **Verification/fallback (about 15%):** preserve warning-strict structural Lean theorems and use
  the product checker only for end-to-end smoke tests. If no precise finite repairable relation with
  positive held-out evidence exists by the next substantive review, bank winning-opening
  uniqueness/reachable-state bounds and pivot to the strongest rigorously isolated obstruction.
- **Next review/stop gate:** approximately 02:30 EDT, or immediately on a decisive repairability
  failure. Continuing the route requires either a stable finite successor vocabulary or a precise
  theorem reducing closure to finitely many symbolic cases.

### Verification snapshot

- `lake --wfail build catch_up.NewOpeningImmediate` passed all 8,068 jobs after integrating the
  packet decomposition, canonical turn classification, trace-to-state bridge, and both legal
  balancing-response theorems.
- `NewOpeningImmediate.lean` is 802 lines / 39,607 bytes, SHA-256
  `71d390b931a0aaae934b8d5c3dd53c01664bd05d45e7676c7f58f8b129332e0e`.
- `#print axioms` for every newly audited structural theorem reports only
  `[propext, Classical.choice, Quot.sound]`. `git diff --check` is clean and the Git index remains
  untouched.

## Oriented repair API and first-generation affine grammar — 2026-08-09 01:21 EDT

- Added `scripts/catch_up/NewOpeningRepair.lean`. It separates the old pending symmetric
  difference into oriented small-only debts and large-only credits. Lean proves that common paired
  picks preserve both oriented sets when the counter is common; a debt-credit substitution lowers
  old pending width by exactly two; and a debt-top substitution lowers it by exactly one.
- Lean also proves the exact alignment boundary for a common mirrored counter: the child movers
  agree if and only if that counter is below both deficits or catches in both games. A threshold
  straddle is therefore precisely the one-step skew case. These are set/transition facts only; they
  do not assert legality or strategic safety of a chosen substitution.
- The initial stronger `Repairable` predicate was falsified: among 183 aligned player-two-owner
  children at `N=11`, only 81 admit an immediately discrepancy-reducing ledger-valid safe paired
  edge, and only 24 do so while keeping movers aligned. This rejects compulsory immediate repair,
  not delayed bounded repair.
- A separate paired computation then treated each of the 30 stabilized high-balanced phases at
  sizes `N` and `N+4`. Across 120 affine packet challenges, it found a common vocabulary of 24
  literal/affine macros that succeeds in all 120 cases at both `12 → 16` and held-out `15 → 19`.
  Responses use one pick in 40 cases, two in 73, and three in seven. Every successor has old
  discrepancy zero or one; normalization yields 40 support/debt phases and 51 signed-ledger
  phases. The selected endpoints are exact-solver safe at both sizes.
- This is positive but still first-generation evidence. The computation may still be consulting
  exact states to select among the 24 macros, and the 40 successor phases have not yet been shown
  closed. The next experiment freezes the vocabulary and advances all of them through one further
  adversarial generation at both size pairs. A growing phase count or size-specific fallback will
  be treated as an obstruction, not hidden by enlarging the grammar.
- `lake --wfail build catch_up.NewOpeningRepair` passed all 8,069 jobs. Current hashes:
  `NewOpeningImmediate.lean`
  `d0b3704cab484eeb0b8d897b52d94e6d5b27485e080ca35b0728be83382fc1b5`;
  `NewOpeningRepair.lean`
  `7978069a529432ad717359b2bf76cefe731d5f1499524e63408e4f62cb635d76`.
  The axiom audit for every theorem in the new repair API reports only
  `[propext, Classical.choice, Quot.sound]`.

## Common-move semantic closure and aggregate-residual obstruction — 2026-08-09 01:42 EDT

- Strengthened `NewOpeningRepair.lean` from support arithmetic to an actual simulation case. If an
  old counter remains in both positions, the movers agree, and the corresponding ghost pick is
  supplied as an explicit `AlignedSafeGhostStep`, Lean proves that reusing the same ledger is a
  `FourLiftGhost.Advances` transition. The proof establishes the pointwise `HistoryStep`, child
  `Supports`, and numerical `ValueStep` separately. Thus the infinite family of common moves needs
  no phase-table ledger algebra; only the strategic choice of a safe ghost move remains external.
- Lean also proves that common mirroring preserves mover alignment exactly when the counter has the
  same catch/continue comparison in both games. If a threshold straddles and the large child has
  deficit zero, any next large pick realigns the movers and makes that counter the new deficit.
- An independent exact replay of all 30 stable high-balanced phases found 210 aligned player-two
  owner nodes at `N=12`: 205 use the ordinary conditional common/debt rule and five use a fixed
  literal/affine exception table. The same five macros replay safely and ledger-validly at held-out
  `N=15` and fresh `N=16`; the exceptions disappear entirely at those larger sizes. Three are
  distinguished `(p2,p1; 1,0)` skew phases and realign safely after every legal next large move.
- A width-minimizing response was decisively falsified: one affine response is safe at `N=12` and
  `N=16` but unsafe at `N=15`. The controller therefore may use discrepancy width as a bound, not
  as a greedy selection criterion.
- More importantly, direct old-extra/debt matching exceeds the existing optional-one-residual
  ledger in exactly 15 of 30 phases (`a=k`) at every tested stable size. Several resolved counter
  contributions coexist, but their total simplifies symbolically to
  `2 * (j - k - q)` and takes only `{-10, -12, -14, -16}` in this generation. This is a persistent
  representation obstruction, not a game-safety failure. A sound aggregate `resolvedValue : ℤ`
  ledger is being audited, together with a falsification test for unbounded accumulation.
- The preserved first-generation replay was independently rerun by the primary agent and exactly
  reproduced `120/120`, 24 macros, 40 support phases, 51 signed-ledger phases, widths `{0:35,1:85}`
  in 20.2 seconds. Script SHA-256:
  `a7e6c4b797685743851c6c745efac170e42da57d7385a9d36b224e6a00e6f2a0`; report SHA-256:
  `3129ea7fca92441619518a0b52cdb706886f62101fb2b38238197c05343705c3`.
- A static audit caught an undercoverage risk in the initial second-generation script: it retained
  only the first occurrence of a normalized support/ledger key even though that key did not encode
  the complete common-hole support. The corrected gate must traverse all 120 reachable
  occurrences (or prove a stronger key determines them); no deduplicated phase count will be
  accepted as exhaustive by itself.
- `lake --wfail build CatchUpResearch` passed all 8,099 jobs. `NewOpeningRepair.lean` is presently
  426 lines before the next hash refresh; its complete axiom audit reports only
  `[propext, Classical.choice, Quot.sound]`.

## Aggregate history semantics and corrected second-generation gate — 2026-08-09 01:58 EDT

- Added `scripts/catch_up/AggregateSimulationLedger.lean` rather than weakening or mutating the
  inherited one-residual semantics. Its ledger stores the two visible sign supports and one
  persistent `resolvedValue : ℤ`, interpreted as the total score-gap contribution of old counters
  that have disappeared from both games. `Supports` retains the old support bounds, an explicit
  pending-width parameter, and evenness of the resolved value.
- The aggregate `HistoryStep` is provenance-preserving, not a fresh numerical decomposition. For
  every old counter still visible in either child, its signed coefficient must equal its parent
  coefficient plus the exact large-pick/ghost-pick delta. Top-counter coefficients obey the
  existing pointwise history equation. Every coefficient that disappears is transferred by a
  finite sum into the child `resolvedValue`, which is therefore uniquely determined by the parent
  and transition.
- Lean proves a finite executable history checker equivalent to that semantic equation, a sound
  aggregate `advanceCheck`, preservation of consistency/relatedness/small safety, lossless
  embeddings of the old empty and new-opening ledgers, and a locally-closed-relation theorem that
  yields `CanAvoidLoss` by well-founded induction on the large remaining-cardinality. `ValueStep`
  remains checked independently, which keeps the strategic checker sound without first deriving
  it from the aggregate history sum.
- This representation is sound only along canonical roots and checked monotone game transitions;
  static consistency alone still permits re-explanation and is not treated as provenance. No
  empirical bound on `resolvedValue` is baked into semantic support. A bounded or affine phase
  restriction, if one survives, belongs to the strategic relation.
- The preserved second-generation occurrence audit exposed two distinct issues. First, exact
  common-hole masks produce many concrete states but are meant to be covered by the generic
  common-move theorem, not enumerated as finite control. Second, under the frozen first-generation
  macro choices, a selected path changes resolved value from `-2*N-4` to `-4*N-10` after one more
  response. This shows that the four first-generation constants are not themselves an invariant;
  the remaining decisive question is whether coefficient growth is forced for every shared
  affine response or avoidable by a different small controller.
- The corrected gate now traverses all 120 root-generated occurrences, enforces mover legality on
  ghost moves, classifies common moves separately, and permits only literal/bounded-affine macros
  shared between `N=12` and held-out `N=15`. A need for exact masks/interior counters, more than
  100 macros, or unavoidable recurrent coefficient growth will suspend this controller route at
  the 02:30 review rather than be hidden by enlarging the grammar.
- `lake --wfail build CatchUpResearch` passed all 8,100 jobs. Current source facts:
  `AggregateSimulationLedger.lean` is 519 lines / 26,144 bytes, SHA-256
  `4a47ded8f9c87344c4dd2e10b54731ffda29c3ee947a483a5d158f03005da7e4`;
  `NewOpeningRepair.lean` is 426 lines / 19,115 bytes, SHA-256
  `7987826b5a2098a2657825e7fd3779fcbd843744cd9a37a0572cd18182510b79`.
  Every audited theorem in both APIs reports only
  `[propext, Classical.choice, Quot.sound]`; `git diff --check` is clean and the index is empty.

## Finite affine-controller route provisionally suspended — 2026-08-09 02:00 EDT

- The corrected paired-generation audit retained all 120 first-generation occurrences, enforced
  mover legality, and treated ordinary common moves through the generic mirror case rather than
  enumerating their exact hole masks. The meaningful initial quotient has 51 control signatures;
  exact common-hole histories already produce 119 distinct concrete signatures and are therefore
  unsuitable as the control state.
- The frozen 24-macro vocabulary covers `1158/1293` obligations at `N=12` and `1525/1653` at
  held-out `N=15`; 91 of 120 occurrences fail. Most failures are aligned common-catch owner nodes,
  but 11 occurrences contain genuine noncommon packet/pending failures and 17 contain held-out
  threshold-skew or boundary classes. The five previously isolated generation-zero exceptions are
  not reached in this second-generation set and do not improve these totals.
- A bounded adaptive search used the same literal/bounded-affine action grammar, aggregate ledger,
  at most three large replies, joint legality and safety at both sizes, and no exact masks or
  interior-counter actions. It hit the preregistered hard cap at 101 total macros (`24+77`) by
  occurrence 14, after 372 failed paired attempts. Even then 25 occurrences remain unresolved,
  and greedy successors occupy hundreds of control signatures. This meets the campaign's explicit
  abandonment criterion for table-expanding the controller.
- Aggregate history repairs real bookkeeping: it recovers 47 paired classes and two whole
  occurrences that the one-residual ledger rejects. It does not make the grammar closed. The
  finite affine-controller route is therefore suspended, not generalized with more labels.
- Reproduction artifacts are read-only scratch files:
  `HISTORICAL_TMP/PairedPhaseGenericControlCEGIS_20260809.py`, SHA-256
  `5d500316d2de67e174a9cd6c89160b561137d465933102be0904320bd6fda6de`, and output SHA-256
  `fac9f9caf566a8f0835dc41ed3cb22d352c5c9b5ca48fcff701bf6c40cdeeb2d`;
  summary script SHA-256
  `1162c4abfd3b7ad655a42cdd73027bc6d9a891392f30be91846bc6467dd3fe2f`, output SHA-256
  `cda29c06fa3c8a02b9436d9b1ccb6cc2cf9a46e65b11987a9bd9e6210b0dcafe`.
  These are exact finite computational diagnostics using an independent transition/value
  implementation, not Lean certificates or a parametric refutation.
- Immediate pivot: formalize arbitrary-set winning-opening uniqueness and reachable interval
  support/deficit bounds while an independent audit ranks non-enumerative research routes. The
  aggregate ledger remains a check-in-worthy semantic result and potential certificate backend;
  its existence is no longer treated as evidence that the rejected phase grammar is finite.

### Reproducibility alert — 2026-08-09 02:02 EDT

- An adversarial reread found that one imported Python helper created `itertools.product(...)` once
  outside a nested loop and then reused the exhausted iterator. Consequently, some occurrence and
  coverage totals can depend on `PYTHONHASHSEED`. The concrete aggregate-growth path is independent
  of that iterator and remains exact; the Lean modules are unaffected.
- The controller route remains provisionally suspended, but the numerical `91/120`, `101 macros`,
  and successor-signature claims above are retracted pending a corrected materialized-product run
  under at least two hash seeds. They must not be cited as final evidence until that audit reports
  reproducible totals.

### Reproducibility alert resolved — 2026-08-09 02:11 EDT

- The exhausted iterator was confined to the diagnostic `OccurrenceAudit.rich_support_keys`; the
  decisive Control/Generic CEGIS programs do not use that helper. After materializing the product,
  seeds `0` and `5` give identical corrected occurrence totals and identical CEGIS results.
- The generic bounded CEGIS conclusion is restored: it hits the 101-macro cap, covers
  `1285/1293` base obligations and `1621/1653` held-out obligations, and leaves 25 occurrences
  failed. Its greedy successors occupy 1,885 control signatures / 2,081 signed certificate
  signatures; these counts are upper bounds from the selected witnesses, not minimality claims.
- The concrete coefficient-growth edge also survives correction, but it is not forced. Twelve
  shared safe/legal replies exist at that parent; eleven retain `-2*N-4`, while only the lexical
  first choice grows to `-4*N-10`. One already-frozen alternative (`N-1` in the large game) avoids
  growth. Therefore the rigorous research conclusion is that the bounded table grammar fails its
  gate—not that aggregate history necessarily grows without bound.
- Corrected audit artifacts:
  `HISTORICAL_TMP/ResolvedValueGrowthAudit_20260809.py`, SHA-256
  `54425d3955ce352eda9146f9c92c9b028a5aebdf059799f4726dc2407fd05fcd`, and report SHA-256
  `c4f5d52191c421728d6d7d6c3947c9ce9061815e9bad554a428baddde748e0b2`.

## Live multi-agent capacity audit — 2026-08-09 02:04 EDT

- Read-only inspection confirmed that `SOURCE_CHECKOUT` now contains
  `[agents] enabled = true` and `max_concurrent_threads_per_session = 64`.
- With the root and three subagents active, one additional bounded independent scout was rejected
  with `agent thread limit reached`. The effective limit for this already-running goal is therefore
  four active threads total, not the configured ceiling of 64.
- The campaign will not restart or troubleshoot this discrepancy. It will recycle the three
  available subagent slots through repeated, mechanism-distinct waves; repository writes remain
  single-writer and expensive computation remains singly owned.

## Reachable interval bounds and parity — 2026-08-09 02:12 EDT

- Added `scripts/catch_up/ReachableBounds.lean`. Lean proves that picking any counter at most `N`
  preserves a deficit bound `≤ N`, then inducts over the formal `ReachableFromOpening` relation to
  show `remaining ⊆ Icc 1 N`, `deficit ≤ N`, and `remaining.card ≤ N` at every reachable absolute
  interval position. These results justify the deficit and mask bounds assumed by finite encodings.
- Strengthened `scripts/catch_up/Parity.lean`: every reachable interval position has
  `deficit + remaining.sum` congruent modulo two to the original interval sum. This connects the
  earlier general odd-weight no-draw theorem to the formal reachability relation rather than only
  to isolated transitions and roots.
- Targeted warning-strict builds passed. The four new theorems were independently axiom-audited;
  each reports only `[propext, Classical.choice, Quot.sound]`. Current hashes:
  `ReachableBounds.lean`
  `2ae6d0483283c54774aad2f57af9d08ae20977d21ed6c9fedfb2bcffaa2445dd` (81 lines / 3,043 bytes),
  `Parity.lean`
  `965345af84a49b838fea9a64bb3264f664c5e2ced3209c5843e7d008945d9d52` (201 lines / 8,165 bytes).

## Approach-family registry — 2026-08-09 02:12 EDT

- **Symmetric fixed-width four-lift:** rejected by a parametric protected-player-one stuttering
  obstruction; do not reopen without a mechanism that allows unbounded pending history.
- **Asymmetric selected-turn packet transfer:** entry/history/balancing lemmas are Lean-verified,
  but finite affine table closure failed the corrected 101-macro gate; table expansion is suspended.
- **Semantic/certificate infrastructure:** one-residual and aggregate ledgers, edge reflection,
  finite product checking, and one literal basin certificate are banked. Infrastructure is a
  verifier, not a discovery argument, and will be expanded only for a surviving theorem candidate.
- **Parity and reachable-state structure:** productive bankable family; odd-total no-draw and the
  new interval bounds/parity are Lean-verified. It narrows state space but does not decide the
  even-total game.
- **Winning-opening uniqueness:** now Lean-verified for arbitrary finite sets, including the sparse
  terminal branch and exact root equivalence. Valuable but not by itself a draw proof.
- **Direct symmetry/pairing/strategy stealing:** reopened as an independent scout with no four-lift
  assumptions. Prior complement and naive equal-sum pairings are known to fail turn dynamics; new
  proposals must state and survive an exact small falsification test.
- **Frontier computation / N=39,40:** direct but infeasible for exact full DP in this campaign;
  heuristic search has no current counterexample signal and remains capped.
- **Odd-total opening-two transfer:** mathematically interesting but outside the formal even-total
  conjecture; deferred unless it yields a mechanism that ports back to residues zero/three.

## Arbitrary-set winning-opening uniqueness — 2026-08-09 02:19 EDT

- Added `scripts/catch_up/WinningOpening.lean`. Lean proves that if two legal openings `a` and `b`
  of an arbitrary finite counter set both leave a normalized loss for the next player, then
  `a = b`. No interval, positivity, parity, or root-win hypothesis is used.
- The crossing argument is formalized with its omitted sparse-set branch. For `a < b`, replying to
  opening `a` with `b` forces the common state
  `((S.erase a).erase b, b-a)` to be a win. If the position after opening `b` is nonterminal,
  replying with `a` forces the same state to be a loss. If that reply is unavailable because the
  position is already terminal, finite-sum arithmetic proves the common state itself cannot catch
  up and is again a loss. Thus the arbitrary-set generalization is genuine rather than an
  interval-only proof disguised by an illegal response.
- Lean also proves, for every nonempty finite set, that the root value is `.win` iff some winning
  opening exists, iff a unique winning opening exists. A direct interval corollary packages the
  statement used in the Catch-Up slides.
- `lake --wfail build CatchUpResearch` passed all 8,102 jobs. `WinningOpening.lean` is 166 lines /
  7,111 bytes, SHA-256
  `5839d946f4367216373d78604e5271ada48c901a7c83286e56149dc418d2c334`.
  Every public theorem reports only `[propext, Classical.choice, Quot.sound]`. This is a verified
  structural theorem and solver audit invariant, not by itself a proof that even-total roots draw.

## Second route gate: completed-turn compression — 2026-08-09 02:25 EDT

- The finite atomic-macro route is suspended after its corrected multi-seed gate. The selected new
  primary route changes the proof language rather than the table: represent an entire completed
  turn by a finite consumed set `T` and a distinguished final catching counter `z`.
- Because counters are positive, unordered turn legality should reduce exactly to
  `T.Nonempty`, `T ⊆ remaining`, `z ∈ T`, `deficit ≤ T.sum`, and
  `T = {z} ∨ (T.erase z).sum < deficit`. The singleton disjunct is essential for a one-pick turn
  from deficit zero; for a longer turn the strict preparation-sum inequality guarantees every
  intermediate pick continues and the final pick catches. A read-only Lean agent is proving the
  full list-trace equivalence, including distinctness, nonterminal sources, exact remaining set,
  final deficit, and mover switch.
- The intended strategic lift permits an arbitrary mirrored common part, at most one oriented
  debt/credit substitution, and at most one proved balancing pair. It deliberately has no
  `resolvedValue` control coordinate and no cap on raw reply length. This directly targets the
  aligned common-catch owner obligations that dominate the failed atomic grammar.
- The smallest preregistered falsification gate is one stable hard packet blocker, instantiated at
  `N=12` and held-out `N=15`. Enumerate all safe completed replies, then require a single shared
  literal/affine construction with at most one substitution and one balancing pair. Abandon the
  route after two hours or immediately if either instance lacks such a response, needs unrelated
  interior counters/exact masks, needs multiple repairs, or grows structurally with `N`.
- Separately, the aggregate ledger is now formally quotiented at the numerical level. Lean proves
  that consistency uniquely determines `resolvedValue`; a canonical ledger constructed from the
  two visible sign supports represents the exact score gap; and any two canonical endpoints
  satisfy `ValueStep` automatically. Thus aggregate magnitude is bookkeeping rather than an
  independent strategic phase. Current `AggregateSimulationLedger.lean` SHA-256:
  `bf9c8975d22168765202d17d129ca5d903b43ae9dddc598888b50b4eb0a3a43a` (570 lines /
  28,875 bytes); the new quotient theorems are warning-strict and axiom-audited under only
  `[propext, Classical.choice, Quot.sound]`.

## Completed-turn semantics — 2026-08-09 02:34 EDT

- A read-only Lean tranche in `HISTORICAL_TMP/CompletedTurnFormal_20260809.lean` proves the exact
  equivalence between an ordered legal pick trace that completes one turn and an unordered chosen
  set with a distinguished final catching counter. The endpoint erases exactly the chosen set,
  switches the mover, and has deficit `chosen.sum - before.deficit`.
- The necessary and sufficient unordered conditions are: the final counter belongs to the chosen
  set; the chosen set is contained in the remaining support; the starting deficit is at most the
  chosen sum; and either the chosen set is the singleton final counter or the preparation sum is
  strictly below the starting deficit. The singleton disjunct repairs the tied-root case.
- The 412-line scratch module passes warning-strict Lean and its principal theorems report only
  `[propext, Classical.choice, Quot.sound]`. SHA-256:
  `baaf1cd2b7f7450ee92f09cc4adabb4332a1321e424c09aeb18a4da51f9d5677`.
  It remains a reviewed scratch artifact pending naming/category cleanup and integration.

## Lower pair-deletion reduction — 2026-08-09 02:44 EDT

- An independent exact-game scout found a non-four-lift reduction. Define
  `pairDeletionPosition N a b` by deleting `a` and `b` from `Icc 1 N` and setting deficit
  `b - a`. For the interval conjecture only the lower ray `a = 1` is required.
- Added `scripts/catch_up/PairDeletionReduction.lean`. Lean proves that for `2 ≤ N`, if every
  `pairDeletionPosition N 1 b` with `2 ≤ b ≤ N` is not `.loss`, and the `b = 2` member is `.draw`,
  then `value (Icc 1 N) = .draw`.
- The assembly is exact: opening `1` is safe for player one because every legal reply `b` catches
  into a lower-ray state that is not a loss for player one; after every opening `a > 1`, player two
  safely replies with `1` and continues in the same lower-ray state; after opening `1`, the reply
  `2` supplies player two's required draw branch.
- Exact computation currently supports lower-ray nonloss at every even-total interval tested
  through `N = 16`. The convenient `b = 2` draw base needs `N ≥ 4`: at `N = 3` that state is a
  win, although the interval root still draws and can be handled separately. This is exact finite
  evidence, not a proof of the ray.
- The module is 182 lines / 7,896 bytes, SHA-256
  `2671467de1d9fe3c099e979386a8370a6528d198a332beef4c128a85f308274e`.
  Its public theorems are warning-strict and axiom-audited under only
  `[propext, Classical.choice, Quot.sound]`. A full `CatchUpResearch` build passed 8,103 jobs.
- The stronger empirical candidate says every finite complete counter set of even total draws,
  where in increasing order the least counter is `1` and each next counter is at most one plus the
  sum of its predecessors. Exhaustive and randomized tests are promising but not yet independently
  reproduced. Three agents are now separating this stronger statement from the narrower lower ray,
  checking the exact Finset quantifiers, and seeking either a proof mechanism or a minimized
  counterexample.

## Approach-family registry update — 2026-08-09 02:44 EDT

- **Lower pair-deletion / complete-set combinatorics:** primary route. It is directly relevant,
  collapses the opening quantifiers to one parameter, and is independent of the failed phase-table
  grammar. Promotion beyond finite evidence requires either a symbolic lower-ray proof or a proved
  stronger complete-set theorem.
- **Completed-turn semantics:** bankable proof tool and support route. It is no longer the primary
  packet experiment unless it supplies the missing lower-ray induction step.
- **Finite affine packet tables:** suspended after corrected multi-seed CEGIS reached 101 macros
  while leaving 25 root-generated occurrences unresolved. Reopen only for a genuinely new
  non-enumerative invariant.

## First independent lower-ray and complete-set audit — 2026-08-09 02:48 EDT

- An independently implemented macro-turn recurrence agrees with the original pick recurrence on
  small games and verifies every pair-deletion state at `N = 19` and `N = 20` is a draw (171 and
  190 unordered pairs respectively). In particular the required lower ray has no loss at these two
  fresh even-total sizes.
- A whole turn from positive deficit `d` can be represented by a nonempty chosen block `B`: some
  ordering completes the turn exactly when `d ≤ B.sum` and `B.sum - B.max < d`. The maximum may be
  taken as the final catching counter. At deficit zero, legal completed turns are singletons. This
  is the compact macro-game form of the completed-turn Lean API.
- The stronger claim that all pair deletions of every complete finite set are nonlosing is false.
  Minimal reported counterexample: `S = {1,2,3,4,6}`, delete `1` and `3`, yielding
  `⟨{2,4,6}, 2⟩`, whose value is `.loss`. Each possible first pick switches into a winning child.
  Therefore no proof may infer the interval lower ray from that false all-pairs generalization.
- The root-only complete-set draw conjecture remains unrefuted: the independent scout exhausted
  10,075 complete distinct even-sum sets and 24,115 complete even-sum multisets through cardinality
  seven, plus several hundred randomized longer examples. Multisets are a distinct model: Lean's
  `Finset` collapses duplicate weights, so any theorem used for Catch-Up must keep the distinct-set
  hypothesis explicit. These counts are exact computational evidence, not a proof.

## Lower-ray canonical first turn — 2026-08-09 02:54 EDT

- A separate exact recurrence found a striking first-turn profile for the required positions
  `Q_N(b) = pairDeletionPosition N 1 b`. For `b ≥ 3`, let `k` be least with `b ≤ k(k+1)/2`.
  The current player takes the consecutive block `2,3,…,k`; it completes the turn and lands at
  `C_N(b) = ⟨(Icc (k+1) N).erase b, k(k+1)/2 - b⟩`. For `b = 2`, taking `3` lands at
  `⟨Icc 4 N, 2⟩`.
- This prescribed first turn reaches a draw-valued child for every lower-ray state at
  `N = 12,15,16,19`. At `N = 19`, all 18 ray states and, much more strongly, every one of their
  17 legal first picks have draw outcomes. Small exceptions exist below the prospective induction
  threshold: the literal first-move rule uses `4` at `(N,b)=(4,2),(4,3),(8,3)`.
- The exact remaining theorem is now explicit: prove the canonical tail-with-one-hole states
  `C_N(b)` draw for even triangular total and `N ≥ 12` (plus the `b=2` tail). This is a compact
  symbolic family with deficit strictly below its least possible remaining counter, not an
  exact-mask phase table.
- The independent pair-state counts `(loss,draw,win)` for all `a<b` are:
  `N3=(0,2,1)`, `N4=(0,3,3)`, `N7=(0,12,9)`, `N8=(0,28,0)`,
  `N11=(0,52,3)`, `N12=(0,66,0)`, `N15=(0,105,0)`, `N16=(0,120,0)`, and
  `N19=(0,171,0)`. No pair-deletion loss occurs in any tested even-total interval. Canonical
  profile script SHA-256:
  `bcd0a42fc11856c2cdd3983aaf1214a7bac59d524dcb7e9673d406be0e9a2219`.

## Adversarial scope corrections — 2026-08-09 03:03 EDT

- The complete-set conjecture does not admit the simpler claim that opening `1` always draws.
  For `S={1,2,3,4,6}`, the post-opening values for the next player are, in opening order,
  `1↦loss, 2↦draw, 3↦draw, 4↦loss, 6↦loss`; hence openings `2` and `3` draw while opening `1`
  wins for the first player under the usual negation convention. A concrete minimax drawing policy
  after opening `2` was exhaustively reconstructed, so the root remains a genuine draw.
- Nor is there a universal first-player strategy-stealing theorem for arbitrary positive sets.
  `S={2,3,4,5,8,9}` is a root loss with odd total, and `S={2,5,6,9,11,13}` is a root loss with even
  total. Therefore the minimum-counter `1` and completeness hypotheses are mathematically active;
  no proof may replace them by parity or positivity alone.
- Added a warning-clean scratch bridge from completed turns to game semantics:
  `CompletedTurn.can_avoid_loss_of_endpoint` transports `CanAvoidLoss` backward along an owned
  completed turn, and `CompletedTurn.value_ne_loss_of_endpoint_value_ne_win` turns a nonwinning
  endpoint into a nonlosing start. Both report only the standard
  `[propext, Classical.choice, Quot.sound]` axioms. Scratch SHA-256:
  `e6dc4e250347006ae4a4b54ffb79d0ef04720e6ba027c480d58093e2ed9ec8e1`.

## Complete-set and one-scalar-tail routes refuted — 2026-08-09 03:14 EDT

- The complete-even-Finset conjecture is false. A verified counterexample found by whole-turn
  recurrence is `S={1,2,4,8,11,12,18,48,56}`, total `160`. It satisfies the complete-sequence
  inequalities at every prefix, but its opening outcomes for player one are
  `(-1,+1,-1,-1,-1,-1,-1,-1,-1)`: opening `2` uniquely wins. A second counterexample is
  `{1,2,4,7,14,17,22,29,91,107}`, total `294`, with unique winning opening `4`.
- The first counterexample has cardinality nine. Exhaustive search found none through cardinality
  seven, while cardinality eight was sampled but not exhausted; therefore it is the smallest found,
  not a proved minimal counterexample. This decisively ends the proposed complete-set proof route.
- The exact canonical tail family remains empirically drawn above the threshold, but no safe
  strategy stays within a one-hole/small-deficit class. At `C_12(3)=⟨{4,…,12},0⟩`, adversary move
  `4` has only six safe replies, all singletons. Every class-preserving reply among `6,7,8` is then
  met by adversary move `5`, after which every safe response has a large deficit and/or multiple
  holes. This exhausts all safe completed replies, so additive triples, fixed prefix responses,
  and a one-scalar tail potential meet the preregistered stop condition.
- Lean scratch `HISTORICAL_TMP/LowerRayLemmas.lean` proves the tied-root identity and an exact-catch
  reduction from a normalized nonloss goal to nonwinning of the tied residual root; SHA-256
  `1c579615f6a2621ee16b9ef7130ab136234b307726fc911992893858d092f8dc`.
  The reproducible closure audit is `HISTORICAL_TMP/tail_closure_audit.py`, SHA-256
  `cd3933f897e4234e7f0071919b84efee10fb141144e7859c01803fb534c2a6d8`.

## Draw-opening theorem and canonical-tail transfer pilot — 2026-08-09 03:20 EDT

- Added `scripts/catch_up/DrawOpening.lean`. For every nonempty finite counter set `S`, Lean proves
  `value S = .draw ↔ ∃ p ∈ S, (afterOpening S p).value = .draw`. The nontrivial reverse direction
  proves that a draw-valued opening cannot coexist with a winning opening by comparing the two
  orders of any distinct pair, with an explicit terminal/insufficient-sum branch.
- The module also proves exact second-pick order symmetry and that every hypothetical pick from an
  insufficient-sum position is losing. Warning-strict build and axiom audit pass under only
  `[propext, Classical.choice, Quot.sound]`. Current SHA-256:
  `66edc999bea93ec594302c6629e12d9cfc64ec8cdf6b7d1d904f6bb5f6d295c0` (130 lines /
  5,739 bytes). A fresh independent adversarial audit is in progress.
- Added an additive diagnostic runner for canonical tails to the inherited
  `SimulationBasinMain.lean`. It constructs the exact state reached after opening `1`, reply `b`,
  and the canonical completed prefix `2,…,k`; compares it with the same state plus four new top
  counters; and runs both protected owners from the empty ledger.
- Two pilots pass at width three: `C_8(4) → C_12(4)` uses 962/3,121 labels for protected
  player two/one, and the genuine boundary `C_12(12) → C_16(12)` uses 23,949/51,804. The hard low
  boundary `C_12(3) → C_16(3)` also passes, using 449,810/722,510 labels. These are exact
  computational basin-search results, not Lean basin certificates or a parametric closure proof.

## Complete old-tail matrix and independent draw-opening audit — 2026-08-09 03:28 EDT

- The full width-three canonical old-tail matrix `C_12(b) → C_16(b)` passed for every
  `b = 3,…,12` and for both protected players. The respective player-two/player-one cache-label
  counts were: `b3 449810/722510`, `b4 173358/433164`, `b5 176659/307561`,
  `b6 269864/301413`, `b7 112814/135675`, `b8 47499/102569`, `b9 48219/106251`,
  `b10 50246/91140`, `b11 18455/57928`, and `b12 23949/51804`. Exact stdout is preserved at
  `HISTORICAL_TMP/LowerRayTailMatrix_N12_20260809.txt`, SHA-256
  `a369b02ae30368d477a8306165f216acc159003bd30ed28e679e9ec14dce4775` (33 lines / 2,804
  bytes). This is exact finite search evidence; no literal product certificate or parametric
  relation has yet been extracted from the matrix.
- An independent read-only audit found no correctness defect in `DrawOpening.lean`, including the
  sparse-set terminal branches, outcome-perspective negations, and singleton case. It also checked
  the canonical-tail state encoding, root empty ledger, owner/opponent quantifiers, and runner
  guards. The suggested fail-on-required-false behavior was added, and the targeted warning-strict
  build passes.
- A single capped held-out diagnostic, `C_15(3) → C_19(3)` for both players, ran for ten minutes
  without emitting a result and was cleanly interrupted with exit code 130. This is an incomplete
  computation, not evidence for failure. No output artifact or mathematical claim is attributed to
  it.

## Four boundary-tail pairing — 2026-08-09 03:35 EDT

- For a new lower-ray hole `b=N+r`, `1≤r≤4`, the natural old source is the tail with hole `b-4`.
  If the triangular ceiling is unchanged, the histories differ by the consumed top `b` with
  coefficient `-1` and the old counter `b-4` with coefficient `+1`, giving score gap `-4`. If the
  ceiling crosses from `k-1` to `k`, the large history additionally consumes old counter `k` with
  coefficient `+1`, giving score gap `k-4`. This yields a canonical initial residual ledger:
  negative consumed-top support `{b}`, all pending old discrepancies positive, and no residual.
- Added a warning-strict compiling boundary-matrix diagnostic using exactly that state/ledger
  pairing. A small `8 → 12` smoke test rejected the first protected-player-two obligation
  `C_8(5) → C_12(9)` at width three. This is an exact finite failure of this particular ledger
  relation below the proposed `N≥12` induction threshold; it neither refutes the lower-ray theorem
  nor predicts the decisive `12 → 16` boundary result.
- The decisive `12 → 16` boundary matrix then passed all four offsets and both protected players.
  Small/large `(k,b)` pairs were `(4,9)→(5,13)`, `(4,10)→(5,14)`,
  `(5,11)→(5,15)`, and `(5,12)→(6,16)`. Player-two/player-one cache sizes were respectively
  `13190/61719`, `43491/71964`, `17792/55491`, and `3252/60821`; every small premise was safe,
  every product root true, and every initial ledger valid. Exact stdout is preserved at
  `HISTORICAL_TMP/LowerRayBoundaryMatrix_N12_20260809.txt`, SHA-256
  `df886901a9e333b14920d6c64c8b1aa191a6baf5c0ed77c752369cc42e621370` (12 lines / 1,309
  bytes).
- Together with the complete old-tail matrix, this supplies exact finite product-search witnesses
  for every canonical tail `b=3,…,16` needed to transfer the lower-ray family from size 12 to size
  16. It does not cover the separate `b=2` drawing tail, does not produce literal checked product
  certificates, and does not prove an `N`-uniform closure relation.

## Tail-transfer API and phase-compression stop — 2026-08-09 03:50 EDT

- A warning-strict scratch Lean development now formalizes the exact canonical completed turn
  `2,…,k`, proves that nonwinning of its tail implies nonloss of the original pair-deletion state,
  and packages the exact induction invariant: the `b=2` pair draws and every `b≥3` has a
  triangular-ceiling tail nonwinning for player two. It proves a conditional `N→N+4` draw theorem
  from: both-owner transfer at `b=2`, player-one transfer at every old tail, and player-one safety
  at the four new tails; a shifted `b-4→b` boundary family discharges the new-tail premise. Scratch
  artifact `HISTORICAL_TMP/TailTransferAPI_20260809.lean`, SHA-256
  `4ee7011cc1a6e6a511785955aebaf9fb4ae6c2000f118669822d922307c015cc` (351 lines / 14,945
  bytes). This is a conditional theorem and does not prove any transfer family.
- The boundary ledger signs were independently checked against the actual opening/reply/prefix
  histories. Consumed top `N+r` has coefficient `-1`; every old symmetric-difference counter has
  coefficient `+1`, including the extra ceiling counter in a triangular-crossing case. For `N≥8`
  the two pending counters cannot coincide. This exactly reproduces the executable score gap.
- A bounded exhaustive phase audit blocks finite controller-table synthesis. Exact integer deficit
  offset removes the tested coarse action conflicts at `N=7,8`, but the offset is unbounded; natural
  sign/relative-to-`N` buckets conflict. Even at identical exact offset, pending counter identities
  change whether the same action creates a residual. Report
  `HISTORICAL_TMP/LowerTailProductStructureReport_20260809.md`, SHA-256
  `8e3c41b2c84d8c233a9cdcb302731037457a5b1d933a7eae9339902fc0b29477`; reproducer
  `HISTORICAL_TMP/LowerTailWitnessProbe.lean`, SHA-256
  `13629cf76d1dbf47930497de044829fb9c9584c456dde70a67614163ad90572e`.
- The root-directed held-out `C_15(3)→C_19(3)` computation also failed to finish its product
  recurrence in ten minutes and was interrupted. This second incomplete run is not negative
  mathematical evidence, but no further time should be spent on that instance without a new
  algorithmic or symbolic mechanism.
- Added and ran the separate `b=2` pair-tail diagnostic at `12→16`. Both protected players pass:
  player two used 3,213,433 cache labels (296,106 winning) and player one used 1,025,470
  (115,870 winning). Exact stdout is `HISTORICAL_TMP/LowerRayPairTwo_N12_20260809.txt`, SHA-256
  `2242c98eea8f2467827d412b5aba44163dda08d523ba3e335b429069721d5c05` (3 lines / 244
  bytes). Together with the old and boundary matrices, every premise of the newly formalized
  lower-ray invariant transfer has exact finite solver evidence at `12→16`. None of these cache
  witnesses is yet a literal checked product certificate or a uniform theorem.
- Integrated the conditional mathematics as `scripts/catch_up/LowerRayTransfer.lean`, with
  repository-style theorem names, documentation, and API/AMS attributes. The warning-strict target
  build passes. Current SHA-256
  `f9425d6b1e71a1f837e46c6238cb4e05174b08d9318f20d03e5954481e81aff7` (389 lines / 16,681
  bytes). Axiom audits for the invariant-to-ray theorem, the boundary-transfer induction step, and
  the final conditional draw theorem report only `[propext, Classical.choice, Quot.sound]`.

## Direct lower-ray structural probes — 2026-08-09 04:12 EDT

- Every strict canonical tail in one triangular block is exactly a same-player child of the
  hole-free parent `P_N(k)=⟨Icc (k+1) N,T_k⟩`; the boundary `b=T_k` uses the opposite perspective.
  Same-`k` adjacent tails also have exact cross-picks reaching an identical child. These identities
  are warning-strict Lean-proved in `HISTORICAL_TMP/LowerRayAdjacentB_20260809.lean`, SHA-256
  `27e0c7b9b9b512a4e24d8d7e85babf3a92fbcd78ec71e643866e7febaa1af0b4`; report SHA-256
  `7c5230e7df900cacd2b5416185a7c215ac22d25da340fe8a3d0418dd0fd2bf83`.
- Bare adjacent-`b` induction is false: kernel-reduced examples have
  `R_7(3)=draw`, `R_7(4)=win`, `R_7(5)=draw`, and the canonical tails cross from
  `C_11(10)=draw` to `C_11(11)=win`. The common-parent premise is also false at the intended
  threshold: `P_12(5)` and `P_16(5)` win, although only low moves `6,7,8` win and the required
  upper-band moves draw. Thus the parent formulation is exact packaging, not yet a logical
  reduction; reopen it only with a new selective winning-move-band invariant.

## Constant-deficit consecutive-hole reduction — 2026-08-09 04:19 EDT

- Define the lower pair-deletion state
  `Q_N(b)=⟨(Icc 1 N \ {1,b},b-1⟩`. For every interior `b<N`, the available move `b+1`
  catches immediately with overshoot two and reaches, after the perspective switch,
  `D_N(b)=⟨Icc 2 N \ {b,b+1},2⟩`. This is a substantially simpler exact reduction than
  the triangular-prefix tail: the deficit is fixed, the holes are consecutive, and every
  remaining counter is at least the deficit.
- Exact recurrence reports `D_N(b)=draw` for every tested even-total
  `N=11,12,15,16,19` and every tested interior `3≤b<N`. The same move fails at the small
  cases `(N,b)=(7,3)` and `(8,4)`, so any theorem needs a real threshold. This is exact finite
  computational evidence, not a proof.
- The reduction proves nonloss of each interior `Q_N(b)` once `D_N(b)=draw` is established. It
  does not by itself prove that `Q_N(2)` draws: a draw-valued move prevents loss but does not
  exclude that the source position is a win. The assembly theorem must retain one explicit
  draw-pair obligation or prove a separate no-win statement.
- A warning-strict scratch strategy-stealing lemma now proves a more general exact-pair
  nonloss criterion: if two available counters sum to the current deficit and every counter
  remaining after deleting them is smaller than the second counter, the position cannot be a
  loss. This is being specialized to the upper endpoint while fresh agents independently attack
  the `D_N(b)` family.
- The configured multi-agent ceiling remains `64`, as re-read from `HISTORICAL_TOOL_PATH`; the
  already-running goal experimentally exposes four active threads total. The campaign was not
  restarted. All three available subagent slots remain in use and will be recycled dynamically.
- The final root-directed `C_15(3)→C_19(3)` product search produced no owner result before its
  preregistered ten-minute cap and was interrupted cleanly. It is an incomplete experiment and
  will not be rerun without a new algorithmic or symbolic mechanism.

## Successor API and first transfer pilots — 2026-08-09 04:31 EDT

- Warning-strict Lean now proves the exact successor move, its perspective negation, the weakest
  honest interval assembly theorem, and the exact minimax decomposition of `D_N(b)`. The weakest
  theorem assumes only: `Q_N(2)=draw`; `D_N(b)≠win` for `3≤b<N`; and a separate nonloss proof
  for `Q_N(N)`. The exact `D=draw` characterization is one existential nonwinning child plus
  universal nonloss of every three-hole child. Scratch source
  `HISTORICAL_TMP/LowerRaySuccessorReduction_20260809.lean`, SHA-256
  `1de2b0cad240a6afed0255e1f1e3749c9ea18e3e2dddc71116cf0b1c8dcdc1ce` (318 lines /
  13,697 bytes). A fresh adversarial review is in progress before repository integration.
- Exact recurrence confirms every `D_N(b)` is drawn at the tested even-total sizes
  `N=11,12,15,16,19`. The all-size version is false: `D_4(2)`, `D_7(3)`, `D_7(6)`, and
  `D_8(4)` win. Even above the threshold not every move draws: moves `5` and `11` lose at
  `D_12(3)`. Thus the universal child-nonloss clause is real, not a tautological reformulation.
- Added a root-directed consecutive-hole transfer diagnostic. Both low-root pilots pass at width
  three for both players: `D_11(3)→D_15(3)` uses 164,268/216,883 product labels for protected
  player two/one, and `D_12(3)→D_16(3)` uses 366,343/880,863. Exact stdout hashes are
  `50ff62f8854e83989b804a3f6866e66958b6849c9e31c169a67ca813b96987c8` and
  `314c0ae10cf39eeb7f8eb7d34f18174fb44e5c150be59eff1fb87672ac35346d`.
- An independent falsification found the smallest tested warning against dropping adjacency:
  `⟨{2,3,4,5,6,8,9,11},2⟩` (holes `{7,10}` in `Icc 2 11`) is a win even though its
  exact-2 tied residual draws. Hence even parity, density, and the exact counter `2` do not imply
  the successor theorem; a proof must exploit the consecutive-hole geometry or something
  stronger.

## Full old-root successor matrix and endpoint descent — 2026-08-09 04:45 EDT

- Integrated the reviewed successor reduction as
  `scripts/catch_up/LowerRaySuccessor.lean`. It has the required license/module documentation,
  omits scratch diagnostics, and incorporates the reviewer's quantifier improvement: the
  lower-ray nonloss assembly needs only `Q_N(2)≠loss`, while the final interval theorem retains
  the separate `Q_N(2)=draw` premise. Warning-strict target build passes; the three principal
  axiom audits report only `[propext, Classical.choice, Quot.sound]`. Current SHA-256
  `5d1dbe9a16d3644d61c9a8b0c3483de8162872a305f733a64d598dc9e8dfb1ef` (325 lines /
  13,757 bytes).
- The complete unchanged-root width-three matrix `D_11(b)→D_15(b)` passed for every
  `b=2,…,10` and both protected players. Exact stdout is
  `HISTORICAL_TMP/ConsecutiveHoleTwoMatrix_N11_20260809.txt`, SHA-256
  `307297a171936afb278f8f19e59715225c42b07e2ee622818e51eca4c6913fcf` (27 lines /
  2,205 bytes). The separately sampled upper root `D_12(11)→D_16(11)` also passed, using
  321,185/590,668 labels; stdout SHA-256
  `b876ae0d8d86d27200e09eb8ec11c780a24a87bc6119a6c0f73432d9049a57af`.
- A warning-strict strategy-stealing proof now gives `Q_N(N)≠loss` for `N≥3` and, more
  strongly, `Q_N(N-1)≠loss` for `N≥7`, with no parity assumption. The general core says a
  losing position with an available exact-deficit counter forces the tied residual to have a
  unique winning opening strictly above that deficit. At `b=N` no such counter exists; at
  `b=N-1` the only candidate is `N`, whose alleged loss is contradicted by the exact pair
  `{3,N-3}`. The scout is testing whether this yields a genuine downward-`b` induction.
- The natural four new-root boundary ledger was derived independently from the exact histories.
  For large hole `B=N+r`, `0≤r≤3`, pair it with small hole `s=B-4`; the semantic ledger is
  `topPositive={B+1}`, `pendingPositive={s}`, residual none. At `r=0`, the pending support has
  three old counters `{N-4,N-3,N}` and the consumed-top support is only `{N+1}`; the signed value
  still cancels to zero. The executable masks are exactly `topPositiveMask=1<<r` and
  `pendingPositiveMask=1<<(N+r-5)`.
- This canonical boundary relation fails decisively at `11→15`. For `r=0`, protected player two
  passes (208,613 labels) but protected player one fails. For `r=1`, protected player two already
  fails. Initial ledger validity was checked before both recurrences. Preserved exact-result notes:
  `HISTORICAL_TMP/ConsecutiveHoleTwoBoundary_N11_r0_RESULT_20260809.md`, SHA-256
  `7615ccb6847b072ccb3049940eca626e9b7dc8a01e458c1a6b29cc652bf5c0e8`, and the analogous
  `r1` note, SHA-256
  `837eb5a8e73cd57622a6482cb8fe1b1bbc9d1c9e03cfd9887f8976a31047a6b3`.
  This blocks the simplest width-three/one-residual `D`-family `+4` induction. It does not refute
  `D_N(b)=draw`; the direct strategy-stealing/descent route remains active.

## Exact-deficit tied-residual reduction — 2026-08-09 05:07 EDT

- For every lower pair-deletion state `Q_N(b)` with `b≥3`, Lean now proves that the available
  counter `b-1` catches exactly and reaches the tied root
  `R_N(b)=Icc 2 N \ {b-1,b}`. Hence `R_N(b)≠win` implies `Q_N(b)≠loss`. Together with the
  separate draw at `Q_N(2)`, this is a complete conditional reduction of the interval conjecture.
- A second theorem uses the tied-root draw-opening characterization to reduce further to explicit
  canonical children: opening `4` at `R_N(3)` gives `⟨Icc 5 N,4⟩`, while opening `2` at every
  `R_N(b)`, `b≥4`, gives `⟨Icc 3 N \ {b-1,b},2⟩`. Draws for these positions plus the `Q_N(2)`
  draw imply the interval draw. This is a sufficient reduction, not an equivalence and not a proof
  of the remaining canonical family.
- Integrated warning-strict module `scripts/catch_up/LowerRayExactDeficit.lean`, SHA-256
  `da62f72a80b19438b0f27e7c6d3d3b605e320fed44c7124598450d3363c28d36` (217 lines / 8,858
  bytes). An independent adversarial audit passed every perspective, membership, and quantifier
  case; all eleven public theorems report only `[propext, Classical.choice, Quot.sound]`.
- Lean also now proves the general strategy-stealing constraint: if a losing normalized position
  still contains its exact deficit, deleting that counter leaves a winning tied root whose
  globally unique winning opening is strictly larger than the old deficit. Consequences include:
  an available maximum deficit cannot lose; `Q_N(N)` never loses for `N≥3`; and lower-ray nonloss
  reduces to excluding winning openings above the exact deficit. Integrated warning-strict module
  `scripts/catch_up/DeficitWinningBound.lean`, SHA-256
  `3d3e984a29e1ca7502ca703a9a090a203bef3b933642654db3bc0f3a6217dc6e` (249 lines / 12,082
  bytes). Its core proof was independently audited before integration; the explicit global
  uniqueness packaging removes an ambiguity in the scratch `∃!` statement.
- A new reduced-width boundary pairing was tested once: `D_11(10)→D_15(11)` with an initially
  valid one-pending-plus-one-residual ledger. The required protected-player-two root failed at
  width three. Exact note `HISTORICAL_TMP/ConsecutiveHoleTwoPenultimateBoundary_N11_r0_RESULT_20260809.md`,
  SHA-256 `1d43f441eab5fc9b4a411674c1c50a8ec534a0f7a5de2ee087732f76cb5dc4d1`.
  No later offset, wider cutoff, or alternate residual encoding was tried. This blocks that repair,
  not the tied-residual theorem.
- Endpoint descent proves `Q_N(N)` and `Q_N(N-1)` nonlosing, but the next case already reduces to
  the smaller interval's opening-one position and therefore recovers the original `N→N+4`
  strategic obligation. This route is stopped absent a genuinely new mechanism. Independent scouts
  are instead attacking the canonical tied-residual children directly.
- The penultimate endpoint is now preserved in warning-strict
  `scripts/catch_up/LowerRayEndpoints.lean`, SHA-256
  `8e62d2c183098c896e988eb47884f10db71a0a49da35367ed06a75842c5239c2` (153 lines / 5,832
  bytes). Its reusable core proves that two available counters exactly filling the deficit prevent
  loss when the second dominates every residual counter. All three public theorems have only
  `[propext, Classical.choice, Quot.sound]`; a fresh independent source audit remains pending.
- Lean also proves the exact local obstruction around a hypothetical interior winning opening:
  if `y-1` and `y+1` are available and opening `y` wins, then the two deficit-one children obtained
  by deleting `y-1` versus `y+1` have values `loss` and `win`. The tempting abstract claim that a
  two-unit replacement cannot cause this jump is false: exact recurrence found
  `⟨{4,7,9,10,12,15},1⟩=loss` but `⟨{4,7,9,10,12,13},1⟩=win`, with even invariant. Therefore only
  a dense, adjacent-hole-specific no-jump theorem could help; abstract counter monotonicity is
  stopped.
- The abstract no-jump counterexample is now preserved as a warning-strict Lean/native-checked
  artifact at `HISTORICAL_TMP/DeficitOneNoJumpCounterexample_successor_boundary_audit.lean`,
  SHA-256 `178d8796e2293a38561c57770c6d4025faa8df5a55f1626924fd2f8644526024`.
  Its exact axiom audit includes `Lean.ofReduceBool` and `Lean.trustCompiler` because it uses
  `native_decide`, in addition to the standard axioms. The independent recurrence reproducer is
  `HISTORICAL_TMP/tied_no_jump_independent_successor_boundary_audit.py`, SHA-256
  `6cec18e4b0ceeca4ecc0271820e7ad2bb3fa1e0a6ff4c54f8e5610aaf9d89e96`.
- Integrated `scripts/catch_up/LowerRayInteriorReduction.lean`. Lean proves that an available
  opening of the tied consecutive-hole residual whose predecessor or successor is missing must be
  one of exactly `2`, `b-2`, `b+1`, or `N`. Combining this with the forced-neighbor jump reduces
  nonwinning of the tied residual to (a) nonloss of its dense interior deficit-one children and
  (b) nonwinning of those four boundary openings. This is an exact conditional reduction, not a
  proof of either remaining premise. An independent audit passed the warning-strict target and full
  research builds, exhaustive four-candidate classification, perspectives, and final quantifiers.
  All three public theorem axiom audits report only `[propext, Classical.choice, Quot.sound]`.
  Current SHA-256 `43cac04e3d249fd405dc265ab4ac95fb6348943f1dd5973fcd7593512ef968e1`
  (106 lines / 4,723 bytes).
- A separate boundary-opening audit proved exact loss/safe-witness recurrence lemmas but found no
  uniform response. At `N=11,12`, all four boundary openings are nonlosing, yet simple candidate
  replies fail nonuniformly. In particular `b=3,y=4` is exactly the unresolved canonical `A_N`
  family, so the boundary package presently contains rather than solves a core strategic
  obligation. Warning-strict scratch `HISTORICAL_TMP/TiedBoundaryRecurrence.lean`, SHA-256
  `36a139756e936562f0d2af03d4c6336d55783e26e276498ebe8c07aa3ef81293` (129 lines).
- The bounded two-pick policy gate is now closed. At every tested `N=15,16,19,20`, every canonical
  `B_N(b)` challenge `x` for which `x+1` remains has the exact drawing singleton reply `x+1`,
  landing at deficit three. But each iteration deletes a new adjacent pair, so the state class
  grows an unbounded exact hole list. The boundary reply sets are genuinely nonuniform:
  `B_11(4),x=5` has only reply `11`, while the analogous `N=12` state allows only `{6,7,9}` and
  the `N=15` state allows every `6..15`; no single affine response fits all three. Applying the
  exact-deficit winning-opening theorem merely produces a four-hole tied-root obligation whose
  winning opening still depends on the exact mask. Preserved report
  `HISTORICAL_TMP/BPairingK2ExactResults_20260809.md`, SHA-256
  `34070d98d45a753754f152e42fc0d73a81eb6abe79417f02402dfeb5634cb909` (145 lines); reproducer
  hashes are `66f236efc7866487173ea0aa4381121b33fcb9d51c9c3fb5bff5c73357522ea9` and
  `acc7cc5e19f7c453fb42e618dd252d4496d5ca220e99d16e770fd6b53408a4da`.
- A separate scalar interval-tail proposal `J_n=value(Icc 2 n)` is also stopped. Its draw-opening
  recurrence immediately leaves the `J` family and creates arbitrary punctures. More decisively,
  the generic top-four-neutral claim is false: `S={2,9,11}` draws, but
  `S∪{14,15,16,17}` is a first-player win with unique winning opening `2`. A balanced-triple bridge
  to the main interval also has an explicit failure. Warning-strict native certificate
  `HISTORICAL_TMP/IntervalTailJNeutralBlockCounterexample_20260809.lean`, SHA-256
  `4a999261c2bf1d352dd280bcaf611e18808c60c37a86466f1f7eb74a85f26123`; its axiom audit includes
  `Lean.ofReduceBool` and `Lean.trustCompiler`. Probe hashes are
  `da14dfae5f185c478aaa5316b1b774f6122d86d3334047ffb326897975152abe`,
  `701a3f4d58950c0d3b8d5e2b7d600592e87f2fad0e6ea497aa0c8d84e1ffadd4`, and
  `d03275a189669dfd83adc8f565dc18d1b34e9c507738903cb2449ca05c1adc55`.
- A genuinely distinct reply-digraph reformulation survived its first gate. For `a<b`, label the
  pair by `P_N(a,b)=⟨Icc 1 N\{a,b},b-a⟩`; orient `a→b` when this state is loss, `b→a` when it is
  win, and leave draws neutral. Opening `a` loses exactly when it has an outgoing edge, wins when
  it is a universal sink, and draws when it is a non-universal sink. Therefore an acyclic graph
  with a neutral incident pair at every vertex proves the interval draw; a losing root forces a
  shortest directed cycle with only neutral nonconsecutive chords. Independent exact recurrences
  agree through `N=19`; at every even-total `N≤20` the graph is acyclic and neutral-covered, and in
  fact every pair-state loss count is zero, so every decisive edge decreases numerically. This
  stronger pair-nonloss claim remains unproved and may retain the original complexity. Detailed
  report `HISTORICAL_TMP/ReplyGraphAuditResults_20260809.md`, SHA-256
  `b886b5ac6668109bdd3ecb01bf656f521c64dc545fc6d1bbaff838662fa5f89a`; C++ and independent
  Python hashes `999da2b173860b48dc481bc4f958ccb39e38383c1a7d4123f5a00f4b4b76f0ba` and
  `e2568edf249f2019b6097af8c61e20cc6645640c2cad5b90cd5c5e69611bce91`.
- Integrated warning-strict `scripts/catch_up/ReplyDigraphReduction.lean`, SHA-256
  `1373186c38130dd500e36b6c69287329836064182c43079cb232f116db4f53a2` (458 lines / 19,770
  bytes). It Lean-proves exact edge reversal and neutral symmetry, catchable-opening win/loss/draw
  graph characterizations, the equivalence `EveryOpeningDraw S ↔ EveryPairNeutral S`, the
  minimum-rank sink theorem, automatic interval catchability for `N≥3`, and bridges from
  number-decreasing edges or all above-diagonal pair nonloss plus a single neutral partner for
  opening `1` to the interval draw. It also contains the exact cross-pick identity below a common
  maximum that survived the cycle-exclusion audit. The rank/pair-nonloss hypothesis remains open; this is a new
  conditional structural interface, not a proof of the conjecture. Its target and 8,111-job
  research build passed before the cross-pick addition; the post-regression target build passes, and all nineteen
  public theorem axiom audits report only `[propext, Classical.choice, Quot.sound]`. A fresh
  post-integration source audit passed every theorem, warning/lint check, and the weakened
  one-neutral-at-opening-one corollaries.
- The direct reply-cycle exclusion route is stopped absent a new dense-interval invariant. Lean
  proves the exact cross-pick identity
  `P_S(a,c).moveOutcome b = P_S(b,c).moveOutcome a` for `a<b<c`, but at a shortest-cycle
  maximum it identifies only one losing move in a winning pair state; minimax can escape through
  an unrelated counter. A proof-backed native certificate gives an even-total drawn obstruction
  `S={5,6,8,12,17,18,22}` whose reply graph has the induced shortest cycle
  `8→18→17→22→8`, both chords neutral, and external winning escapes `5,6` from `P(8,22)`.
  Hence parity, opening uniqueness, cross-pick algebra, and neutral-chord minimality do not imply
  acyclicity; acyclicity is strictly stronger than the desired draw conclusion. Warning-strict
  artifact `HISTORICAL_TMP/ReplyCycleObstruction_interval_cycle_exclusion.lean`, SHA-256
  `8a0c0374eea40082f5d0c622e867a448b7eed8f55f0e11a7e21c9b3152d931cc`; its finite value
  theorems use `native_decide`, while the symbolic cross-pick theorem has only standard axioms.
  Detailed report `HISTORICAL_TMP/IntervalCycleExclusionReport_20260809.md`, SHA-256
  `35e218985c38c5154830c4c56348af879f89f61dee37148eae3d98878f8ee9ac`.
- Raw complement neutrality remains credible finite evidence but its obvious proof mechanisms are
  stopped. It passes held-out exact tables through `N=28`, yet reflection is not a value
  automorphism: `P_11(1,10)` is win while its reflected `P_11(2,11)` is draw. The child-deficit
  update depends on the integer count gap `q`; its exact reflected signed deficit is
  `(N+1)q-d`, and `q` evolves by `q↦q-1` on a continuation and `q↦1-q` on a catch. This scalar is
  sufficient for score reconstruction but unbounded, and it still does not preserve turn legality.
  At the self-complementary `P_N(1,N)`, the low prefix `2,3,…,k+1` can continue arbitrarily long
  while the first mirrored move `N-1` already catches, forcing unbounded pending moves. Even legal
  mirror completion can be losing (`P_8(1,8)`, take `3`, reply `6`). The only exact conjugacy
  toggles ordinary counter weights with a different co-score rule, not ordinary Catch-Up. Direct
  recursion grows arbitrary holes. Report
  `HISTORICAL_TMP/ComplementNeutralityScoutReport_20260809.md`, SHA-256
  `7beb1cd3e2ec99a3dd677d5215f361b40974418d356eab79022dc2a4276bda59`; the augmented-conjugacy
  and bounded complement-controller routes are blocked, though complement neutrality itself is
  not refuted.
- A fresh independent exact recurrence exposed a stronger dense-state pattern. For every
  `N=6,…,19`, every catchable state whose support is `Icc 1 N` with at most two counters deleted
  and whose effective total `deficit + remaining.sum` is even is nonlosing; the small statement is
  false at `N=4` (`remaining={3,4}`, deficit `3`) and `N=5`
  (`remaining={2,3,5}`, deficit `2`). From `N=11` through `19`, a deterministic first move is safe
  in every tested state: take the exact deficit if present, otherwise the least available counter
  above it, or the maximum if every counter lies below it. For actual pair holes `a<b`, the generic
  exact catch deletes the additive triple `{a,b-a,b}`; every resulting tied residual and its
  minimum opening draw at all tested even-total targets `N=11,12,15,16,19`. The doubling case
  `b=2a` has a separate explicit one-step child, also drawn in the tested range. This is exact
  finite Python evidence, not a checker-backed theorem; the closure obligation is under active
  adversarial audit. Reproducers `HISTORICAL_TMP/dense_two_hole_even_probe_20260809.py`, SHA-256
  `fa798dfa6806c2d8568341a691abef4b45a52727ff4fad44771ebc8f3eb6ada9`, and
  `HISTORICAL_TMP/dense_two_hole_policy_probe_20260809.py`, SHA-256
  `43e0a23fb365747050b9d7e9b87d10d41651e825512b9a6f9bad39274a969f9d`.
- Integrated warning-strict `scripts/catch_up/AdditiveTripleReduction.lean`, SHA-256
  `ff9e9f060732e5401db9397471278f38f1e02d7aa3ede57f350c904aa80cdb87` (208 lines / 9,306
  bytes). It proves the exact `b-a` catch into the tied additive-triple residual, the separate
  `a+1` catch for doubling pairs `b=2a`, legal availability, both one-edge nonloss bridges, full
  above-diagonal pair nonloss from residual nonwin hypotheses, and the final interval draw from
  those hypotheses plus the already isolated `(1,2)` draw. This is a rigorous conditional
  reduction, not evidence that the residual hypotheses hold. Its target build passes all 8,056
  jobs; all eleven public theorem axiom audits report only
  `[propext, Classical.choice, Quot.sound]`. Audit source
  `HISTORICAL_TMP/AdditiveTripleReductionAxiomAudit_20260809.lean`, SHA-256
  `7a5d5b01176e1f2e352b095b9878cbb4f4e5c50d240ee66db58f8f982903e11b`.
- A fresh independent source audit of `LowerRayEndpoints.lean` passed: exact-pair perspective,
  penultimate endpoint quantifiers, lints, and all three public theorem axioms are clean. After the
  interior reduction was added, a fresh independent warning-strict `CatchUpResearch` build passed
  all 8,110 jobs.

## Dense three-hole reduction and hierarchy gate — 2026-08-09 07:21 EDT

- Independent implementations now agree on a substantially stronger finite pattern. For every
  `N=9,…,21`, every catchable position `⟨R,d⟩` with `R ⊆ Icc 1 N`, at most three missing counters,
  `d≤N`, and even `d + R.sum` is nonlosing. The independent C++ audit covered 624,308 roots; the
  smallest preceding failure is the sharp `N=8` state
  `R={1,5,6,7,8}, d=5`. Parity and the anchoring at counter `1` are both essential: odd-parity and
  shifted-interval counterexamples occur already at small sizes.
- At most two holes satisfy the same statement throughout `N=6,…,21` (116,296 independently
  checked roots). The deterministic rule “exact deficit, otherwise least available catching
  counter, otherwise maximum” is safe for every such state at `N=11,…,21`; for three holes its
  safe threshold moves to `N=14`. This rule is therefore evidence for a strategy vocabulary, not
  itself a closed induction, because an arbitrary reply creates another hole.
- A broader `N≥3k` pattern survived the first exact gates: every qualifying state with at most `k`
  holes was nonlosing at `(N,k)=(9,3),(12,4),(15,5),(16,5),(18,6),(21,7)`. The last two gates
  cover 1,885,418 and 16,085,520 roots. A fresh independent `N=22,k=3` implementation also found
  zero losses among 20,636 qualifying roots. The closure problem is explicit: one pick raises the
  hole count from `k` to `k+1` without increasing `N`. A new independent scout is seeking either a
  complete-turn response that restores the budget or the first minimized obstruction.
- A bounded action diagnostic is surprisingly small: at `N=12` and `22`, one of the four smallest
  available counters is safe in every qualifying three-hole state. At `N=9` there is one exception,
  the tied state `R={1,3,4,6,7,9}`; adding the four largest candidates covers it. This is finite
  evidence for an extremal-move proof target, not yet a symbolic strategy.
- Integrated warning-strict `scripts/catch_up/DenseHoleReduction.lean`, SHA-256
  `fb3bf2e74c8e76a257800848c42e63b0e95a6ada0a40fb427faf8455c99c500b` (374 lines / 16,015
  bytes). It defines the exact catchable even-parity three-hole nonloss invariant and proves that,
  for `N≥4`, it implies `value (Icc 1 N)=draw`: every lower pair-deletion state has only two holes,
  while every legal child of `pairDeletionPosition N 1 2` has exactly at most three; nonloss of all
  those children rules out a winning move and makes the first pair draw. A second corollary rewrites
  the interval sum to the usual `N*(N+1)/2` surface statement. The target build passes all 8,054
  jobs; all three public declarations audit exactly to
  `[propext, Classical.choice, Quot.sound]`. It now also defines the stronger exact
  `DenseThreeHoleMinimumMoveSafe` candidate and Lean-proves that it implies the dense nonloss
  invariant by selecting the finite-set minimum; this is a conditional bridge, not a proof of
  minimum safety. Independent adversarial source audit passed every original reduction quantifier,
  perspective, threshold, build, and linter check. Updated audit SHA-256
  `d5fc86e87d6f50ab04e15cf51e7d08539e513965c993a261be7de799d38cdfdf`.
- The additive-triple module passed two independent source audits, but its recursive mechanism is
  stopped. At `N=11`,
  `Q=⟨Icc 1 11 \ {1,2,3,4,9},5⟩` is a draw, while exact catch `5` reaches the tied winning set
  `{6,7,8,10,11}`; only mask-dependent replies `7` and `10` draw. Thus disjoint additive triples
  accumulate an unbounded exact hole list and can leave a winning complement. The integrated
  reduction remains a valid conditional interface, but is not a complexity reduction. Its
  docstring was clarified; current SHA-256
  `15a0069b128f1ab2cd6bf6852641146dc0b33172d1c41cdf28d29c6d504c3928` (209 lines / 9,419
  bytes). Independent probe `HISTORICAL_TMP/probe.py`, SHA-256
  `4ef64b36f1a9aedf7cfc0c3bfca31a4df085c784847d6e60829f520610d78c2e`.
- A deliberately unprimed scout found a useful guardrail: for every `a≥5`,
  `Position ⟨{a,a+1,a+2,a+3},4⟩` is losing, despite even effective parity and an offline balanced
  partition. The `a=5` trap is reachable inside the `N=8` interval. This refutes parity-only,
  balanced-subset, shifted-tail, and static-pairing generalizations, but does not contradict the
  anchored dense-hole statement because the state has many missing low counters.
- Independent recurrence artifacts and cross-checks:
  `HISTORICAL_TMP/RESULTS.md` SHA-256
  `9ef6b21f1c2bec154f9178e0be589bd043ab1d57cef7b2e9ed6bc4292b12fe5b`;
  `audit.cpp` SHA-256 `c7c9e0a7b87eba944cabdcc7632a58cc813361cbb2f4b48decdc0a341f7bd0df`;
  `crosscheck.py` SHA-256
  `cde825930e6fa71af183680ead2d562f810f013e85ddfb5b9764dc7407519d05`. Whole-turn and
  absolute-score evaluators agreed on 8,953 and 17,906 comparisons; sanitizer runs were clean.
- Fresh N=22 source `HISTORICAL_TMP/dense_hole_n22_independent.cpp`, SHA-256
  `50fe3a2293d2387531671aae16436fb99f3d3e2949d2593a089c7dd566bccf90`; its 58,720,256-byte
  table completed in 0.438 seconds. Address/undefined-behavior sanitizers reproduced the N=9 and
  N=12 root counts with zero losses.
- After the dense and additive modules were integrated, a fresh warning-strict
  `lake --wfail build CatchUpResearch` passed all 8,113 jobs.
- After adding the hierarchy reduction and the formal minimum-move bridge, a newer warning-strict
  `lake --wfail build CatchUpResearch` passed all 8,114 jobs.
- The bounded action diagnostic has now collapsed to a single exact candidate: for every
  qualifying three-hole state at each `N=12,…,22`, the minimum available counter has move outcome
  different from `loss`. Independent per-size root counts are
  `1941,2646,3528,4608,5921,7506,9390,11600,14181,17182,20636`, with zero failures. The statement
  is sharply non-tautological: `N=11` has three failures, including the tied state with holes
  `{1,6,9}`, and `N=9` has 28. The executable one-step diagnostic is
  `HISTORICAL_TMP/dense_min_failures_20260809.cpp`; this is exact computational evidence, not yet a
  certificate or theorem.
- Integrated warning-strict `scripts/catch_up/DenseHoleHierarchy.lean`, SHA-256
  `f15d30971f35132ab2ea4091dc512b53fb8723a4f0e51a64549dc639178eb29c` (169 lines / 7,358
  bytes). It defines the exact hole count and hierarchy qualification, proves that a
  prefix-blocked state has `deficit - 1 ≤ holes`, and uses strong induction to reduce the entire
  `3*holes≤N` nonloss hierarchy to saturated or prefix-blocked states. Its 8,055-job target build
  passes; all three public theorems have exactly the standard axiom list. Audit SHA-256
  `64414612f17def3fda4dc1462cbbf217fba4c91432aeb2998d4460a3e86af732`.
- A naive hereditary proof of the hole hierarchy is blocked by a precise transition. At `N=9`,
  `Position ⟨{1,2,6,7,8,9},7⟩` is a win (hence still a nonloss), but its legal continuing move `2`
  reaches the losing four-hole child `Position ⟨{1,6,7,8,9},5⟩`. More generally, in a strong
  induction proof of the candidate `3h≤N` hierarchy, a hypothetical losing state with
  `3(h+1)≤N` cannot have any continuing move: such a child would have `h+1` holes and fall under
  induction. Hence the remaining core is exactly the union of saturated states
  `3h≤N<3(h+1)` and prefix-blocked states with no available counter below the deficit. This is a
  genuine reduction but not closure: the saturated family persists at hole density about one
  third. A warning-strict Lean formulation is in progress.
- The canonical completion “after the first minimum, keep taking successive minima until the turn
  catches” is also false. At `N=12`, the qualifying root
  `Position ⟨{1,3,4,5,6,7,8,9,10,11,12},12⟩` has a safe first minimum `1`, but the forced minimum
  continuation `1,3,4,5` leaves the opponent at
  `Position ⟨{6,7,8,9,10,11,12},1⟩`, which is a win; hence that completed turn loses. The number of
  such failures across the structured post-first-min continuation family is nonzero for every
  `N=12,…,21` (and happens to vanish at `N=22`). This decisively rules out a fixed minimum sweep;
  the first turn already needs adaptive play.

## Dense minimum route review — 2026-08-09 08:00 EDT

- Integrated warning-strict `scripts/catch_up/DenseMinimumShiftedReduction.lean`, SHA-256
  `6bdb95f14ff3769af18f91abb26c9c44b8c005b7211dce19d5d2679e56655ce6` (321 lines / 14,183
  bytes). It proves the exact equivalence between `DenseThreeHoleMinimumMoveSafe N` and eight
  shifted-tail families: for minimum `m=1,2,3,4`, continuation children are nonlosing and small
  catch children are nonwinning, with respective upper-tail hole budgets `3,2,1,0`. Both
  directions reconstruct the parent and check exact Finset decomposition, catch/continue
  perspective, parity, catchability, and natural subtraction. A fresh independent audit found no
  mathematical defect and emphasized that this is an exact reparameterization, not a weakening of
  the hard claim. Its target build and the 8,115-job research build pass; both public theorems use
  only `[propext, Classical.choice, Quot.sound]`. Separate audit SHA-256
  `3b1adef924ca40d1fde5983dca839d45497e881cdb5a464c86661007650bb13a`.
- Reusing existing packed exact tables, an independent scout extended the minimum-move zero-failure
  evidence to `N=23,24,27,28`, covering respectively 24,576; 29,057; 46,256; and 53,397
  qualifying roots. Reproducer `HISTORICAL_TMP/dense_min_strategy_packed_audit_20260809.py`, SHA-256
  `1e12cbd30405089aebe32f549f3cd9d861b8af7c29e6cb707c9585872267c35b`. This is exact finite
  evidence from pre-existing tables, not a certificate or parametric proof.
- The same audit found that forcing every protected completed turn to leave deficit at most four
  fails every shifted root already at `N=12`; the predecessor/adjacent-response identity therefore
  cannot close through a bounded-deficit invariant alone. Together with the false minimum sweep
  and the exact shifted equivalence, this meets the stopping rule for table expansion or renamed
  one-step minimum variants. The dense minimum theorem itself remains credible, but is suspended
  as a primary route until a genuinely new closure mechanism appears.
- The next primary theoretical gate is materially different: prove or refute the saturated
  `N=3h` hierarchy through a triple-block, matching, or Hall-type strategy. One scout remains on a
  sharply structured shifted-tail closure; the next freed slot is reserved for a fresh unprimed
  alternative to prevent the campaign from collapsing onto one mechanism.
- That structured closure is now stopped after a decisive adversarial audit. The two proposed
  nonwin predicates `P4` (at most four holes, deficit at most four, corresponding low prefix
  missing) and `B5` (at most five holes, counter `1` and one short consecutive block missing) have
  no wins in exact checks at `N=16,…,24,27,28`, but they are not mutually closed. At `N=16`, the
  `P4` draw `Position ⟨{5,…,16},0⟩` after challenge `5` either leaves six holes under any small
  catch or deficit `11` under the top reply. The `B5` draw
  `Position ⟨{2,7,…,16},3⟩` has continuation `2` to the six-hole-prefix draw
  `Position ⟨{7,…,16},1⟩`. Thus raw recursion immediately resumes hole growth. The broader `B5`
  threshold is sharp at `N=15`, where `Position ⟨{2,7,…,15},3⟩` is a win. Full report
  `HISTORICAL_TMP/DenseMinimumStrategyReport_20260809.md`, SHA-256
  `7e302150b5970edc9f553fca1be2cac89e1498f3123493cbf74dc722c7db732c`.
- Pure adjacent response is independently dead: after opening `1` from `Icc 1 12`, an adversary
  can take `2,4,6,8,10,12`; forced successors `3,5,7,9,11` grow the protected deficit from one to
  six and leave no counters. More generally every one of the 341 shifted catch roots at `N=12` is
  safe without a bound but fails the restriction that every protected completed turn leave
  deficit at most four. This rejects bounded-deficit predecessor strategies, not arbitrary adaptive
  play.
- The algebra behind the stopped adaptive turn was nevertheless preserved as a warning-strict Lean
  scratch theorem. `HISTORICAL_TMP/StructuredPostMinReduction.lean`, SHA-256
  `26576bc9d65f24544dbb47d832ed6afda17bee8f44b42cdeb27fcb3489a8e05b` (271 lines / 9,821
  bytes), proves that the least catching counter lands in the five-hole distinguished-block family,
  while the no-ceiling maximum-then-minimum turn lands in a rebased three-hole prefix family. Both
  theorem axiom audits are standard. It is intentionally not integrated yet: the recursive
  mechanism is false, and the scratch still needs production header/attributes. Full report
  `HISTORICAL_TMP/StructuredPostMinReductionReport_20260809.md`, SHA-256
  `ac0b9d9ab2b182ffa2dae824876e0d966a270f3be3c9d01b43b0511cc0b9bd8a`.

## Saturated exact-sum audit — 2026-08-09 08:29 EDT

- A sound strategy-stealing lemma has been isolated. If a losing position has a nonempty chosen
  subset whose counter sum is exactly the current deficit, then completing that exact turn leaves
  a tied winning root; its globally unique winning opening is strictly larger than the largest
  chosen counter. The proof propagates loss through all chosen counters except the maximum, then
  invokes the available-deficit/cross-order argument at that maximum. This is now integrated as
  warning-strict `scripts/catch_up/ExactSumLossObstruction.lean`, SHA-256
  `d9e996a5a444de0bbdf11d48ce778e4d35d2d3cbb2be14554597a3e3c2779096` (251 lines / 11,344
  bytes after the later exact-block-dominance corollary). Its 8,056-job target build passes, and the public theorem's axiom audit is exactly
  `[propext, Classical.choice, Quot.sound]`; audit SHA-256
  `88879462a8db5e6134bf0371f2afd85e9ba34ad47a2a37fd54bb2329cc521939`. A fresh full
  warning-strict `CatchUpResearch` build also passes all 8,116 jobs after integration.
- The tempting increasing-target iteration is not valid. Even parity alone already fails at
  `Position ⟨{4,5,6},9⟩`: the position loses, the exact subset `{4,5}` leaves the tied singleton
  `{6}`, and its unique winner `6` is below the old target `9`. More decisively, the saturated
  even tied root `{1,4,5,6}` at `N=6` (two holes, hence `3h=N`) wins uniquely at opening `4`, but
  its resulting nonterminal loss `Position ⟨{1,5,6},4⟩` has no exact-sum subset at all. Thus the
  density/even hypotheses are not inherited after the forced winning opening and cannot justify a
  renamed exact-sum chain.
- A bounded independent probe of the one-over-density failure boundary found a useful but still
  empirical dichotomy: at `N=9` with four holes, the three even losses consist of one with an
  exact subset forcing a larger residual winner and two with no exact subset; at `N=12` with five
  holes, the five even losses split four versus one in the same way. Reproducer
  `HISTORICAL_TMP/exact_sum_increase_probe_20260809.py`. This may help diagnose a genuinely new
  saturated contradiction, but it is not a proof mechanism by itself and will not be table-expanded.

## Every opening draws at twelve — 2026-08-09 08:56 EDT

- Integrated `scripts/catch_up/N12EveryOpeningCertificate.lean`, SHA-256
  `22e0e4b6a04077539703dafdf0f14498efa7f42e9f5cc3c89515a24032f4e5ab` (109 lines / 4,401
  bytes). It proves the strict finite strengthening
  `EveryOpeningDraw (Finset.Icc 1 12)`: every one of the twelve possible openings is drawn, not
  merely the root game. This is the first all-opening theorem in the retained development.
- The new player-one certificate is a deterministic checked extraction: the bounded solver run
  reported 43,168 solved states and the extracted shared DAG contains 3,480 nodes. The theorem
  independently checks the DAG, proves that all twelve opening states occur in it, obtains
  player-one safety at each opening through the generic certificate soundness theorem, and combines
  that with the existing all-opening player-two certificate from `N12Certificate`.
- `lake --wfail build catch_up.N12EveryOpeningCertificate` passes all 8,066 jobs. The warning-strict
  axiom audit for the checker theorem, all-opening containment, player-one safety, and final
  `every_opening_draw` theorem is exactly
  `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`; this records the
  explicit `native_decide` trust boundary. Audit SHA-256
  `9ffcc645b10d624a70ae418634b4d5ae3ed994283d0506b4aadc53e1903a2a7e`. There is no
  `sorry`, declared axiom, `unsafe`, or suppressed linter in the production module.
- Trust limitation: the extractor and exact solver select the finite DAG, but they are not assumed
  sound. Soundness comes from the separately proved checker theorem applied to the checked DAG.
  The DAG is defined by deterministic extraction rather than serialized as 3,480 literal nodes;
  consequently this is a proof-checked generated certificate, not a purely literal certificate.

## Maximum-counter potential boundary — 2026-08-09 08:59 EDT

- Integrated warning-strict `scripts/catch_up/MaximumCounterPotential.lean`, SHA-256
  `dc79cb874c591c99cbc81c81ca2702e0f7d82563646463d25066fdd56a5d2b09` (444 lines / 21,649
  bytes). With retained maximum `M`, deficit `d`, and lower sum `L`, it formalizes the signed
  numerator `L+d-M`: a continuing lower pick `x` subtracts `2x`, a catching lower pick subtracts
  `2d`, and a lower block followed by `M` hands over an endpoint whose terminal/draw threshold is
  the exact comparison `L+d` versus `M+2*block.sum`.
- The clean structural theorem classifies the zero-potential boundary for positive counters. When
  `L+d=M`, the position is drawn exactly when every lower counter catches immediately; otherwise
  any positive lower continuation followed by `M` wins. All nine public theorem axiom audits are
  exactly `[propext, Classical.choice, Quot.sound]`. Target build passes all 8,052 jobs; audit
  SHA-256 `5511dc418989162cc8b8b582ded958008cc12446407bf8461e8782d53ce10a15`.
- The scalar-controller route is stopped, not promoted as a parametric solution. At reachable
  `N=7` states, `{2,3,5}` and `{1,4,5}` at deficit `2` have identical
  `(card,max,deficit,potential)=(3,5,2,2)` but values loss and draw. The drawn reachable state
  `{4,5,6,7}` at deficit `2` also requires taking the maximum while the potential is still positive;
  every lower first move loses. Thus the local theorem is sharp API, while any global induction
  must retain genuine subset/hole geometry rather than this scalar alone. Full adversarial report
  `HISTORICAL_TMP/MaximumCounterPotentialAuditReport_20260809.md`, SHA-256
  `4a5ec577817ba3dda4efcbb97971a899dcca1c2c541fea0ac0b9acd8a55067a0`.
- A fresh warning-strict `lake --wfail build CatchUpResearch` after both integrations passes all
  8,118 jobs.

## Dense-loss residual injection — 2026-08-09 09:40 EDT

- Integrated warning-strict `scripts/catch_up/DenseLossInjection.lean`, SHA-256
  `90dfec1600d31837159f53666e72042f6fc9aefca34bd9b0422ef7425d9a5b10`. For a hypothetical
  losing position supported in `Icc 1 N` with at most three holes and deficit `7 ≤ d ≤ N`, the
  module first proves that one of the exact blocks `{d}`, `{1,d-1}`, `{2,d-2}`, or `{3,d-3}` is
  available. Applying the exact-sum loss obstruction yields a tied residual with a globally unique
  winning opening `w ≥ d-2`, `w ≠ d`.
- The sharp final alternative records the entire failure of strict growth. Either some exact block
  of at most two counters produces a residual winning opening `w>d`, or the original loss descends
  by an explicitly legal continuing move to one of three prefix-blocked states: deficit one after
  removing `d-1`; deficit two after removing `d-2`; or, when counter one remains, deficit one after
  additionally removing it. The production theorem exposes membership of every continuing counter,
  so these alternatives can be replayed without reconstructing legality.
- This is a genuine local reduction, but not a closed induction: the small-deficit children carry
  larger hole budgets and the same exact-sum argument has no available target. The exact-sum/
  complement route is therefore stopped at these prefix-blocked endpoints until a qualitatively new
  closure mechanism appears. Scaling the sparse loss `{1,2,3,4,5,11}` at deficit five shows that
  even parity and three disjoint exact blocks do not force distinct residual winners.
- `lake --wfail build catch_up.DenseLossInjection` passes all 8,057 jobs. All four public theorem
  axiom audits are exactly `[propext, Classical.choice, Quot.sound]`; production audit SHA-256
  `bf276b21ab364bd5b2893660f442d091ef9683b2ee9802d9331d59b93b1487e4`. The final scratch report
  is `HISTORICAL_TMP/DenseLossInjectionReport_20260809.md`, SHA-256
  `f5f1dff3ee0ed29e5ba17ae6e235243666fbc0209750dee8e9f2dd2617f38add`.

## Consecutive quadruple-block candidate — 2026-08-09 09:40 EDT

- An independent quota scout found a materially different direct candidate: a tied set that is a
  pairwise-disjoint union of translated blocks `{a,a+1,a+2,a+3}` appears drawn; the same is true
  after adjoining the distinguished initial triple `{1,2,3}`. If proved, these two statements
  immediately imply the interval conjecture for `N ≡ 0` and `N ≡ 3 (mod 4)` respectively.
- Initial exact evidence covers every disjoint pair with starts up to 17/21, every disjoint triple
  with starts up to 13, and ten widely separated four-block unions. The specificity is real:
  arbitrary draw-set plus quadruple-block closure is false, for example the tied set
  `{6,10,14,18}` becomes a win after adjoining `{21,22,23,24}`; translating the distinguished
  triple also fails. This is exploratory exact evidence, not yet a theorem or certificate.
- All three live scouts have been redirected to independently derive or falsify the block class,
  with requested deliverables restricted to an exact response invariant/strategy or a minimized
  counterexample. Expensive duplicate interval computation remains prohibited.
- A fresh warning-strict `lake --wfail build CatchUpResearch` after the dense-loss integration
  passes all 8,119 jobs; `git diff --check` remains clean and the index is untouched.

## Adjacent-pair falsification and turn-level API — 2026-08-09 10:07 EDT

- The tempting strengthening from quadruples to an even number of arbitrary adjacent pairs is
  false. The tied 16-counter set with pair starts
  `(3,6,15,58,66,77,82,97)` has total `816` and exact value loss: every one of its 16 openings
  loses. An independent recurrence reproduced the value and full opening profile. Inside this
  witness, deleting two pairs yields a subset-minimal six-pair win at starts
  `(3,58,66,77,82,97)`, total `772`, with unique winning opening `4`; replacing the first start by
  `6` or `15` gives analogous unique winners `7` or `16`. Every four-pair subset of the original
  eight-pair loss draws. Thus the broad phase passed large finite scans but was a genuine finite
  mirage rather than an induction theorem.
- The reply-graph repair is also blocked. A four-pair drawn root at starts `(8,12,18,23)` contains
  the directed cycle `12 → 24 → 19 → 12`, while another root has upward edge `2 → 5`. Hence
  numeric, reverse-numeric, pair-index, orientation, lexicographic, and any global acyclic rank all
  fail before the root counterexample. The mate-pair edge remains neutral throughout bounded tests,
  but a neutral perfect matching alone does not supply a safe opening.
- The clean non-root obstruction is parametric. For `a ≥ 5` and `a+3 ≤ b ≤ 2a-2`,
  `Position ⟨{a,a+1,b,b+1},2⟩` is losing even though its effective total is even and its draw
  quotas have a perfect one-from-each-pair partition. The smallest state is `{5,6,8,9}` at deficit
  two, and it occurs on a legal history inside `Icc 1 12`. Likewise
  `Position ⟨{a,a+1,a+2,a+3},4⟩` is losing for every `a≥5`, despite an exact top-pair/bottom-pair
  quota partition. These traps prove that no hereditary adjacent-pair or static balanced-quota
  invariant can establish the root theorem.
- Genuine consecutive quadruples add metric structure that arbitrary adjacent pairs lack. Their
  two-counter subset sums fill every value `2a+1,…,2a+5`, yielding exact repair offsets
  `-2,-1,0,1,2` around the half-block sum `2a+3`. This near-quota ladder is the remaining direct
  mechanism under investigation; the deficit-four loss shows it must be used strategically, not
  asserted as unconditional non-root safety.
- Integrated `scripts/catch_up/CompletedTurn.lean`, SHA-256
  `ac8fa0b4c97554e27b48dce89359052b6db8b945e6e08118f33fa50e802522cd` (442 lines / 19,742
  bytes). It defines ordered completed-turn and actual-step traces, the unordered `TurnSet`
  specification, and an exact endpoint. It proves every traced pick is a legal nonterminal step,
  that the endpoint depends only on the chosen set, and the exact equivalence between an ordered
  completed turn and a chosen subset with distinguished final catching counter. This removes
  factorial ordering redundancy from future turn-level strategy arguments while retaining kernel
  soundness.
- `lake --wfail build catch_up.CompletedTurn` passes all 8,052 jobs. All 20 public theorem axiom
  audits are exactly `[propext, Classical.choice, Quot.sound]`; production audit SHA-256
  `ea48ec0c4f30a161f930ebbb32ae575aa908cd478969a4922164f1e0d15600c0`. There is no `sorry`,
  native computation, unsafe declaration, diagnostic command, or linter suppression in the module.
- A fresh warning-strict `lake --wfail build CatchUpResearch` passes all 8,120 jobs after this
  integration.

## Order-free completed turns and the deficit-four block obstruction — 2026-08-09 10:24 EDT

- Strengthened `scripts/catch_up/CompletedTurn.lean` to 543 lines / 24,958 bytes, SHA-256
  `b2ba5ae3e8417076f8128613d27bd734c7d7efaad8a34ea548143834158ce6cc`. At positive deficit
  `d`, a nonempty available subset `A` is exactly the support of one completed turn iff
  `d ≤ A.sum` and `A.sum < d + A.max'`. The companion theorem includes the exact normalized
  endpoint and is equivalent to an ordered legal trace. This is the rigorous subset-turn recurrence
  needed for block arguments: it removes factorial order choices without weakening legality.
- The same API now proves the exact doubled-quota transport identities. After a completed turn,
  `remaining.sum + deficit` at the endpoint equals the old `remaining.sum - deficit`; the old
  mover's residual numerator is the old `remaining.sum + deficit` minus twice the turn sum. These
  are unconditional endpoint identities, not a claimed quota strategy.
- `lake --wfail build catch_up.CompletedTurn` passes all 8,052 jobs. All four new theorem audits use
  exactly `[propext, Classical.choice, Quot.sound]`; audit SHA-256
  `7a78e9ab03242cb7fff93555be4abfb35dbec8eb5ea3ffc020efb261a18dc7ec`.
- Added the named corollary
  `CatchUpSearch.TopFourClassification.value_top_four_deficit_four`: for every `a ≥ 5`, the
  normalized position on `{a,a+1,a+2,a+3}` at deficit four is loss. This is derived from the
  existing exact four-counter classifier, not native computation. Updated module SHA-256
  `3faf7438e4db823c61e729dc30409e23f828147e307957966d2eca5f8448c874`; target build passes and
  the theorem audit is exactly `[propext, Classical.choice, Quot.sound]`, audit SHA-256
  `638abf9a79241f338d768c72d20dbc621c4efa28624ccac5e85498522f9c6be4`.

## Quad-block stress test and phase stop — 2026-08-09 10:34 EDT

- The strongest targeted lift remains drawn. Exact recurrence gives
  `Q_4 ∪ Q_76 ∪ Q_92 ∪ Q_116 ∪ Q_128 ∪ Q_144` value draw, where
  `Q_a={a,a+1,a+2,a+3}`. Openings `5` and `7` draw and the other 22 lose. The packed solver visited
  138,921,536 states in 15.99 seconds using a collision-free parity-compressed 296 MiB memo; source
  `HISTORICAL_TMP/quad_solve.cpp` SHA-256
  `9cfe0e7108afd4e126683527cc921c7f517d3fc901402faf58d239e7c4506c86`. This is exact but
  untrusted finite computation, not a certificate or parametric theorem.
- The distance-two pair `5,7` is neutral: both opening orders reach the identical residual at
  deficit two, which the exact recurrence evaluates as draw. The known adjacent-pair loss core
  instead has the explicit directed triangle `3 → 7 → 4 → 3`; its compact winning-reply map is
  `f(3)=7`, `f(7)=4`, and `f(x)=3` otherwise. Adding the gap-two companion pairs destroys that
  cycle in the tested lift.
- A natural mutual phase was sharply tested and stopped. Let `D` be a tied union of whole
  quadruples and `F` a whole-quad union plus one adjacent dangling pair at deficit one. Thousands
  of bounded `F` instances draw, which would provide a neutral adjacent mate for every `D`
  opening. But `D/F` is not response-closed: from drawn
  `({2,3,4,5,6,7},1)`, the move `6` cannot be repaired by mate `7` (it leaves the winning state
  `({2,3,4,5},2)`); the actual response `2,5` reaches the losing residual `({3,4,7},2)`, outside
  both phases. This is an explicit partial-quad/singleton escape, so the campaign will not grow a
  renamed phase table around `D/F`.
- The remaining quad-specific candidate is reply-digraph acyclicity. Four adversarial four-block
  roots were acyclic despite having edges in both numeric and block directions and realizing all
  16 within-block offset source/target patterns across graphs. Thus no fixed coordinate rank
  survives; a proof must exclude shortest cycles using genuine quad geometry. A fresh independent
  adversary is now seeking either that mechanism or the first quad-union cycle.

## Quad reply-cycle and internal-neutrality falsifications — 2026-08-09 10:50 EDT

- Reply-digraph acyclicity is false even for four genuine blocks. Let
  `S=Q_1 ∪ Q_27 ∪ Q_34 ∪ Q_43`, total `444`. With
  `V(a,b)=Position.value ⟨S\{a,b},b-a⟩` for `a<b`, exact recurrence gives
  `V(29,46)=loss`, `V(36,46)=win`, and `V(29,36)=win`, hence the unique directed triangle
  `29 → 46 → 36 → 29`. The root itself is draw: openings `1,2,3,4` draw and all twelve upper
  openings lose. Every within-block pair is neutral in this witness, so even the strongest local
  neutral cover coexists with a global cycle. All 14 nonempty proper whole-block subunions are
  acyclic, making the cycle inclusion-minimal under deleting blocks.
- Two independently implemented normalized recurrences agree. C++ artifact
  `HISTORICAL_TMP/catchup_quad_wave7.cpp` SHA-256
  `e8cbb349bb34eefd15c58f2ec3d6907b4bdceb3ca47f46a9cd36573b2ce047a8` reports 60 directed
  edges, the unique triangle, and 159,398 memo labels; independent Python artifact
  `HISTORICAL_TMP/interval_cycle_exclusion_probe.py` SHA-256
  `2b74fb9ae8e2033b7439f8c26577895cd0e6028ac38bdab3c6def55c25527e10` agrees. This is exact
  finite computational evidence, not a Lean certificate. It falsifies the acyclic proof route, not
  the still-drawn quad root.
- The blanket internal-neutrality claim is independently false at one block. For every `a≥3`,
  opening `a+2` has winning reply `a+1`; the player continues into
  `Position ⟨{a,a+3},1⟩`, whose value is win. Thus the middle pair is oriented high-to-low even
  though four other reflection-compatible pairs have canonical drawing lines. Integrated three
  warning-strict regression theorems into `scripts/catch_up/ReplyDigraphReduction.lean`, now 458
  lines / 19,770 bytes, SHA-256
  `1373186c38130dd500e36b6c69287329836064182c43079cb232f116db4f53a2`. Target build passes all
  8,055 jobs; all three theorem audits are exactly `[propext, Classical.choice, Quot.sound]`, audit
  SHA-256 `05a238b961003d96a5902421a3881b3401778084ada9515314a2ee780b41dc3e`.
- Consequently the quad route has no surviving bounded proof mechanism: local cancellation proves
  only one minimax polarity; the `D/F` phases escape immediately; fixed pivots and coordinate ranks
  fail; neutral internal covers do not prevent cycles. The broad quad-root statement remains
  empirically plausible, but continuing now would require the same universal-reply complexity as
  the original game. It is marked blocked unless the bounded six-block random search finds an
  outright counterexample or a genuinely new invariant appears.
- A fresh `lake --wfail build CatchUpResearch` after the completed-turn quota and reply-graph
  regression integrations passes all 8,120 jobs; `git diff --check` is clean.

## Bounded six-quad counterexample search — 2026-08-09 10:56 EDT

- A single designated computation owner completed 20 exact six-quad roots spanning consecutive,
  clustered, arithmetic, geometric, and widely separated starts. Every root drew: across all 480
  openings, 118 were losing for the opener, 362 drawing, and none winning. This strengthens the
  empirical quad-root signal but does not repair the falsified proof mechanisms.
- The parity-compressed recurrence performed 31,235,199,189 runtime checks of both `d≤maxCounter`
  and the parity index invariant with no failure. Total measured solver time was about 398.4
  seconds, within the preregistered seven-minute cap; no seven-block instance was run. Table memory
  stayed between 48 and 296 MiB.
- Reproducible results `HISTORICAL_TMP/quad_search6_results.tsv`, SHA-256
  `02623c718459ed8648d855c3e2ea08d9b0c1217851dbaf190b987af7bb7fce33`; adapted source
  `HISTORICAL_TMP/quad_search6.cpp`, SHA-256
  `8d6166bc359c6494c4b231223b93072fba8af28917e919069d639ecabfec6f7d`; binary SHA-256
  `9f61bd1ccfd3bb8cf5c459a5c9ae6a8e6e0fb0b04908aa49280e20df3e5ba346`. Trust remains an
  independently implemented exact recurrence, not a Lean certificate.
- Per the stop gate, the campaign is not expanding this search to seven blocks. The empirical
  statement has survived, but all bounded strategy/graph closures tested so far reduce to the full
  universal-reply problem. Research capacity has been redirected to fresh interval-only and
  turn-subset mechanisms.

## Completed-turn minimax target and exact-block obstruction — 2026-08-09 11:13 EDT

- The order-free turn API suggests an exact minimax flattening, not a heuristic: at every
  nonterminal normalized position, nonloss should be equivalent to the existence of one legal
  completed-turn endpoint that is nonwinning for the new mover, while nonwin should be equivalent
  to every legal completed-turn endpoint being nonlosing. Equivalently, win is existential and
  loss universal over the finite family of legal subsets. A warning-strict Lean proof extending
  the already checked backward-safety bridge is now in progress; this claim is not yet promoted to
  production.
- The flattening does not make exact catches sufficient. Exact recurrence independently confirms
  that `Position ⟨{3,4,7,11},7⟩` is loss. Its seven legal completed-turn supports and endpoint
  values are `{3,4}→win`, `{7}→win`, `{3,7}→win`, `{4,7}→win`, `{11}→win`,
  `{3,11}→win`, and `{4,11}→win`; thus every macro choice loses. In particular, the two disjoint
  exact blocks `{7}` and `{3,4}` both leave tied roots uniquely won by opening `11`.
- This loss is not an unreachable sparse curiosity. The legal singleton-turn history
  `1,2,5,6,8,9,10` from tied `Icc 1 11` has boundary deficits
  `0,1,1,4,2,6,3,7` and reaches exactly that state. Hence multiple exact representations do not
  force distinct residual winners, even on an even-parity reachable branch; any injection theorem
  must exploit substantially stronger density that survives the history.
- The all-pair scout independently rediscovered the already integrated additive-triple rule:
  play `b-a` unless `b=2a`, use `a+1` in the nontrivial doubling case, and isolate `(1,2)`.
  Since `AdditiveTripleReduction.lean` already proves precisely this and the remaining
  three-hole residuals recreate the unresolved dense minimax families, that route was stopped and
  the slot recycled to a joint four-residue induction.

## Complete-set and joint-residue falsifications — 2026-08-09 11:31 EDT

- The weakened generalization “every subset-sum-complete distinct set of even total is nonlosing”
  is false. The exact set
  `S={1,2,3,7,14,23,37,68,101,111,123}` has total `490`; its successive prefix sums are
  `0,1,3,6,13,27,50,87,155,256,367`, so every next counter is at most one plus the preceding
  sum and hence `S` represents every subtotal from `0` through `490`. Exact normalized minimax
  nevertheless gives `value(S)=loss`, and every one of its eleven opening outcomes is loss.
- Root independently replayed the 1,831-label recurrence and all embedded assertions in
  `HISTORICAL_TMP/verify.py`, SHA-256
  `e44497cf6131bfce1d71d805711229c09f970d1009a01445788d3d2c0d76ec30`. Exhaustive search found
  no such loss through cardinality eight, so `9≤|S_min|≤11` is only a computational bracket,
  not a minimality theorem. This kills both the original complete-set draw conjecture and its
  one-sided nonloss weakening; completeness is also destroyed immediately when counter `1` is
  opened, so it offered no hereditary interval invariant.
- The joint four-residue/add-one strategy also stops at a forced value flip. Warning-strict Lean
  scratch `HISTORICAL_TMP/JointResidueAddOneScout_20260809.lean`, 105 lines / 4,750 bytes, SHA-256
  `1c9e0c851856c89476c32994e3f937c9c50932025421728a9d48f984b767121a`, proves that winning
  opening `3` forces `P_N(2,3)=loss`, whereas winning opening `2` forces the same pair state to be
  `win`; likewise the `1→2` transfer requires `P_N(1,2)` to flip `win→loss`.
- Exact packed `N=23→24` data show every possible `W/L` add-one transition already on dense
  odd-parity states with at most two holes and deficit at most three:
  `(I_23,1):W→L`, `(I_23,3):W→W`, `(I_23\{1},0):L→W`, and
  `(I_23\{1,4},2):L→L`. Thus parity, hole count, and winning-opening uniqueness do not control
  the required flip. The route has reduced to generic add-one minimax and is marked blocked.

## Completed-turn minimax integration — 2026-08-09 11:48 EDT

- `scripts/catch_up/CompletedTurn.lean` now proves exact turn-level minimax on top of the existing
  ordered/unordered turn semantics. For a nonterminal node, friendly-player safety is equivalent
  to one safe completed-turn endpoint, while waiting-player safety is equivalent to every endpoint
  being safe. In normalized form, `value≠loss` is existential over endpoints whose new mover does
  not win, and `value≠win` is universal over endpoints whose new mover does not lose.
- At positive deficit, both directions are stated without an unnecessary nonempty-support
  hypothesis: legal subsets are exactly the nonempty `A⊆R` satisfying
  `d≤sum(A)<d+max(A)`. A final corollary proves that a position draws exactly when every legal
  completed-turn endpoint is nonlosing for the new mover and at least one endpoint draws.
- The production file is 888 lines / 41,446 bytes, SHA-256
  `738557c54208235340c6e267299f5fa86efeda8626fb185f67bc44e98d75cff4`.
  Warning-strict target build passes 8,052 jobs, `CatchUpResearch` passes 8,120, and the full default
  build passes 9,010. Root axiom audit
  `HISTORICAL_TMP/CompletedTurnMacroAxiomAudit_root_20260809.lean`, SHA-256
  `de201b9141bb74383ebbe3673181da73444f94f94e8597c57198c252d28b5869`, reports exactly
  `[propext, Classical.choice, Quot.sound]` for all twelve new declarations.
- A fresh independent production audit reconstructed quantifier polarity, the one mover switch,
  endpoint terminal cases, guarded natural subtraction, positive-deficit nonemptiness, the
  half-open subset condition, and the draw equivalence. It found no actionable defect; audit
  `HISTORICAL_TMP/CompletedTurnIntegratedAudit_20260809.lean`, SHA-256
  `fd37d4c01ba452c1a73bc9e748925d6581a48c396c92983d87142e0cccb595b7`.
- The semantics are a durable formal deliverable, not a strategy: the reachable loss
  `({3,4,7,11},7)` has every legal macro endpoint winning for the next mover. The associated Python
  search may corroborate that obstruction but does **not** justify its earlier unrestricted
  minimality wording because it bounded deficit by the remaining maximum rather than enumerating
  the actual reachable set. No minimality claim is retained.

## Unbounded obligation memory audit — 2026-08-09 11:53 EDT

- Unbounded capacity does not repair the natural complement/diagonal reply mechanisms. For a fixed
  perfect matching, the strongest tested policy lets the protected player choose **any** live owed
  mate and make an unrestricted optimal move whenever no debt is live; this strictly contains the
  corresponding FIFO and LIFO policies. Exact minimax over all 105 perfect matchings of `Icc 1 8`
  finds no universally nonlosing policy: 103 fail after opening `1`, and the remaining two fail
  after opening `2`.
- The true-drawn complement target `Position({1,2,3,6,7,8},1)` is a policy loss after every first
  protected pick. One explicit branch, beginning from the split `4` versus `5`, is
  `F:1,O:2,F:7,O:6,F:3,O:8`; every pick catches, the debt word is empty, yet the final scores are
  `15–21`. Cancelling a complement pair forgets the signed residue `C-2x`; an additive debt weight
  would need simultaneously `w(x)=x` at creation and `w(x)=C-x` at discharge. Retaining all such
  residues reconstructs the actual score gap rather than yielding a new monotone invariant.
- A stronger dynamic same-quad policy also fails on the drawn root `Q_2∪Q_6`: after opening `6`,
  every allowed first response `7,8,9` loses under the policy. Exact-catch stacks fail already on
  the legal `I_4` history `1,3`, where `Position({2,4},2)` draws, exact catch `2` loses, and
  overshoot `4` draws.
- Queue depth is genuinely unbounded but not well-founded. For `k≥2`, put
  `T_k=k(k+1)/2` and `N=4(T_k+1)`. Opening `T_k`, followed by the opponent's legal exact turn
  `1,…,k`, creates `k` live complement debts; from the resulting tie the protected player can
  discharge only one before the turn switches, leaving at least `k-1`. Only remaining-cardinality
  is automatically decreasing, which is the original full minimax recursion.
- Root replayed both independent exact implementations. Main verifier
  `HISTORICAL_TMP/UnboundedObligationAudit_20260809.py`, SHA-256
  `68cc5484cc36df1c1663e83f74eebf73a75b9f09ae3fc886f2ff059110344b9b`, visits 791 normalized
  states and asserts every profile above. Independent bit-mask checker
  `HISTORICAL_TMP/UnboundedPairQueueIndependent_20260809.py`, SHA-256
  `83a50a794dbedf273fcf42022ee2e3db3eaf216c2ec3483b6f34525e78bf83a7`, reproduces the 105-
  matching distribution and complement profile. Full report SHA-256
  `65072c8d1324a1e4393bc83e59ce9d49599a40cc576b75762528f593496e4ab8`. Trust is exact finite
  computation plus direct algebra, not Lean. Fixed queues/stacks are stopped; reopen only with an
  independent signed-residue endpoint theorem that does not query minimax or store the full mask.

## Completed-turn reflection and complement-duality stop — 2026-08-09 12:23 EDT

- Added `scripts/catch_up/CompletedTurnReflection.lean`, 158 lines / 6,582 bytes, SHA-256
  `83c6985f3738d0bdd0706ad74119065894b48d28e64481bac20f70d0e1ecea33`. At zero deficit a
  completed turn is exactly a singleton. At positive excess `e=sum(A)-d`, replaying the same
  chosen set at deficit `e` is legal exactly when `d<max(A)`; reflection is involutive. If the old
  deficit counter is unavailable, the positive and zero-excess branches combine into the same
  clean iff, and every nonreplayable chosen set lies wholly below the old deficit.
- Warning-strict target builds pass. Axiom audit
  `HISTORICAL_TMP/CompletedTurnReflectionAxiomAudit_20260809.lean`, SHA-256
  `8fd48909fb8f7c0d010b0ea94f5deca5626269684afc5086e81b55fa6e390185`, reports only
  `[propext, Classical.choice, Quot.sound]` (the arithmetic involution itself omits choice).
  A fresh read-only audit checked all quantifiers and 16,384 bounded position/set instances and
  found no defect; source SHA stayed unchanged. It recommends retaining the native-decided
  reachable counterexample only in campaign evidence.
- The reflection has no endpoint-value polarity. From the even-total interval `Icc 1 7`, opening
  `1` followed by the legal singleton turns `2,5,7,6` reaches
  `Position({3,4},3)`. Its complete legal-turn hypergraph is exactly `{{3},{4}}`, so complement
  gives a perfect involution, yet both endpoints are wins for the new mover and the source is loss.
  Warning-strict Lean regression `HISTORICAL_TMP/MacroTurnComplementDualityCounterexample_20260809.lean`,
  SHA-256 `95eaf097aa1a70d640008dcd62b8602dd90f7afe580579d45cc30c631dbbd47d`, and independent recurrence
  `HISTORICAL_TMP/MacroTurnComplementDualityAudit_20260809.py`, SHA-256
  `43f682718406b0ef2500f3a56f72437b7f9649d84c12e0706ce966a39cf54f5c`, agree. The regression uses
  `native_decide` and remains scratch evidence; the reusable reflection API has the standard trust
  boundary. Complement/local-order duality is stopped unless a separate endpoint-value theorem
  appears.

## Infinite reachable tied-top-five trap — 2026-08-09 12:23 EDT

- Added `scripts/catch_up/FiveConsecutiveTrap.lean`, now 296 lines / 12,877 bytes, SHA-256
  `387ffd095115d848db5bd1323475bb8270e0737d46e23ae4dfeb2fb60e4dc80b`. Using the existing exact
  top-four classifier, Lean proves that `value(Icc a (a+4))=win` for every `a≥4`: opening `a`
  hands the opponent four consecutive counters at deficit `a`, an exact symbolic loss.
- For every `k≥2`, Lean constructs a legal history after opening `3` in `Icc 1 (4*k)`: player two
  takes `1,2`, then each quartet beginning at `low=4,8,…,4*k-8` is consumed in the order
  `low,low+1,low+3,low+2`. Every quartet returns to a tie with player one to move, leaving exactly
  `Icc (4*k-4) (4*k)`. A final theorem combines this reachability with the normalized endpoint
  value `win`. The statement is existential reachability, not forced or optimal play.
- The production module also proves the stronger normalized band: for `a≥6` and every
  `d≤a+1`, `Position.value(Icc a (a+4),d)=win`. It takes the bottom counter when `d≤3` and the
  top counter otherwise, leaving one of the symbolic top-four losses. This is independent of the
  particular reachability construction.
- The independent longer scratch `HISTORICAL_TMP/CatchUpFiveConsecutive.lean`, SHA-256
  `84bd7ea57b350aa4f9948df6b1b7f9eec75f9530810a4329c7ca004b37068c0f`, proves the sharper
  `a≥3` value theorem directly by a four-reply minimax table. Production deliberately retains the
  shorter `a≥4` theorem because it covers every reachable trap above and reuses audited API.
- A warning-strict scratch additionally proves that deterministic all-least-counter play after
  opening `3` reaches this winning band in every `Icc 1 (4*k)`, `k≥3`, with deficit `2*k-4`.
  Artifact `HISTORICAL_TMP/CatchUpFiveBandMinimumPolicy_20260809.lean`, SHA-256
  `a1302790bd596798da57615094ebece086f1d514416b0bb96ce76feeba0441c4`; independent recurrence
  `HISTORICAL_TMP/CatchUpFiveBandMinimumPolicyAudit_20260809.py`, SHA-256
  `429faded77a83d357f38472ccf39eb18685d858f5ec61b2e71987ace6e3a7743`, passes through `k=40`.
  Neither player can force the top-five support against arbitrary play because the other can take
  `4*k` at its first opportunity, so this is a quantified policy obstruction rather than a root
  forcing strategy. The 165-line policy-specific trace remains scratch; the reusable band theorem
  is integrated.
- `lake --wfail build catch_up.CompletedTurnReflection catch_up.FiveConsecutiveTrap` passes 8,059
  jobs, the post-integration `CatchUpResearch` build passes 8,122, and a fresh full
  `lake --wfail build` passes all 9,010 jobs. Axiom audit
  `HISTORICAL_TMP/FiveConsecutiveTrapAxiomAudit_20260809.lean`, SHA-256
  `17f3ac0ae84adafa9965e7d04b2cfe7bbf02024e5dfd76e3bfef8d3be0cd32d1`, reports exactly
  `[propext, Classical.choice, Quot.sound]` for all five public theorems. A fresh read-only audit
  independently reconstructed the value and reachability proofs and found no semantic defect.
- A current literature search found only the original 2015 paper and von Stengel's computational
  progress report/conjecture, not a later proof or counterexample. The search is negative evidence,
  not a completeness claim about the literature.

## Bounded `N=15` all-opening extraction stop — 2026-08-09 12:49 EDT

- The guaranteed finite fallback attempted to extend the `N=12` shared player-one certificate to
  all fifteen post-opening roots. The exact probe computes `ExactSolver.solveGame 15`, applies
  `extractAllOpeningsUntil (smallSafeTarget 8 15 .p1)`, and then runs the independent checker.
- Exact command: `/usr/bin/time -l lake env lean HISTORICAL_TMP/N15ExtractionProbe.lean`.
  It was interrupted at the preregistered boundary after 1,139.50 seconds wall time, with no Lean
  output, node count, or checker result. Thus the result is pipeline noncompletion, not a checker
  failure and not evidence against the all-opening statement. Sandbox denial of `sysctl`, `ps`, and
  `pgrep` prevented a peak-RSS measurement.
- No solver optimization, second run, repository edit, or `N=16` computation was attempted.
  Probe `HISTORICAL_TMP/N15ExtractionProbe.lean`, SHA-256
  `69550412a8e434afb57cf09cfb4b1864525cea6313fcbf6c03952eff0cc65e59`; report
  `HISTORICAL_TMP/N15EveryOpeningExtractionReport_20260809.md`, SHA-256
  `be0cf309724c3176b2f43402b24b77a1abfa56ba203033ce46b317bd3694af42`.

## Rigid prefix-blocked dense endpoints — 2026-08-09 12:49 EDT

- The final two alternatives of `dense_loss_forces_upper_residual_or_small_prefix_blocked_loss`
  become exact tail shapes under the original at-most-three-hole hypothesis. Warning-strict Lean
  proves the deficit-two child is `Position(Icc 3 N \ {d-2,d},2)` and the deficit-one child is
  `Position(Icc 3 N \ {d-2,d-1,d},1)`. The first alternative similarly has at most one optional
  additional hole in `Position(Icc 2 N \ {d-1,d,h},1)`.
- Lean artifact `HISTORICAL_TMP/PrefixBlockedDenseEndpointShapes_20260809.lean`, 128 lines / 4,747
  bytes, SHA-256 `3f4e2098672b388b71d0d66e826c5d9d8ddb5b6ecc2b0d0b547acbbaae29bf5f`.
  Both public theorem audits are exactly `[propext, Classical.choice, Quot.sound]`.
- Exact independent recurrence found zero losses in every parity-compatible member of all three
  families for each `N=12,…,22`; a separately written Python evaluator agrees through `N=18`.
  C++ source SHA-256 `da503e5cb02ef36a6ea47158ff58520cbce5eaebbe490c50aef8ac3d09ea6cc5`;
  Python source SHA-256 `4a3a2e0e2225e456ba76236f0b46388b83d57f014a784c3368722f6d9e3827e2`.
  The `N=12` sanitizer run was clean.
- Parity alone is insufficient: the first sparse even deficit-one loss is
  `Position({4,7,9,10,12,15},1)`, of effective total 58. Through ambient endpoint 22 every such
  loss has at least nine anchored holes, versus four or five here, but this remains computational
  evidence rather than the required counting theorem.
- Full report `HISTORICAL_TMP/PrefixBlockedDenseEndpointsReport_20260809.md`, SHA-256
  `1cdd7fb1e2d74fac238b42ecd19c698fb13c5c7adbf31eb4b122faee997e24e0`.
  Route verdict: retain the rigid shapes; do not grow another hole grammar. Reopen only with a direct
  dense-tail response invariant or a counting lemma forcing more than five holes in any even
  deficit-one loss.

## Prefix parity elimination and production integration — 2026-08-09 13:00 EDT

- Added `scripts/catch_up/PrefixBlockedDenseEndpoints.lean`, now 352 lines / 14,464 bytes, SHA-256
  `b49183ecbff0002af6ebe30961bc89658c54591103c84d53a62259643dc48d4a`. The four theorem bodies from
  the independently audited production-style scratch remain unchanged; the root then added a
  warning-strict branch-shape theorem and the synthesis API. The module has a 2026 header, documentation, and
  `category API`/`AMS 91` annotations.
- The module proves the exact two rigid child shapes. More importantly, it eliminates the entire
  deficit-two alternative from the even-triangular target: its parent holes are exactly
  `{1,2,d}`, so `sum(Icc 1 N)=sum(remaining)+d+3`. Consequently an even interval total makes
  `d+sum(remaining)` odd. This is a genuine branch closure, not a bounded computation.
- In the remaining deficit-one alternative the parent holes are exactly `{2,d-1,d}` and the child
  is `Position(Icc 3 N \ {d-2,d-1,d},1)`. If the interval and effective totals are even, Lean
  proves `Odd d`, halving the residual parameter range.
- In the first deficit-one alternative, whose forced parent holes are `{1,d}`, Lean now proves
  that even interval and effective totals force a third hole `h`; moreover `h` is odd and the
  child is exactly `Position(Icc 2 N \ {d-1,d,h},1)`. This removes the misleading optional-hole
  case and exposes the exact remaining two-parameter dense family.
- A final synthesis theorem now classifies every hypothetical even dense loss of deficit at least
  seven: either an exact block of at most two counters produces a strictly larger residual winning
  opening `w>d`, or the loss descends to the explicit odd-`h` first family above, or it descends to
  the explicit odd-`d` consecutive-triple family. The parity-impossible deficit-two branch is absent
  from the conclusion.
- `lake --wfail build catch_up.PrefixBlockedDenseEndpoints` passes all 8,058 jobs. The independent
  audit checked every finite-set and natural-subtraction boundary of the original four lemmas and
  separately audited every parity, exact-shape, and branch-rewrite step in the root-added synthesis.
  A fresh root warning-strict audit for all six current public theorems reports only
  `[propext, Classical.choice, Quot.sound]`; audit SHA-256
  `5deeae41f6f4175f74fdc6d0d9c4914deec43c1fdbd339a67f683bb52e010f38`. There is no placeholder or
  unsafe declaration. The post-integration `CatchUpResearch` build passes all 8,124 jobs.

## Held-out `8 → 12` product certificate — 2026-08-09 13:00 EDT

- The preregistered held-out gate succeeded for protected player two and old opening one:
  `lake env lean --run scripts/catch_up/SimulationBasinMain.lean --check-four-lift-old-root 3 8 1 p2`.
  It searched 23,546 product labels, selected 1,190 DAG nodes, and returned
  `combinedCheck=true` and `rootMatches=true` in 9.90 seconds.
- Added the emitted literal
  `scripts/catch_up/FourLiftN8P2Old1Certificate_20260809.lean`, 1,245 lines / 317,936 bytes,
  SHA-256 `5f97dee3ea08fb9debd01d3e7c119205eeeb28d2b274d042d3ba2bad3c4884cf`. Two independent emissions
  were byte-identical. A scoped `set_option maxRecDepth 10000 in` is needed only around the large
  literal DAG definition; the default recursion depth was insufficient.
- Warning-strict compilation passes. The checked theorem is
  `CatchUpSearch.FourLiftN8P2Old1Certificate.old_opening_basin :
  ExplicitFourLiftOldOpeningBasin 8 .p2 1`. Generic checker soundness and the root-ghost bridge use
  only the standard axioms. Literal evaluation of the certificate and root uses `native_decide`,
  so those proof closures additionally expose `Lean.ofReduceBool` and `Lean.trustCompiler`; this
  trust boundary is explicit and matches the earlier finite certificate modules.
- Emission report `HISTORICAL_TMP/FourLiftN8P2Old1Certificate_20260809_REPORT.md`, SHA-256
  `d6a29c954c1854ca22d9de185eb6481c9d8bd51bc78e3dccf6ab7ce115c0fe33`; validated integration
  patch SHA-256 `f712fa993d6dbc552f15d1b77c5f3a4a8693f60f413f3fd7caaa93d81d8f767f`.
  A fresh unrelated read-only audit reran the exact gate, reproduced all counts and the raw emission
  hash, checked that the scoped recursion-depth line is the only raw/production difference, traced
  both roots through the generic soundness theorem, and found no blocker. Scope remains deliberately
  narrow: this proves one protected-player-two unchanged-opening basin, not the whole `8 → 12`
  induction step.

## Fixed-low response obstruction for the surviving prefix family — 2026-08-09 13:13 EDT

- For the surviving consecutive-triple endpoint
  `P(N,d)=Position(Icc 3 N \ {d-2,d-1,d},1)`, warning-strict Lean proves the exact identity
  `P.afterPick 3 = Position(Icc 4 N \ {d-2,d-1,d},2)` and the corresponding negated move-outcome
  formula. Scratch `HISTORICAL_TMP/PrefixCMoveThreeShape_20260809.lean`, SHA-256
  `4e1105fcbd4f98fe5cc25699f80cf5ae19bd391020d85b047aa514f8fb446a72`; all three theorem audits
  are standard `[propext, Classical.choice, Quot.sound]`.
- The previously reported uniform drawing move `3` is false at the first allowed size. At
  `(N,d)=(12,9)`, `P=Position({3,4,5,6,10,11,12},1)` draws, but move `3` loses because its child
  `Position({4,5,6,10,11,12},2)` is a win. The exact root move profile is
  `3:L,4:D,5:D,6:D,10:D,11:L,12:D`; the child wins via `4` or `5`.
- No single fixed move among `3,4,5` is a uniform legal nonloss policy through the intended target
  sizes up to 22: move `3` first loses at `(12,9)`, move `4` first loses at `(12,7)`, and move `5`
  is already illegal at `(12,7)`. Independent Python agrees with the C++ recurrence. Report
  `HISTORICAL_TMP/PrefixCFixedLowMoveReport_20260809.md`, SHA-256
  `f534765e1b1752dfbd71520310a42eb39bdb903fe6ca7fc032d372fa06028a03`; C++ source SHA-256
  `6c45b38b0e09fd41d5026b575deabe20a9b2cca0c997fb1fea30421ce8b08b9a`; independent Python
  SHA-256 `cd575fa6c3c2d9612281745bcde6ed98ccdfba4023286d558a14c74283498136`.
- This does not refute nonloss of the family—the minimized state itself draws—but it decisively
  stops a fixed-low-counter proof. The empirical branch rule `d=7 -> 3`, `d>=9 -> 5` is not being
  promoted; doing so would reopen the same response grammar.

## Six-hole upper-gap counting reduction and stop — 2026-08-09 13:23 EDT

- After an upper witness from the three-hole parent, the losing post-opening child has at most six
  anchored holes. Let `p` be its greatest remaining counter below the missing deficit `d`, and put
  `r=d-p`. Warning-strict Lean proves that any positive exact block of sum `d` and maximum `p`
  forces the next residual winning opening strictly above `d`.
- If `r<p`, the missing suffix `(p,d]` already contributes `r` holes. Blocking the canonical
  pairwise-disjoint exact-`r` blocks `{r},{1,r-1},{2,r-2},...` contributes another
  `ceil(r/2)` low holes, so the exact combinatorial bound is
  `holes >= r + ceil(r/2)`. The Lean artifact proves the sharp sufficient consequence directly:
  with at most six holes, either `r≤4` or another exact block forces a strictly larger winner.
  If the disjointness boundary fails (`r≥p`), the suffix count forces `d≤12`.
- Scratch `HISTORICAL_TMP/DenseUpperGapCounting_20260809.lean`, 268 lines / 11,109 bytes, SHA-256
  `4b24f99f69e9bcb33fe6bce02a8e9ae8877dd27f05da081c8ddef2ce194d8cf8`; warning-strict and no
  placeholders. Axiom audit SHA-256
  `b74c4b9ae8a76c91dc065f24727ce2f809eae87b5d7c5df953a393d0286f08bf` reports only
  `[propext, Classical.choice, Quot.sound]`.
- An independent adversarial audit passed all five formal theorem statements, including exact
  maxima, disjointness, truncated subtraction, winner perspective, and the `d≤12` overlap branch.
  It also identified the exact production boundary: the combined trichotomy is not yet one Lean
  theorem, and the first-child six-hole bound plus existence of a greatest lower counter remain
  prose. The scratch therefore has not been copied into production unchanged.
- The count does not close the chain. Each tight gap `r=1,2,3,4` has an explicit
  parity-compatible decomposition into original holes, the parent exact block, and the opened
  residual winner. These are geometric route obstructions, not loss counterexamples. A cheap
  recurrence run reported zero losses among 63 canonical child roots through `N=18` (27 draws,
  36 wins), but its source/reproduction command was not archived with the report, so those counts
  are explicitly non-bankable evidence.
  Full report `HISTORICAL_TMP/DenseUpperGapCountingReport_20260809.md`, SHA-256
  `88fde644101ba8d875750f39d2e2db6909ce17583854305ede474dbfb00642f8`.
- Route verdict: preserve the one-step reduction, but stop parity/counting iteration. Reopen only
  with a direct semantic nonloss theorem for the four displayed small-gap child families or a
  genuinely different well-founded invariant. An unrelated agent is auditing the Lean hypotheses
  and deciding the minimal production tranche.

## Symmetric every-opening four-lift transfer — 2026-08-09 13:28 EDT

- Added `scripts/catch_up/EveryOpeningFourLiftTransfer.lean`, 98 lines / 4,477 bytes, SHA-256
  `3cb13c5bb32b50263caa8654e0b3c2dddddf560ccda0bf18bd5f22f5f6f301e8`.
- Lean proves the exact perspective bridge for every finite set and opening:
  `(afterOpening S x).value = draw` iff both fixed players can avoid loss from the corresponding
  absolute post-opening game. Since player two owns that node, player-one safety excludes normalized
  `win`, player-two safety excludes normalized `loss`, and the conjunction is exactly `draw`.
- The main theorem assumes `EveryOpeningDraw (Icc 1 N)`, `4≤N`, and old- plus new-opening transfer
  predicates for both fixed players. It partitions every target opening in `Icc 1 (N+4)` at `N` and
  proves `EveryOpeningDraw (Icc 1 (N+4))`. In the new branch the existing helper proves
  `k=x-N∈Icc 1 4`, then uses `4≤N` to obtain the matching small opening and `x=N+k`; there is no
  natural-subtraction or endpoint gap.
- A corollary accepts the four explicit basin families directly. This is a conditional structural
  theorem: it does not assert that those families exist, and the currently preserved held-out
  `8→12` literal supplies only one of the required old player-two roots.
- `lake --wfail build catch_up.EveryOpeningFourLiftTransfer` passes all 8,069 jobs. A fresh root
  warning-strict axiom audit reports only `[propext, Classical.choice, Quot.sound]`; audit SHA-256
  `c095949365e57f56341c5a395f93fcdc2b81dd6e1fa32df8cf0861c2e75240ff`.
- A separate read-only adversarial audit reproduced warning-strict compilation, checked every owner
  polarity and old/new quantifier, found imports non-cyclic and necessary, and ran
  `lake --wfail build CatchUpResearch` successfully with 8,125 jobs. Its independent audit source
  has SHA-256 `0def95b9cf6018837a98ca622e1a80729adb9cba029020b3a279ca50d6467118`.

## End-to-end dense upper-gap pipeline — 2026-08-09 13:59 EDT

- Added `scripts/catch_up/DenseUpperGapPipeline.lean`, 396 lines / 17,216 bytes, SHA-256
  `0e98bda322e7471b7989ba1c2b494886f13f67634edae6111995dc4eeddd4a9e`.
  It is byte-identical to the independently prepared production scratch
  `HISTORICAL_TMP/DenseUpperGapPipelineProduction_20260809.lean`.
- The public theorem `strict_upper_winner_of_exact_block_at_greatest_lower` packages the exact
  semantic transfer: in a losing position with missing deficit `d`, an exact positive block whose
  maximum is the greatest remaining counter below `d` forces the tied residual's winning opening
  strictly above `d`.
- The main theorem `dense_upper_residual_witness_to_greatest_lower_trichotomy` starts with an actual
  `DenseUpperResidualWitness` from a parent with at most three holes and `d≥7`. It retains the
  original exact block and residual winner, constructs the resulting losing child, proves that
  child is anchored in `Icc 1 N`, has its deficit missing, and has at most six holes, constructs the
  greatest remaining lower counter `p`, and proves one of:
  1. a new exact block forces another residual winning opening strictly above the new deficit;
  2. the greatest-lower gap is at most four; or
  3. the new deficit is at most twelve.
- This closes every formerly prose-only bridge in the one-step reduction. It does **not** close an
  induction: the next exact block can have cardinality three, whereas `DenseUpperResidualWitness`
  records cardinality at most two. The public documentation states this limitation explicitly.
- `lake --wfail build catch_up.DenseUpperGapPipeline` passes all 8,059 jobs. The root axiom audit
  `HISTORICAL_TMP/DenseUpperGapPipelineRootAudit_20260809.lean`, SHA-256 prefix `15ad918`, reports only
  `[propext, Classical.choice, Quot.sound]` for both public theorems. Independent warning-strict
  audits of the counting core and the bridge also pass; their source hashes are respectively
  `b74c4b9` and `12ebe7`, and the bridge report is
  `HISTORICAL_TMP/UpperGapPipelineReport_20260809.md`, SHA-256 prefix `972d727`.

## Proof-backed finite dense-three-hole checker — 2026-08-09 13:59 EDT

- Added `scripts/catch_up/DenseThreeHoleFiniteChecker.lean`, 91 lines / 3,842 bytes, SHA-256
  `6b19e2a527dc1310c82f855a37f2df204dcff4e7e7bd1c8f421e689b3ec9c89e`.
  The executable checker enumerates exactly every support subset of `Icc 1 N` and every deficit in
  `range (N+1)`, filters the hole, catchability, and even-effective-total hypotheses, and invokes
  the proof-backed `CanAvoidLossClassifier` with the current player as fixed player one.
- The generic theorem `dense_three_hole_nonloss_of_check_eq_true` proves that Boolean acceptance
  implies the full quantified `DenseThreeHoleNonloss N`. The nested Boolean folds are connected to
  every enumerated support/deficit by `Finset.fold_op_rel_iff_and`; classifier soundness then gives
  normalized `value ≠ loss` with the correct current-player perspective.
- Native-checked category-test theorems establish the complete invariant at `N=9` and `N=10`, not
  merely selected roots. `lake --wfail build catch_up.DenseThreeHoleFiniteChecker` passes all 8,056
  jobs; a fresh warning-strict independent elaboration recomputed both checks and passed in 302.62
  seconds.
- Independent audit PASS: powerset/range coverage, implication polarity, both fold extractions, and
  the fixed-owner perspective are all exact. The generic soundness theorem has only
  `[propext, Classical.choice, Quot.sound]`; the two concrete test theorems additionally and
  explicitly use `[Lean.ofReduceBool, Lean.trustCompiler]`. Independent axiom audit
  `HISTORICAL_TMP/DenseThreeHoleFiniteCheckerAxiomAudit_20260809.lean`, SHA-256
  `a5cf1da9e68e6f6dfa67b2d991fe45d36b2d3954ca6a035961770d6a4d2483e3`; fresh root audit SHA-256
  `9d78c0b0e5cba9c31d7178cc8ce919981a4ff337a2a210ac4d71f96c480fe8f0` agrees.
- An isolated `N=11` proof probe is running under a hard 45-minute cap. It is deliberately outside
  the production module while runtime and certificate alternatives are assessed; noncompletion at
  the cap will not be interpreted as mathematical failure.

## Canonical small-gap children and exact scalar descent — 2026-08-09 14:18 EDT

- Added `scripts/catch_up/SmallGapChildFamilies.lean`, 154 lines / 6,221 bytes, SHA-256
  `72e4df979c56c529ef859a6a7b3112080ccde790c5b43bbeb23f8f2cdb8e2aa8`. It defines the four
  parity-compatible gap-one through gap-four residual families and proves availability and exact
  `afterPick` identities for the fixed continuing counters `2,1,1,2` respectively. Two generic
  lemmas isolate the honest semantic boundary: a nonlosing child under a legal continuing pick makes
  the parent nonlosing, and every legal pick strictly decreases remaining-cardinality.
- This module is intentionally conditional. It neither proves the displayed roots nonlosing nor
  classifies every arbitrary small-gap child. An independent adversarial audit passed all ten
  theorem statements and reproduced two independent recurrence runs: 124 parity-compatible roots
  through `N=20` had zero losses and zero fixed-candidate failures, while relaxed parity hypotheses
  have concrete losses. Arbitrary later moves create extra holes, so the first-pick identities do
  not close an invariant.
- `lake --wfail build catch_up.SmallGapChildFamilies` passes all 8,052 jobs. Root axiom audit
  `HISTORICAL_TMP/SmallGapChildFamiliesRootAudit_20260809.lean`, SHA-256
  `3b9c2af70c32afdcbac41035abbb7e246a2cffbca47860dc189e222172fe4644`, reports only
  `[propext, Classical.choice, Quot.sound]` for all ten theorems. The independently prepared source
  and full audit have hashes `d40adac` and `c60bf153` before the root's theorem-name cleanup.
- Added `scripts/catch_up/EffectiveTotalDescent.lean`, SHA-256
  `f6a27227999487cd332a6e3d3060be2482f550f29657766571e52621896870ea`. If an exact block of sum
  `d` is deleted and a residual opening `w` is then removed, Lean proves the subtraction-free
  identity `E' + 2d = E`, the exact natural-subtraction form `E'=E-2d`, strict descent for `d>0`,
  and child catchability iff `2d+2w≤E`. Hence a catchable strict step `w>d` requires `E≥4d+2`.
- Independent scalar audit PASS: the production target builds all 8,052 jobs and all five theorems
  use only standard axioms; production audit SHA-256
  `1f8b7ee6095193c05f7a62735afbd4acf90009025308eda8d6c734586749a681`.
  Descent does not force a contradiction. The formal six-hole even-loss example
  `Position({2,4,5,7,11},9)` with exact block `{2,7}` and strict residual opening `11` descends
  `E:38→20` to terminal loss `Position({4,5},11)` while its anchored hole count grows from six to
  nine. Report `HISTORICAL_TMP/StrictEffectiveTotalDescentReport_20260809.md`, SHA-256
  `b1bbba5c9f0f66003e17217398764801d6e9e155140f04dcfbb7f48beb0e8e6a`. The example blocks
  unconditional six-hole iteration; no qualifying dense predecessor for it was found, so it does
  not refute a narrower generated-subclass theorem.

## Shared dense-root certificate and `N=11` invariant — 2026-08-09 14:18 EDT

- Added `scripts/catch_up/DenseThreeHoleCertificateChecker.lean`, 90 lines / 4,265 bytes, SHA-256
  `e6bdfc7b12ceadbcee301f71e78c4a83f87dde3702d62523650ac976c506ffe7`. It extends the independent
  partial-strategy checker with exact powerset/range coverage of every root quantified by
  `DenseThreeHoleNonloss`. One DAG may therefore share descendants among all roots. The module does
  not import the exact solver or extractor.
- Its soundness theorem requires an external proof that the target predicate is sound, checks
  metadata `gameSize=N` and owner `p1`, independently checks every local strategy obligation, and
  proves formal `ContainsPosition` for every qualifying support/deficit. Partial-DAG soundness
  applies to every contained node, not only the distinguished root, so each current-player root is
  nonlosing. Independent audit PASS at exact SHA: no metadata, Boolean associativity, coverage, or
  perspective mismatch. The generic theorem uses only `[propext, Classical.choice, Quot.sound]`;
  audit `HISTORICAL_TMP/DenseThreeHoleCertificateCheckerAxiomAudit_20260809.lean`, SHA-256
  `ebeff69e07281af1922eef379a3be4a7dc569a0a490c9f02e525c9b9a7db9bc2`.
- Added `scripts/catch_up/DenseThreeHoleN11Certificate.lean`, 89 lines / 3,496 bytes, SHA-256
  `3814d5ed987f5b063db860c9bc8e69a610b9d59dfb8fab6d5372551144c96f03`. The untrusted generator
  enumerates 1,392 qualifying endpoint-eleven roots, solves them in one transposition table, and
  extracts one shared partial strategy DAG with 3,154 nodes and proof-backed small-state leaves.
  The independent checker accepts both the DAG and exact formal coverage of all 1,392 roots.
- The resulting theorem `dense_three_hole_nonloss_eleven : DenseThreeHoleNonloss 11` is stronger
  than the already known interval-root draw. The standalone shared gate reported
  `partial=true`, `coverage=true`, `combined=true` in 198.46 seconds; the production warning-strict
  target build passed all 8,067 jobs in 101.16 seconds. By contrast, the original direct finite
  classifier was interrupted after 1,180.60 seconds without output.
- Root axiom audit `HISTORICAL_TMP/DenseThreeHoleN11CertificateRootAudit_20260809.lean`, SHA-256
  `92e3e9c1396bd65976ed40b0123dc0ef8aa6fd281880ec7ac765fbbc48c78a26`, reports the explicit
  finite-certificate boundary `[Lean.ofReduceBool, Lean.trustCompiler]` in addition to the standard
  axioms for both the Boolean check theorem and final invariant. Independent production audit PASS:
  there are exactly 232 supports and six parity-compatible deficits per support, hence 1,392 roots;
  the solver produced 22,902 states and the extracted independently checked DAG has 3,154 nodes.
  Audit runner `HISTORICAL_TMP/DenseThreeHoleN11CountAudit_20260809.lean`, SHA-256
  `4c1f7b8ea3f3cc545dde730578702ae3a84fbdb282248b3260b3d8163fd9d800`, confirms root uniqueness,
  metadata, partial validity, exact coverage, and the combined check.

## Dense transfer opening and exact-block dominance — 2026-08-09 14:34 EDT

- The prospective one-step transfer from `DenseThreeHoleNonloss N` to endpoint `N+1` splits into
  two independent semantic gates. If the new maximum is absent, only a maximum-deficit boundary
  with at most two lower holes remains. If the new maximum is present, the hard gate is whether
  adjoining an even maximum preserves nonloss; exact recurrence found no failure for odd
  `N=9,11,13`, but this is not value preservation and has no proof yet.
- Added the generic theorem
  `Position.value_ne_loss_of_exact_sum_block_dominates` to
  `scripts/catch_up/ExactSumLossObstruction.lean`: a positive exact-deficit block whose maximum
  dominates every residual counter rules out loss. This is an immediate rigorous corollary of the
  unique residual winning-opening obstruction and is the right endpoint tool whenever a dense
  boundary admits an exact block containing its maximum. The warning-strict target build passed all
  8,056 jobs; the theorem uses only `[propext, Classical.choice, Quot.sound]`. Axiom audit
  `HISTORICAL_TMP/ExactSumBlockDominatesAudit_20260809.lean`, SHA-256
  `4ee7c0822f6c6f414861a48e6b8149983f613e9c4e974953f8b219447d605fb4`.
- The missing-new-top boundary is now closed from `DenseThreeHoleNonloss N`, with no parity class
  restriction beyond the position's effective evenness. Among `N,N-1,N-2` one counter remains;
  taking it continues to a child with deficit at most three, at most three lower holes, preserved
  catchability, and effective total reduced by twice the pick. The preceding dense invariant rules
  out child loss and therefore parent loss. Warning-strict Lean scratch
  `HISTORICAL_TMP/DenseTopAbsentBoundary_20260809.lean`, SHA-256
  `307e7355b6f3221ef244ded7f9dd751eb41a16ba186ecca185aaf54e7cac9b64`; theorem
  `top_absent_dense_two_hole_value_ne_loss` uses only standard axioms and requires merely `4≤N`.
- Integrated the full conditional reduction as `scripts/catch_up/DenseHoleSuccessor.lean`, 356 lines /
  15,273 bytes, SHA-256
  `8b4479c55d2ed1ae86bd9607319deaa59240b0a75ae003c9f6746e8d390b9372`. Its predicate
  `AddTopPreservesDenseThreeHoleNonloss N` says precisely that adjoining `N+1` preserves nonloss
  for catchable, even, lower three-hole states already known nonlosing. For `4≤N` and even `N+1`,
  this premise together with `DenseThreeHoleNonloss N` proves `DenseThreeHoleNonloss (N+1)`.
  Every other branch is discharged: missing top below the boundary by `H_N`, missing top at the
  boundary by the theorem above, present top at maximum deficit by max-deficit stealing, and a
  present top over an uncatchable lower state by taking every counter in one completed turn.
  The reverse implication is also formal: full `H_(N+1)` implies the add-top predicate without
  using its lower-nonloss antecedent. Consequently, under `H_N`, the module proves an exact iff
  between `H_(N+1)` and the add-top predicate. Warning-strict target build passed all 8,059 jobs;
  all four public theorem audits are exactly
  `[propext, Classical.choice, Quot.sound]`. Root audit
  `HISTORICAL_TMP/DenseHoleSuccessorRootAudit_20260809.lean`, SHA-256
  `9091a01f4a8065ca4a49711e596c121757fc5ed49c2ff3ec477711ff910d50d7`.
- Independent integrated and post-equivalence audit PASS at the final source SHA, including the
  interval-hole equalities, parity witnesses, completed-turn perspective, imports, and hygiene.
  Final equivalence audit `HISTORICAL_TMP/DenseHoleSuccessorEquivalenceAudit_20260809.lean`, SHA-256
  `9bc1934b5276f5de6d3c217a552a3e3cb3eecfb719ab247996fdb7be7a7dfe8a`.
  Strength calibration is important: the premise is exactly the unresolved top-present slice,
  not a disguised consequence of `H_N`; the real progress is closure of every complementary case.
- A shared direct `H_12` certificate probe was deliberately stopped after 359.50 seconds with no
  output. This is recorded as noncompletion, not checker failure; that failed direct probe added no
  certificate. The later catching-window certificate below supersedes it and does prove `H_12`.
  Preserved probe `HISTORICAL_TMP/DenseThreeHoleN12CertificateProbe_20260809.lean`, SHA-256
  `7138308e03791afb6b3e8a3d149ba7de7477b62c0f7955a8b10219bc38a32673` (59 lines / 1,988 bytes).

## Five-counter add-top window and quantified `H_12` invariant — 2026-08-09 15:57 EDT

- Added `scripts/catch_up/DenseAddTopWindow.lean`, 251 lines / 10,915 bytes, SHA-256
  `31d0c16abb28815bdbe22c46c147e2ed261a93f8e5bbd7028fe20cca3802ae05`. Its predicate
  `DenseAddTopWindowSafe N` asks for a catching singleton `x` in the exact five-counter window
  `d ≤ x ≤ d+4` whose child is not winning, for every lower support and deficit quantified by
  `DenseThreeHoleNonloss N`. The module proves exact child bookkeeping: after adjoining `N+1`,
  such a move has deficit at most four, support in `Icc 1 (N+1)`, effective parity preserved, and
  at most four holes. It also defines `SmallGapFourHoleNonwin M` and proves that, for `4≤N` and
  even `N+1`, this small-gap predicate implies the catching window, add-top preservation, and hence
  the successor implication `DenseThreeHoleNonloss N → DenseThreeHoleNonloss (N+1)`.
- Added `scripts/catch_up/DenseAddTopWindowCertificateChecker.lean`, 107 lines / 5,230 bytes,
  SHA-256 `f46b0961e2e5e7ae3d9251f82ce6ab4597c41bd59207ad5bc73bb399315b875d`.
  The checker independently enumerates the five candidates with `List.range 5`, verifies the
  partial-strategy DAG and its metadata (`gameSize=N+1`, owner `p1`), and proves exact coverage of
  every qualifying lower support/deficit. Its soundness theorem converts a contained catching
  child's fixed-owner `CanAvoidLoss p1` proof into the normalized assertion that the child value is
  not `win`; the mover/perspective switch is therefore checked rather than assumed. The generic
  checker and all six generic window theorems use only
  `[propext, Classical.choice, Quot.sound]`. Temp checker report
  `HISTORICAL_TMP/DenseAddTopWindowCertificateCheckerReport_20260809.md`, SHA-256
  `819a40f2c217191715dcb7cfc11a2bdb0e0ce4c94aa0bffe30ba391b07c09b04`.
- Added the deterministic literal certificate
  `scripts/catch_up/DenseAddTopWindowN11Certificate.lean`, 2,420 lines / 100,373 bytes, SHA-256
  `7eaa07df83b22781604ff53fcf475d10287f692490298b4207df0877c5205890`. It covers exactly the
  same 1,392 lower endpoint-eleven roots as `DenseThreeHoleNonloss 11`, selects the first safe
  catching child in `d..d+4`, and shares their player-one strategies in a 2,350-node DAG:
  1,698 proof-backed target or terminal leaves, 455 owner branches, and 197 opponent branches.
  The target is `smallSafeTarget 8 12 p1`. The generator
  `HISTORICAL_TMP/generate_dense_add_top_window_certificate_20260809.py`, SHA-256
  `f2a7b00ad64e36f9f81b284c12524a1bb396dc860d2ec48849e04c9af15cdae1`, now defaults to the
  exact target cutoff eight used by the literal and reproduces the integrated file byte-for-byte
  without an environment override. The sole scoped elaboration accommodation is
  `set_option maxRecDepth 30000 in` on the literal definition.
- The checked theorem `dense_add_top_window_safe_eleven : DenseAddTopWindowSafe 11`, composed with
  `dense_three_hole_nonloss_eleven` and the successor theorem, yields
  `dense_three_hole_nonloss_twelve : DenseThreeHoleNonloss 12`. This is strictly stronger than an
  interval-root or every-opening draw computation: it rules out loss at every even-effective,
  catchable, deficit-at-most-12 support with at most three holes in `Icc 1 12`. The concrete target
  build passed all 8,075 jobs in 407 seconds; the aggregate research build then passed all 8,135
  jobs. Axiom audit
  `HISTORICAL_TMP/DenseAddTopWindowN11CertificateAxiomAudit_20260809.lean`, SHA-256
  `d32bc2052c9f568bfe915bc9d2014eceb23a7514278ddfa9086076713f3f26ea`, reports exactly the
  disclosed finite-computation boundary
  `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]` for the Boolean
  check, the window theorem, and final `H_12` theorem.
- A fresh adversarial audit independently reconstructed all 232 supports and six parity-compatible
  deficits per support, checked coverage `1392/1392`, all 2,280 certificate edges, and every one of
  the 2,350 sorted distinct nodes. It found 1,990 covered witness occurrences but only 592 distinct
  selected children; every selected child independently evaluates to draw. Six malformed-certificate
  mutations (including wrong metadata, missing roots, duplicates, and false targets) were rejected.
  The player polarity and final theorem type were read back exactly. Full report
  `HISTORICAL_TMP/REPORT.md`, SHA-256
  `01e7540c073c77d309310b267f79b1327d4b91dbda8576daaa8c29a544c84544`.
- Independent recurrence found zero window failures among 69,510 qualifying roots at odd lower
  endpoints `N=11,13,15,17,19,21,23`; width four is sharp at `N=11,15,19,23`, for example at
  holes `{1,2,3}` and deficit zero. Removing either the three-hole or even-parity restrictions has
  exact failures. The resulting parametric target is now precise: prove
  `SmallGapFourHoleNonwin M` for even `M≥16`. Exact classification found wins at `M=12` and `M=14`
  but none at `M=16,18,20,22,24`, so the threshold is substantive rather than cosmetic. Audit
  report `HISTORICAL_TMP/REPORT.md`, SHA-256
  `8718a796e1200ad6fc821c85059fa79cc5f829051763586f54d7f116603cb3f2`.
- The alternate universal add-top macro-duality route is stopped. Exact Lean A/B local recursion is
  valid, but its complementary bridge fails already at empty and singleton descendants and along
  legal descendants of qualifying dense roots; `AddTopPreservesDenseThreeHoleNonloss 5` itself is
  false. Consequently the window theorem's existential, threshold-sensitive safe catch is not
  replaceable by an every-descendant or every-common-turn induction. Report
  `HISTORICAL_TMP/AddTopMacroDiamondReport_20260809.md` (SHA-256 prefix `97d0577f`) and warning-strict
  scratch `HISTORICAL_TMP/AddTopMacroDiamond_20260809.lean` (SHA-256 prefix `2b77c1d9`).

## Exact completed-turn compression of the small-gap target — 2026-08-09 16:38 EDT

- Added `scripts/catch_up/SmallGapTurnEndpoint.lean`, 413 lines / 19,989 bytes, SHA-256
  `26cdda492c1542aaafa7f33c2741f36424a9cec478884295fd09ddbb7a15feb5`.
  It defines `SmallGapTurnEndpointShape M` as the union of three precise endpoint strata and
  `SmallGapTurnEndpointNonloss M` as their semantic nonloss assertion. For any legal completed
  turn from a source with at most four holes, deficit at most four, anchored support, and even
  effective total, the module proves that the endpoint remains supported, catchable, and even,
  has deficit at most `M`, and lies in one of:
  1. at most five holes with a missing `y` satisfying `e ≤ y ≤ e+4`;
  2. at most six holes with a missing `y` satisfying `e < y ≤ e+4`;
  3. at most seven holes with `{1,2,e+1}` missing.
  The third case is not guessed from data: positivity and the half-open legality inequality force
  the two preparation counters to be exactly `{1,2}`, the source deficit to be four, and the
  consumed final counter to equal `e+1`. The endpoint is automatically catchable for `M≥16`
  because a nine-counter top band and seven-hole bound leave two counters whose sum is at least
  `M`. The public identity `TurnSet.endpoint_holes_eq` additionally proves that the endpoint hole
  set is exactly the old hole set union the chosen turn counters, not merely bounded by that union.
- The formal minimax flattening then proves
  `SmallGapTurnEndpointNonloss M → SmallGapFourHoleNonwin M` for `M≥16`: a source is nonwinning
  exactly when every legal completed-turn endpoint is nonlosing. Empty and uncatchable sources are
  discharged as terminal nonwins. Target build passed all 8,061 jobs. Independent adversarial
  audit checked the nonexclusive trichotomy wording, all `d=0..4` Nat boundaries, perspective,
  hole bounds, parity, catchability, and terminal branches; PASS with no blocker. All three public
  theorem audits are exactly `[propext, Classical.choice, Quot.sound]`; local root audit
  `HISTORICAL_TMP/SmallGapTurnEndpointRootAudit_20260809.lean`, SHA-256
  `06e94b5aa3ca2f2443b1f38461098120640abd0e22c1c615d40df579ac21c0d2`.
- A second, independently written warning-strict normal-form proof reached the same three strata
  and conditional reduction without using the production proof. Preserved proof
  `HISTORICAL_TMP/SmallGapEndpointNormalForm.lean`, SHA-256
  `e5bc8e97b45c4c20a98805fd01c715bf3cb4a153d4dbc9014e324912f17d7f48`.
- Independent exact recurrence enumerated the full three-stratum family. It has a sharp last
  observed loss at `M=15`, namely `Position({8,...,15},6)`, but zero losses at every tested even
  maximum `M=16,18,20,22,24`: respectively 105,756; 235,988; 482,960; 915,212; and 1,637,156
  states. Every one of the 6,303/10,106/15,508/22,750/32,405 original small-gap roots is exactly
  draw at those maxima, and every legal completed-turn endpoint is nonloss. The broader
  seven-hole/near-gap condition is false already at `M=16`, so the exact strata are a real
  compression rather than decorative bounds. Sanitizer-backed report
  `HISTORICAL_TMP/SmallGapThreeStratumAuditReport_20260809.md`, SHA-256
  `fe9c4d9e6d55f84e648c2c4e41e997b546db00e764c86e4d82225a065343c549`; exact recurrence source
  `HISTORICAL_TMP/small_gap_response_patterns_20260809.cpp`, SHA-256
  `330676cb89c425be3b2500d4ea3577bb1a0243f8e5bb59f8a066b63efd7fcc3b`.
- Strategic calibration remains explicit. At `M=16`, a menu consisting of the first five
  available counters is necessary and sufficient one ply across all three strata; at `M=18`, the
  first two suffice; at `M=20,22,24`, the minimum counter is always safe. Repeating those local
  rules is not yet a proof: restricted-policy closure leaves the endpoint class and can fail.
  Therefore the new Lean theorem is banked as a rigorous reduction, while the parametric
  `SmallGapTurnEndpointNonloss M` assertion remains the substantive open gate.
- Added the reusable proof-backed finite interface
  `scripts/catch_up/SmallGapFourHoleCertificateChecker.lean`, SHA-256
  `07f764a0230b00c673f8ec04f078b89517644c5d6d7bf48edc471031eccca66f`. It enumerates exactly
  every support in `Icc 1 M`, every deficit at most four, the four-hole condition, and effective
  parity; metadata pins the protected owner to player two while roots have player one to move.
  Hence a checked partial DAG yields precisely `SmallGapFourHoleNonwin M`, with no accidental
  catchability premise. Independent audit checked coverage, owner/current polarity, fail-closed
  metadata and targets, and imports; PASS. The generic soundness theorem uses only
  `[propext, Classical.choice, Quot.sound]`; audit
  `HISTORICAL_TMP/SmallGapFourHoleCertificateCheckerAxiomAudit_20260809.lean`, SHA-256
  `71b8f5f31cfdeb5dc56a9b12d37cb92246e68921c69bc6cd2cdbae68ef75a0f8`.

## Shifted-tail reduction of the exact endpoint strata — 2026-08-09 17:25 EDT

- Added `scripts/catch_up/SmallGapShiftedTailPackage.lean`, 249 lines / 11,429 bytes, SHA-256
  `b113b0b333e4d6fae21b79218fe52e3712a597bdee656536b00a319f523db5f4`. It isolates three
  semantic assertions:
  `ShiftedUpperTailContinuationNonloss M 7 1`,
  `ShiftedUpperTailCatchNonwin M 6 1`, and
  `ShiftedUpperTailCatchNonwin M 7 3`. The hole score is the number of deleted counters above a
  removed minimum `m`, plus the forced missing prefix of length `m-1`. Continuation states require
  a positive, catchable deficit at most `M-m`; catching states require only deficit at most `m`,
  because an uncatchable state is already nonwinning.
- The formal bookkeeping proves that erasing a least available counter produces exactly such a
  shifted upper tail. The A5 and B6 endpoint strata use the `H=6,q=1` catching assertion; the C7
  stratum has both counters 1 and 2 missing, so its least remaining counter is at least 3 and uses
  `H=7,q=3`. Continuations use `H=7,q=1`. The resulting least-counter move is nonlosing in every
  nonempty exact endpoint, and the empty catchable endpoint is tied. Thus the package proves
  `SmallGapTurnEndpointNonloss M`, then `SmallGapFourHoleNonwin M` for `M≥16`, and finally advances
  `DenseThreeHoleNonloss N` to `N+1` whenever `N≥15`, `N+1` is even, and the package holds there.
- Warning-strict target build passed all 8,062 jobs. All five public theorems use exactly
  `[propext, Classical.choice, Quot.sound]`; production audit
  `HISTORICAL_TMP/SmallGapShiftedTailPackageProductionAxiomAudit_20260809.lean`, SHA-256
  `8cc4a3430f3273acef651d1d3f8bf34a007d34280c18a21bde9de4144f3deb46`. Independent adversarial
  audit found no quantifier, Nat-subtraction, catchability, endpoint-shape, perspective, or terminal
  defect. Its certified source differed from the current file only by the subsequent correction of
  “below” to the exact bound “at most” in one definition docstring.
- Exact data support the sharp package at every `M=20,...,24`; `M=19` has fifteen failures of the
  `H=7,q=3` catching assertion. The generalized `H=7,q=1` catch predicate is false even at `M=20`,
  so the lower bound `q=3` in the C stratum is essential rather than cosmetic. The fully formal
  independent scratch is `HISTORICAL_TMP/SmallGapShiftedTailPackage_20260809.lean`, SHA-256
  `b2899813d5032ef3f632b9dfececc112494eadefe4a7705865b4bab392f01813`; exact-data report
  `HISTORICAL_TMP/ShiftedUpperTailReport_20260809.md`, SHA-256
  `ccee73254f2530f93cf3352caddaecd9edb89e8ff564ba1cb0ec99d6a6a6ef73`.
- This is a strict structural reduction, not a proof of the three semantic assertions. A pure
  exact-sum/hole-count attack is stopped sharply: the A5 state
  `Icc 1 M \ {1,2,3,7}` at deficit 7 has no positive exact-seven block, and an exact-block
  injection from another A5 state can land in a genuine seven-hole loss with no next exact block.
  Exact-sum arguments remain excellent certificate pruning but do not form a parametric induction.
  Report `HISTORICAL_TMP/SmallGapExactSumScoutReport_20260809.md`, SHA-256
  `86245f0a4c42d534731e429e39e76c87989af65ff79ee3ceaa0bb3bcb49fd987`.

## Duplicate-tolerant certificate soundness and finite endpoint probe — 2026-08-09 17:27 EDT

- Added `scripts/catch_up/DuplicateTolerantPartialCertificate.lean`, 184 lines / 8,797 bytes,
  SHA-256 `d346f300b64c25f7cc8c87e4ec7f0b9fc655ec406a2f83625094673613444e26`. Its
  `LocalPartialDAGValid` removes only the global `Nodup` conjunct: the root must still be present,
  and every listed occurrence must satisfy the unchanged `PartialNodeValid` predicate. Soundness
  does not need uniqueness. `ContainsPosition` selects a concrete occurrence, `List.Forall`
  validates that occurrence, and every followed `CoversMove` supplies both semantic child
  containment and strict decrease of `remaining.card`. The remaining-card induction therefore
  remains well founded even with duplicates.
- The module supplies an executable local checker, soundness for every contained position/state,
  root soundness, and a dense-three-hole coverage specialization. Independent adversarial audit
  PASS: metadata, root coverage, player-one perspective, occurrence selection, and recursive
  polarity match the original checker. The target build passed all 8,071 jobs and all five public
  theorem audits use only `[propext, Classical.choice, Quot.sound]`. The independent audit covered
  the logic-identical prior hash; the only subsequent change corrected the root theorem's
  docstring. Production axiom audit
  `HISTORICAL_TMP/DuplicateTolerantPartialCertificateProductionAxiomAudit_20260809.lean`, SHA-256
  `8c9b2a7a7920f3b6febe3b9ec122d731c8b4a49e8a91e4e60b756d15f6fb268c`.
- Exact literal generation for the next dense endpoint was independently audited. At `N=13` there
  are exactly 2,646 roots; a cutoff-eight strategy has 6,600 nodes and passes an independent
  bottom-up value, edge, strict-progress, metadata, and root-coverage audit. The deterministic
  generator is `HISTORICAL_TMP/generate_dense_three_hole_literal_certificate_20260809.py`, SHA-256
  `7787f3e7ed425565e85fa0ff5394a2c112734cfb19710ed84054e1b9dd74e5dc`; independent audit script
  SHA-256 `0b4e99c87dc4be13ee91c7f6254da052e11322f665f836b4a49b14bf05d45d46`.
  Cutoff-eight Lean checking remains too expensive with linear list membership and overflows the
  default stack.
- A byte-reproducible cutoff-twelve `N=13` certificate is much smaller: 2,647 nodes, of which 2,640
  are proof-backed target leaves and seven are owner branches. Preserved artifact
  `HISTORICAL_TMP/N13_cutoff12_regen.lean`, SHA-256
  `8b232f246bd6a7a041792423c80b0dfea937103ff0a54398cc6e92faff7638c7`. An initially reported
  warning-strict pass was later retracted as a tool-yield misread. Two fresh root replays were
  stopped after more than six minutes without output, so it is not integrated and the result is
  recorded as noncompletion rather than a checker failure. A proof-backed indexed lookup is now
  the preferred performance target.
- Response-policy evidence also clarifies what an indexed product certificate must encode. Across
  the full A5/B6/C7 family at `M=16,18,20`, the first five remaining counters cover every one-ply
  state, but repeated play requires the first six; first five fails 15, 51, and 106 small-gap roots,
  while first six succeeds all 6,303, 10,106, and 15,508 roots. This is a basin property rather
  than a universal state theorem—the induced strategy may accumulate `M-1` holes. Full report
  `HISTORICAL_TMP/REPORT.md`, SHA-256
  `05e70fc8cc68d3d0669614417933dbb150e8f8c3531655e80e9d5c12dc98c1ea`.

## Linear indexed and packed certificates; dense endpoint thirteen — 2026-08-09 18:05 EDT

- Added `scripts/catch_up/LinearIndexedCertificate.lean`, initially 297 lines / 13,050 bytes. Its
  certificate
  branches store explicit child indices rather than searching a global node list. Every child link
  is still checked against the exact formal `afterPick` state and must strictly decrease
  `remaining.card`; opponent branches must list exactly `availableCounters`, in order, and supply a
  checked child for every move. Dense roots are advertised by indices and placed in a derived hash
  map, but every lookup is rechecked by array lookup and exact decoded-position equality. Thus an
  out-of-bounds index, stale entry, duplicate key, or hash collision can only reject or select an
  independently validated exact node.
- Two independent adversarial audits PASS. They checked wrong/self/OOB child indices, incomplete
  and duplicate opponent move lists, OOB and mismatched roots, duplicate states, recursive
  well-foundedness, owner/current polarity, and exact powerset/range dense coverage. The target
  build and warning-strict source check pass; all four public theorem audits use only
  `[propext, Classical.choice, Quot.sound]`. Production axiom audit
  `HISTORICAL_TMP/LinearIndexedCertificateProductionAxiomAudit_20260809.lean`, SHA-256
  `8f06aad...`; focused adversarial audit `HISTORICAL_TMP/LinearIndexedCertificateAdversarialAudit_20260809.lean`,
  SHA-256 `ea059ba...`.
- The local-edge and hash-index portions audited above are unchanged. After `N=16` exposed a
  default-stack failure in the original full-powerset coverage traversal, `coverageCheck` was
  replaced at the same public API by a proved equivalent enumeration of hole sets of cardinality
  zero through three. The new proof reconstructs any qualifying support as
  `Icc 1 N \ (Icc 1 N \ remaining)` and selects the corresponding `powersetCard` branch. Current
  production SHA-256 is
  `2c76570a37566b951529cc5970cd100021e08f3985e5317da1b4dade258c05f3`.
  Warning-strict source and target builds PASS; concrete `N=13,14,15` checks all replay on the new
  implementation, now in 4.4, 5.0, and 5.7 seconds respectively. Independent audit of this exact
  316-line / 13,990-byte rewrite PASS: it proved the hole/support difference bijection, exhaustively
  compared the old and new enumerated domains for `N=0,...,20`, and reconfirmed the generic
  theorem's standard-only axiom footprint. Audit script SHA-256 prefix `064ded70`; full report
  `HISTORICAL_TMP/LinearIndexedCoverageAndN16FinalAudit_20260809.md`, SHA-256 prefix `6e4acb21`.
- Added `scripts/catch_up/PackedLinearIndexedCertificate.lean`, SHA-256
  `9412511da04822f6b2135480b1c827d6092cbbf66a8fb1db7442e2449f9b70ff`. It parses one compact
  decimal CSV string directly to the indexed DAG, checking decimal syntax, player and branch tags,
  every declared count, truncation, and absence of trailing fields. Malformed, empty, signed,
  whitespace-bearing, Unicode-digit, truncated, huge-truncated-count, bad-tag/player, and
  extra-field inputs all reject. Naturals are parsed without machine-word overflow. The generic
  soundness theorem has only the three standard axioms; independent audits found no logical
  blocker. The absence of an input-size cap is only a resource-exhaustion concern for hostile
  payloads, not a proof-soundness issue. Warning-strict target build passed all 8,061 jobs; the
  full repository build passed all 9,010 jobs after the two generic modules.
- The complete `N=13` strategy was regenerated with no target leaves and independently audited
  bottom-up before packing: 13,759 unique nodes, comprising 38 terminal, 11,841 protected-owner,
  and 1,880 opponent nodes; 22,997 checked edges; and exactly 2,646 dense roots. The mechanical
  payload has 105,560 fields and 340,857 bytes, SHA-256
  `3576f3d571b98b55979992477f85d8bf3066cf5bddd004153a74590503a0637f`; generator SHA-256
  `9c3155d58338fd3d73d95bd414d39adbe9b1344ea6d01f69b9a967ea8a55b63f`.
- Added `scripts/catch_up/DenseThreeHoleN13PackedCertificate.lean`, 53 lines / 342,922 bytes,
  SHA-256 `cd645d1abae14cfde1d3b8f786e97b0e175bf6e5bb3c06f6aa6ff96beff998b8`.
  The executable runner decodes in 144 ms, checks every local branch in 396 ms, and checks dense
  coverage in 1,132 ms. The whole warning-strict `native_decide` theorem and formal
  `DenseThreeHoleNonloss 13` corollary pass in about 6.2 seconds; the Lake target build passed all
  8,062 jobs. Both concrete theorems expose exactly
  `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`, with native
  compiler trust confined to the Boolean certificate check. Axiom audit
  `HISTORICAL_TMP/DenseThreeHoleN13PackedCertificateAxiomAudit_20260809.lean`, SHA-256
  `55d3250ee11b0b78020b54263f9cda80ff2346fe954ecf064c1bb05a5cc1397b`.
- Independent integrated readback PASS at the exact production hash. A separate decoder parsed all
  105,560 fields with no trailing data and matched the earlier audited full literal node-for-node:
  every state, branch kind, chosen owner move, full opponent list, child index, and dense-root order.
  It reconfirmed 38/11,841/1,880 terminal/owner/opponent branches, 22,997 edges, zero target tags,
  and exact dense-root set coverage. Fresh warning-strict check completed in 5.67 seconds. Auditor
  `/private/tmp` script SHA-256
  `13dbef1923e413d332f7dda379c5e7f821fdef251f2901f2158744e77793210f`;
  mutation audit SHA-256 `4627b9ef...`; independent axiom audit SHA-256 `344e2fef...`.
- After integration, `lake --wfail build CatchUpResearch` passed all 8,142 jobs and a fresh full
  `lake --wfail build` passed all 9,010 jobs.
- This resolves the measured serialization bottleneck rather than weakening certificate
  obligations. The equivalent 736,766-byte nested array literal did not finish elaborating in
  more than 100 seconds, while the packed full proof checks in about six seconds. Independent
  readback of the integrated `N=13` file passed, as did the independently generated packed
  extensions through `N=18` recorded below.

## Packed dense endpoint fourteen — 2026-08-09 18:11 EDT

- Added `scripts/catch_up/DenseThreeHoleN14PackedCertificate.lean`, 50 lines / 580,097 bytes,
  SHA-256 `da40ed8631a091eba994c5a7bc63d05fd3d9c22e9d3a39ccaf37d0f1a021a42c`.
  This is again a complete strategy with no target leaves. Independent exact audit verifies 22,003
  unique states, 3,528 dense roots, and 37,894 edges, split into 40 terminal, 19,004 protected-owner,
  and 2,959 opponent nodes. Every root and node was classified safe by an independent recurrence;
  every owner choice, full opponent move list, exact child, metadata field, and one-counter
  cardinality decrease was rechecked.
- The 170,291-field payload has 578,273 bytes and SHA-256
  `5b16954e44eb460869f54dcb5f84cab5054fa19ab2887be648025dae5ca64fa1`;
  deterministic generator SHA-256
  `21250dd45ca2edfeb6cdf88deca3db6671b4a136e85a2d3b2fdb87f616501537`;
  focused independent auditor SHA-256
  `df50fa538a55d7e5a7a77a135ee3a7daa7b294afe1b9b30f18654ca07b46ee3d`.
  Median measured decode/local/coverage times were 244/686/2,644 ms; the warning-strict native
  theorem and formal `DenseThreeHoleNonloss 14` corollary pass in about 7.5 seconds. Fresh production
  direct check and the 8,062-job Lake target both PASS. The concrete axiom footprint is the expected
  three standard axioms plus `Lean.ofReduceBool` and `Lean.trustCompiler` at the native Boolean
  boundary.

## Packed dense endpoint and interval draw at fifteen — 2026-08-09 18:17 EDT

- Added `scripts/catch_up/DenseThreeHoleN15PackedCertificate.lean`, 61 lines / 947,837 bytes,
  SHA-256 `36180a471d5ed5d0695f23c607469773d3e63a9b87ec3ed3550b8fe3c820752b`.
  Independent scalar minimax and structural audit verifies all 34,622 nodes, 4,608 dense roots,
  and 61,443 exact edges: 47 terminal, 29,943 protected-owner, and 4,632 opponent branches. It
  rechecked every exact child, perspective switch, strict card decrease, full opponent move list,
  deterministic first-safe owner choice, metadata field, and root set. Regeneration reproduced the
  payload and wrapper byte-for-byte.
- The payload has 270,618 fields / 945,432 bytes, SHA-256
  `1f668517386d7425e3cb4abf0fd296381b6051063ba614ee5e08f416bf97310f`;
  generator/auditor SHA-256
  `6fb1884beaa86314745fc65c089be57c935e50ccdbcf00cfe3b11d2eb120f38b`.
  Decode/local/coverage took 390/1,195/6,102 ms; the warning-strict concrete theorem passes in about
  11.9 seconds. Trailing-data and out-of-bounds-root mutations reject. Fresh production direct check
  and the 8,062-job Lake target both PASS.
- The module formally proves the stronger `DenseThreeHoleNonloss 15` and, via the ordinary
  dense-reduction theorem and the even triangular total 120, the explicit conjecture instance
  `value (Finset.Icc 1 15) = .draw`. The logical bridge has only the standard three axioms; the
  concrete results additionally inherit the disclosed `Lean.ofReduceBool` and `Lean.trustCompiler`
  boundary from the packed `native_decide` check.

## Packed dense endpoints sixteen through eighteen — 2026-08-09 18:35 EDT

- Added `scripts/catch_up/DenseThreeHoleN16PackedCertificate.lean`, 61 lines / 1,507,853 bytes,
  SHA-256 `3cd6423c1f3ef0bb17653588a2f6ea5e43828870f6e964a4f8775470f239fa8d`.
  Its 1,505,475-byte payload has SHA-256
  `ea42ad8d1ac330bc3a51f4fdab9fd494f030d4a1bb8d1c8a94e95f33d9a2c6fb`.
  Independent recurrence and packed-structure audits verify 53,741 nodes, 5,921 dense roots, and
  98,058 edges, split 49 terminal / 46,536 protected-owner / 7,156 opponent, with no target leaves.
  The default-stack warning-strict check passes in about 7.1 seconds and the 8,062-job Lake target
  passes. The module proves `DenseThreeHoleNonloss 16` and the explicit interval draw at total 136.
- Added `scripts/catch_up/DenseThreeHoleN17PackedCertificate.lean`, 2,402,935 bytes, SHA-256
  `323404ef22de146625b509b97f529df60c85a49c6b93699b6f1e21216624af4e`.
  Its 2,401,109-byte payload has SHA-256
  `c72e92d2adef27b821ee430d7fa120a67e758187da2747a196234abadc6ab47c`.
  Independent exact recurrence over all 2,359,296 scalar states and an independent packed audit
  verify 82,693 nodes, 7,506 roots, and 155,088 edges, split 62 / 71,648 / 10,983, again with no
  target leaves. The warning-strict default-stack check passes in about 9.3 seconds and its Lake
  target passes. It proves `DenseThreeHoleNonloss 17`; no draw corollary is stated because the
  triangular total 153 is odd.
- Added `scripts/catch_up/DenseThreeHoleN18PackedCertificate.lean`, SHA-256
  `ec70f80224229046dcacf84126de43cddd2c239e1404848f97d047e803a3d381`.
  Its 3,789,816-byte payload has SHA-256
  `ee4d8d4f3fd17090f247d353c06515a2f9c79c5463826eef0fab997efc572fee`.
  Independent scalar and packed audits verify 124,705 nodes, 9,390 roots, and 240,889 edges, split
  63 / 108,061 / 16,581, with no target leaves. The warning-strict default-stack check passes in
  about 12.4 seconds and its Lake target passes. It proves `DenseThreeHoleNonloss 18`; the total
  171 is odd, so again no interval-draw corollary is claimed.
- All three concrete certificate theorems have exactly the standard axioms plus the disclosed
  `Lean.ofReduceBool` and `Lean.trustCompiler` native-evaluation boundary. Their generic indexed
  checker and coverage soundness remain kernel proofs with only
  `[propext, Classical.choice, Quot.sound]`.
- After integrating the complete `N=13,...,18` tranche and the stack-safe coverage proof,
  `lake --wfail build CatchUpResearch` passed all 8,147 jobs and a fresh full
  `lake --wfail build` passed all 9,010 jobs. `git diff --check` is clean.

## Packed dense endpoint and interval draw at nineteen — 2026-08-09 18:38 EDT

- Added `scripts/catch_up/DenseThreeHoleN19PackedCertificate.lean`, 61 lines / 5,975,884 bytes,
  byte-identical SHA-256
  `5355071ddc44407f5e28ae24b50f24b963e37fcb55cf657678fe56ff447a4889`.
  Its 1,542,200-field / 5,973,499-byte payload has SHA-256
  `5c296565be20a53ae5fa7fa25777d5edf33b640ee1bc437ddebf30d2b4353b66`.
- Independent full recurrence and packed audits verify all 188,916 unique nodes, 11,600 dense
  roots, and 374,872 exact edges, split 73 terminal / 163,655 protected-owner / 25,188 opponent,
  with no target leaves. The independent evaluator classified 10,485,760 normalized states;
  every owner choice, full opponent list, exact child index/state, strict card decrease, and root
  was rechecked. Literal SHA-256
  `5daf19d628bf4dc1332356e80e61491a48f9fa5c70830e6b343bad2d0f39d30d`;
  full report `HISTORICAL_TMP/DenseThreeHoleN19PackedPipelineReport_20260809.md`, SHA-256
  `85e24fded69cbe382cbaba8fa19f96a6ae9a2dd7a4b06d763c9aa6d4b7a3a3bd`.
- Warning-strict default-stack verification passes in about 17.0 seconds and the 8,062-job Lake
  target passes. The module proves `DenseThreeHoleNonloss 19` and the explicit interval draw at
  triangular total 190. The concrete proof has only the standard axioms plus the disclosed native
  Boolean `Lean.ofReduceBool` / `Lean.trustCompiler` boundary and no `sorryAx`.

## Packed dense endpoint and interval draw at twenty — 2026-08-09 18:43 EDT

- Added `scripts/catch_up/DenseThreeHoleN20PackedCertificate.lean`, 61 lines / 9,174,612 bytes,
  byte-identical SHA-256
  `2dfdb27309c67465b929fc45115a975c0c7df9e6766cda10bc7292387e5bbb25`.
  Its 2,311,754-field / 9,172,225-byte payload has SHA-256
  `0fd599a1131ee76b139d5da7b794fdd461a53dd8dad9f7a35f6ebf2df9a4a650`.
- Independent Python and C++ evaluators agree after classifying all 22,020,096 normalized states.
  The Python distribution is 878,314 loss / 6,652,827 draw / 14,488,955 win. They rechecked all
  279,639 unique certificate nodes, 14,181 qualifying roots, and 570,816 exact edges, split 78
  terminal / 242,180 protected-owner / 37,381 opponent, with no target leaves. Of the dense roots,
  14,180 are draws and one is a win; none is a loss, while the full tied interval root is a draw.
  Python audit SHA-256
  `df4dfd212c128646eb169d5e07beaf213031c5218e1c6b92108bd425d810c3e5`;
  independent warning-strict/sanitizer-clean C++ source SHA-256
  `d79ef3b02721de699868261fbb8f6308f9d975317272144ba3232b2bd09b73f8`.
- Warning-strict default-stack verification passes in about 24.3 seconds and the 8,062-job Lake
  target passes. The module proves `DenseThreeHoleNonloss 20` and the explicit interval draw at
  triangular total 210. Its axiom footprint is exactly the standard three plus the disclosed
  native Boolean boundary; no `sorryAx`, trusted target leaf, or source placeholder occurs.
- Added `scripts/catch_up/DenseThreeHoleCertifiedRange.lean`, SHA-256
  `f86b64a56632434f12dfd3c21c04f3ae13b4f8427f7444da1a35d8926fca341f`.
  It collects the independently proved `N=9,...,20` instances into the single theorem
  `dense_three_hole_nonloss_nine_through_twenty`, then applies the generic dense reduction to prove
  every even-triangular interval in that range is a draw. Warning-strict direct elaboration and the
  8,086-job Lake target PASS. Both aggregate theorems have exactly
  `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`, reflecting only
  the already disclosed finite certificate checks.
- Independent audit of the exact aggregate production hash PASS. It rechecked all eleven direct
  imports and the exact twelve-way `N=9,...,20` branch mapping; verified that the draw theorem
  derives `4 ≤ N` only from `9 ≤ N`, forwards the triangular parity premise unchanged, and makes
  no odd-total claim; reran the 8,086-job target; and reconfirmed the expected axiom footprint.
  Text-audit SHA-256 prefix `3f98c30f`; no blocker.
- With all certificates through `N=20` and the aggregate imported, a fresh
  `lake --wfail build CatchUpResearch` passed all 8,150 jobs and a fresh full build passed all
  9,010 jobs.

## Packed dense endpoint twenty-one — 2026-08-09 18:51 EDT

- Added `scripts/catch_up/DenseThreeHoleN21PackedCertificate.lean`, 53 lines / 14,216,409 bytes,
  byte-identical SHA-256
  `91c1929970f718c91143ecbb6c5308afd2cdd5cef7089bd6490a2b8689114b32`.
  Its 3,479,051-field / 14,214,336-byte payload has SHA-256
  `ec100b4745eb80ddb882b6ff1c9caa256145e3fe65240452278b2020d5a49e6d`.
- Independent fixed-byte-cache recurrence and packed audits verify 21,887,459 exact values,
  415,744 unique certificate nodes, 17,182 dense roots, and 871,467 edges, split 88 terminal /
  359,701 protected-owner / 55,955 opponent, with no target leaves. Every polarity, exact child,
  complete opponent list, strict rank decrease, and canonical root was rechecked. Literal SHA-256
  `2fcfe729f469f3742096a5a2013dcd63ff669d36ed59eeaeb72fa41ccae9171e`;
  report `HISTORICAL_TMP/DenseThreeHoleN21PackedPipelineReport_20260809.md`, SHA-256
  `2082a53bd4c5134437e6c77f5640917d7b6e4ed7dcb3d649d5c962d84cc17b73`.
- Default-stack warning-strict verification passes in about 36 seconds and the 8,062-job Lake
  target passes. The module proves `DenseThreeHoleNonloss 21`; correctly, it states no draw theorem
  because triangular total 231 is odd. The concrete axiom boundary is the same disclosed native
  Boolean boundary and contains no `sorryAx`.

## Packed dense endpoint twenty-two — 2026-08-09 18:57 EDT

- Added `scripts/catch_up/DenseThreeHoleN22PackedCertificate.lean`, 53 lines / 21,511,982 bytes,
  byte-identical SHA-256
  `c69a20ad8a67c4e93dbf6fe138ebccd7c10dbdff3c96fc2526b909874baacc1f`.
  Its 5,183,347-field / 21,509,909-byte payload has SHA-256
  `2c5320a29f524fefc38190f79b6f4609326013114031aef2b3012445352c5d37`.
- A fresh independent C++20 implementation classified all 96,468,992 scalar states and performed a
  second full Bellman-residual traversal over every cell: 61,829,492 win / 31,226,426 draw /
  3,413,074 loss. All 20,636 dense roots are draws. Before reading the payload it independently
  derived the same 612,042 unique nodes and 1,316,041 edges, split 91 terminal / 529,494 owner /
  82,457 opponent. Its strict payload pass then rechecked every decimal field, state, polarity,
  terminal, first-safe owner move, complete opponent list, child, rank decrease, and root. The
  warning-strict ASan+UBSan-clean auditor source has SHA-256
  `de445e7d15a226763ae0e39f45785f733a081534d75e5cb69cad3994308bb6c6`.
- Default-stack warning-strict verification passes in about 53 seconds and the 8,062-job Lake target
  passes. The module proves `DenseThreeHoleNonloss 22` and correctly has no draw theorem because
  triangular total 253 is odd. It uses the standard axioms plus the same disclosed native Boolean
  boundary, with no target leaves, placeholders, or `sorryAx`.

## Exact formal dense invariant and interval draw at twenty-three — 2026-08-09 19:09 EDT

- Added `scripts/catch_up/DenseThreeHoleN23PackedCertificate.lean`, 61 lines / 32,517,679 bytes,
  byte-identical SHA-256
  `db3c295779b0a166c6594868b2b58e1dc4f87d521f627f705df85aeec64ba6c3`.
  Its 7,754,888-field / 32,515,262-byte payload has SHA-256
  `3df61d5869f656cae7b1b18786c781eed69d4451a160f69b3156ea4c72307913`.
- A fresh independent recurrence classified all 201,326,592 scalar states, then a second full
  Bellman pass revalidated every cell. All 24,576 qualifying dense roots are draws. Before trusting
  the payload, the audit independently reconstructed the same deterministic, constant-false-target
  DAG: 903,308 unique nodes and 1,996,844 edges, split 105 terminal / 779,815 owner / 123,388
  opponent. It then checked every packed field, exact root/state set, polarity, terminal, first-safe
  owner move, complete opponent list, child index/successor, and strict rank decrease.
- Default-stack warning-strict Lean verification passes in 80.6 seconds; a separate imported-olean
  readback confirms decode/local/coverage/whole are all true and all three public theorems have
  exactly `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`.
  The 8,062-job Lake target passes. The module proves both `DenseThreeHoleNonloss 23` and the exact
  interval draw at triangular total 276. Full report
  `HISTORICAL_TMP/REPORT.md`, SHA-256
  `5968d8b5e030736e50e505a50123e5bb75c0577ef228196bcb87d0a5ab02691b`.
- This advances the campaign's exact formal result beyond the source paper's exact-through-20
  computation and replaces its `N=23` MCTS evidence with a fully checked certificate. No claim of
  a parametric proof is made: the global conjecture remains open.
- Extended `scripts/catch_up/DenseThreeHoleCertifiedRange.lean` to `N=9,...,23`, current SHA-256
  `c59246fa8af1c812fe00a787e7f583d674e20a6435c2c0ae8da11d17a4cba4ec`, while retaining the old
  through-twenty theorem names as compatibility corollaries. Its warning-strict direct check and
  8,089-job Lake target PASS. The new range invariant and conditional draw theorem inherit exactly
  the same disclosed finite-evaluation axiom boundary.
- With the exact `N=23` endpoint and extended aggregate imported,
  `lake --wfail build CatchUpResearch` passed all 8,153 jobs and a fresh full build passed all
  9,010 jobs.
- Independent post-integration audit PASS at the exact endpoint and range hashes. It compiled all
  fifteen `N=9,...,23` numeral instantiations, rechecked the `N=23` parity/draw reduction and both
  through-twenty compatibility signatures, reran warning-strict target/range checks, and found the
  expected axiom footprint for all seven public theorems with no `sorryAx`. Report
  `HISTORICAL_TMP/N23IntegratedRangeAuditReport_20260809.md`, SHA-256
  `d73974eb917f70811adbd349fbebc8249f4ca3ce88fb9a2174e78344ecbbd993`.

## Exact formal dense invariant and interval draw at twenty-four — 2026-08-09 19:35 EDT

- Added `scripts/catch_up/DenseThreeHoleN24PackedCertificate.lean`, 61 lines / 49,914,523 bytes,
  byte-identical SHA-256
  `b762ccfb87800cd999cbfd6d5f732cabf895911dbf31cac1c9fe97b21a1c9da7`.
  Its 11,461,998-field / 49,912,121-byte payload has SHA-256
  `951a7c0807b1596677d30b36924ab091c64a31d0cbefe7db77c86670ec99d021`.
- Exact generation took 1,044.57 seconds and produced 200,646,145 cached values, 29,057 dense
  roots, 1,319,099 unique nodes, and 2,987,827 edges, split 106 terminal / 1,138,106 owner /
  180,887 opponent, with no target leaves. A separate fixed-byte-cache audit took 580.29 seconds,
  peaked at 1,069,858,816 bytes RSS, and rechecked exact recurrence, polarity, every edge/root, and
  the complete packed literal byte-for-byte. Literal SHA-256
  `92ede39d364e215c48ea94ce082c41f1fe5e4cc9feb4b54a33ec0c9834659b74`;
  report `HISTORICAL_TMP/DenseThreeHoleN24PackedPipelineReport_20260809.md`, SHA-256
  `ce730b32997b1103d06251de79ff564ef7b251a5a8ad720b65638ff859dbcedf`.
- Default-stack warning-strict verification passes in 121.8 seconds and the integrated 8,062-job
  Lake target passes in 119 seconds. The module proves `DenseThreeHoleNonloss 24` and the exact
  interval draw at triangular total 300, with the expected native finite-check boundary only and no
  `sorryAx`.

## Exact formal dense invariant at twenty-five — 2026-08-09 19:35 EDT

- Added `scripts/catch_up/DenseThreeHoleN25PackedCertificate.lean`, 53 lines / 76,046,743 bytes,
  byte-identical SHA-256
  `b28ac63e59a42d2dd2ffdcdb8e6affa1de21fb39074f03ef7b9cc84b4f790cb4`.
  Its 16,995,513-field / 76,044,665-byte payload has SHA-256
  `34c6b3d88709279f7de13d997adbd8b734a3fe5fe9876609df91d73c1018fcdb`, leaving 23,953,257
  bytes below the explicit 100,000,000-byte single-file stop gate.
- An independent C++ implementation classified all 872,415,232 scalar states and performed a
  second Bellman-residual traversal comprising 10,905,177,613 move evaluations with zero mismatch:
  535,584,527 win / 310,366,118 draw / 26,464,587 loss. All 34,138 dense roots are draws. It
  independently reconstructed and then field-by-field checked the complete deterministic DAG:
  1,931,447 nodes and 4,484,168 edges, split 120 terminal / 1,664,080 owner / 267,247 opponent.
  Warning-strict audit source SHA-256
  `c3f6d2de3769a654fea80c84f25044d8b1c5df05e9217c7eaf82d773f286a5f1`;
  deterministic generator/auditor source SHA-256
  `8760efc1d361bce198c3a9827f194e03f7a3f2f4042f5b29e051c2bd7d858404`.
- Default-stack warning-strict verification passes in 189.1 seconds and the integrated 8,062-job
  Lake target passes in 185 seconds. The module proves `DenseThreeHoleNonloss 25` and correctly
  states no draw theorem because triangular total 325 is odd. It has no target leaf, placeholder,
  `sorryAx`, or encoding/trust relaxation.
- Extended `scripts/catch_up/DenseThreeHoleCertifiedRange.lean` through `N=25`, current SHA-256
  `b70f2eda87e8481a40c142e20845bea9425596a900c1b49ca5ec7e1bfd0a8cef`, while retaining the
  through-twenty and through-twenty-three APIs as compatibility corollaries. Warning-strict direct
  elaboration and the 8,091-job Lake target PASS; all six range/conditional-draw theorems inherit
  exactly the disclosed finite certificate axiom footprint.
- With the complete `N=9,...,25` certified range imported, a fresh
  `lake --wfail build CatchUpResearch` passed all 8,155 jobs and a fresh full build passed all
  9,010 jobs.
- Independent integrated audit PASS for the exact N24, N25, and current range hashes. It reran the
  full N24 literal/root audit and the N25 872,415,232-state / 10,905,177,613-move recurrence,
  checked every packed field and exact branch, instantiated the complete `N=9,...,25` theorem
  surface, and reran warning-strict checks (N24 133.61s, N25 195.05s, range 5.13s). It confirmed
  zero target leaves, the exact even-triangular draw set `{11,12,15,16,19,20,23,24}`, and only the
  disclosed native-check axioms. Report
  `HISTORICAL_TMP/IntegratedN24N25CertifiedRangeAudit_20260809.md`, SHA-256
  `e7de35e4b10857e123ffb385c29bf4f306917126467447afbb2080dee62ac831`.

## All even-triangular intervals through twenty-four — 2026-08-09 19:39 EDT

- Added `scripts/catch_up/CatchUpSmallBaseDraws.lean`, 123 lines / 4,830 bytes, SHA-256
  `551c684cfc0d379032e2eae305440fa25d38650976ac8fbbe36a38cddad0d0e4`. It closes exactly the
  missing even-triangular bases `N = 0, 3, 4, 7, 8`: the empty interval is reduced in the kernel,
  while the four positive bases use the executable one-sided-safety classifier only through its
  proved `CanAvoidLoss` equivalence. The module then proves a generic finite-range theorem from any
  supplied dense-three-hole range `N = 9,...,24`.
- Extended `scripts/catch_up/DenseThreeHoleCertifiedRange.lean`, current SHA-256
  `d61e679b5a6d1265d5c7fa633c9e1a0158c3dcc6459c1d64b174c9cfcc8893ed`, with the unconditional
  theorem `value_Icc_eq_draw_le_twenty_four_of_even_triangular`: for every natural `N ≤ 24`, if
  `N * (N + 1) / 2` is even, then optimal Catch-Up play on `{1,...,N}` is a draw. This combines the
  five small bases with the independently certified dense invariant through twenty-five; no claim
  is made at odd triangular totals.
- Direct warning-strict elaboration of the small-base module passes, and
  `lake --wfail build catch_up.DenseThreeHoleCertifiedRange` passes all 8,092 jobs. `git diff
  --check` is clean. The positive small-base and aggregate theorems inherit the already disclosed
  native Boolean evaluation boundary; the underlying classifier equivalence and range reduction
  remain ordinary kernel-checked logic. Warning-strict axiom audit SHA-256
  `7c1a7580831a537e89d9f4011b717e50ea15d8fd52a5f8d07bae9daed6d75c85` confirms that the empty
  base uses only `[propext, Classical.choice, Quot.sound]`, while the positive bases and final
  finite-range theorem add exactly `[Lean.ofReduceBool, Lean.trustCompiler]`.
- An independent post-integration audit PASS at the exact production hashes. It rechecked all
  thirteen parity-admissible indices through twenty-four, confirmed that the low branch excludes
  exactly `N = 1,2,5,6` and uses exactly the five proved bases, audited the protected-player
  polarity, reran direct warning-strict checks and the combined Lake targets, and found no
  placeholder or undeclared axiom. Report
  `HISTORICAL_TMP/CatchUpSmallBaseIntegratedAuditReport_20260809.md`, SHA-256
  `69940b9ef652b8959a4a67542a004720a7c6141c1cb953fd207524cac8f3025e`; audit harness SHA-256
  `cfc308337ddcb0a09a69d4bec25bf76f6e2cadb4627a62829a1df6e36fe71055`.

## One-opening packed root-draw checker — 2026-08-09 19:53 EDT

- Added `scripts/catch_up/OpeningPackedIndexedCertificate.lean`, 173 lines / 8,276 bytes, SHA-256
  `cb1feb4c7cd027d25bb7aacd0ecbdfae373a768c22fe9af5479692dadf4c0a6c`. It reuses every local
  obligation of the linear indexed checker, but replaces dense-family coverage with one exact
  advertised post-opening root. Two constant-false-target certificates protect Player 1 and
  Player 2 at that same root; their conjunction proves the normalized root value is draw, and the
  already proved opening-exchange theorem then proves the entire interval game is draw. Thus no
  all-openings Player-2 certificate is required.
- Metadata, legal-opening membership, singleton root-index shape, exact decoded post-opening state,
  all owner/opponent branches, and strict remaining-cardinality descent are independently checked.
  Malformed packed input, a wrong owner, wrong opening, missing/out-of-bounds root, or an extra
  advertised root all fail closed.
- Direct warning-strict elaboration and the 8,063-job Lake target PASS. Warning-strict axiom audit
  `HISTORICAL_TMP/OpeningPackedIndexedCertificateAxiomAudit_20260809.lean`, SHA-256
  `62c0dea51d92255aa4ec02f4126ba8eb95aa38283d9fcd65e3379e0fa8809c0c`, reports exactly
  `[propext, Classical.choice, Quot.sound]` for all five public soundness theorems: there is no
  native computation, trusted leaf, or placeholder in the generic bridge.

## Exact formal root draw at twenty-seven — 2026-08-09 20:01 EDT

- Added `scripts/catch_up/CatchUpN27PackedRootDraw.lean`, 58 lines / 31,294,992 bytes, SHA-256
  `091d5cc3f3fea0774be3b3049640a623ba0e1d6a482129a66d8056e257aaca39`. It checks two complete
  constant-false-target strategies at the same position after opening counter one, then applies the
  generic one-opening theorem to prove `value (Icc 1 27) = draw`.
- The protected-P1 payload has SHA-256
  `1f9ae2cf194518d735704570f77c0ff0b058fc31b0e7ea70112815a92afa200f`: 403,358 nodes,
  994,478 edges, 3,693,113 fields, and 16,211,951 bytes, split 82 terminal / 312,556 owner /
  90,720 opponent. The protected-P2 payload has SHA-256
  `a868e2167355e721b9bdd084ef4683952d2229fa2253a260e54a642fa2db5d28`: 376,208 nodes,
  925,985 edges, 3,442,879 fields, and 15,080,968 bytes, split 79 / 290,057 / 86,072.
- A fresh independent packed Bellman implementation checked every one of `2^27 * 28 =
  3,758,096,384` source-table labels and 1,811,939,328 mask/move transforms, with zero malformed
  words or mismatches; a separate scalar recurrence checked one million samples. Exact W/D/L is
  2,238,006,556 / 1,415,669,286 / 104,420,542, and all 27 post-opening positions are draws. The
  table SHA-256 is `88ccc20388d36d14f3045c2f77aa1059a03dc5218b60bf9b57ead7bfaf1515c8`.
- Independent C++ and Python traversals rebuilt both sorted strategy DAGs, and a streaming
  comparator matched all 7,135,992 payload fields—including every metadata field, state, branch,
  legal move, and child index—both standalone and embedded. A wrong-player mutation rejects at
  field two. Full report
  `HISTORICAL_TMP/FINAL_INTEGRATED_AUDIT.md`, SHA-256
  `c540eaa10bd4cfbcd1424f9e7ef735f71051a25b0dc0cf7c2cf90848f4c2d02f`.
- Direct warning-strict verification passes in 58.04 seconds and the 8,064-job Lake target passes
  in 57 seconds. The generic soundness layer remains standard-axiom-only; the concrete Boolean
  certificate and draw theorem add exactly `[Lean.ofReduceBool, Lean.trustCompiler]`, with no
  `sorryAx` or target leaf.

## Exact formal root draw at twenty-eight — 2026-08-09 20:04 EDT

- Added `scripts/catch_up/CatchUpN28PackedRootDraw.lean`, 58 lines / 48,729,491 bytes, SHA-256
  `410cd96932843f001b6d77d042e7fa38881b57114bdea09e00a1a1a420cb21dd`. It uses the same exact
  opening-one/two-owner construction and proves `value (Icc 1 28) = draw`.
- Protected P1: payload SHA-256
  `aee0fa0593a4c99f93d8fa377c8a04c421676a5cb0a1d5f40bef25ffe67ac9a5`, 618,700 nodes,
  1,542,646 edges, 5,696,670 fields, 25,440,765 bytes, branches 91 terminal / 482,036 owner /
  136,573 opponent. Protected P2: SHA-256
  `1051bd177811c1218d0861624da198dd66e2d2cc6b6432611867b7a8dcc7e932`, 566,899 nodes,
  1,414,078 edges, 5,223,179 fields, 23,286,653 bytes, branches 91 / 439,386 / 127,422.
- A separate C++ Bellman residual checked all 268,435,456 masks, 7,784,628,224 labels, and
  3,758,096,384 mask/move transforms with zero mismatch; exact W/D/L is 4,565,496,966 /
  3,011,344,704 / 207,786,554. Independent streaming audits checked every payload field and more
  than 9.8 million scalar child evaluations; deterministic regeneration was byte-identical; the
  actual Lean decoder and local checker returned true for both payloads. Source-table SHA-256 is
  `75f984ed1cd0152ae835e74b2b6f236e51dd125933a3dfdef75ed746c587506e`; full report
  `HISTORICAL_TMP/CatchUpN28Opening1TwoOwnerPayloadReport_20260809.md`, SHA-256
  `06cf89573c4b236d59b20b5d79163fd6f0ee9864b18494fbb9f2d4e2444d151d`.
- Direct warning-strict verification and the 8,064-job Lake target PASS (the latter in 86 seconds).
  Axiom audit `HISTORICAL_TMP/CatchUpN28PackedRootDrawAxiomAudit_20260809.lean`, SHA-256
  `e767657b2cb081d9a1db552abf94cebc08568d189405d7ca771f87faea08581e`, reports only the standard
  three plus the disclosed native Boolean boundary and no `sorryAx`.

## All even-triangular intervals through twenty-eight — 2026-08-09 20:06 EDT

- Added `scripts/catch_up/CatchUpCertifiedThrough28.lean`, 47 lines / 1,770 bytes, SHA-256
  `95e1315e3a1e57ea58d60dc7a0d3800875354dcd4e6daf22a983f9afa2eed0e1`. Its theorem
  `value_Icc_eq_draw_le_twenty_eight_of_even_triangular` combines the unconditional range through
  twenty-four, rules out twenty-five and twenty-six by parity, and applies the exact N27/N28 root
  certificates. Therefore every natural `N ≤ 28` with even triangular total has formal draw value.
- Direct warning-strict elaboration and the 8,097-job Lake target PASS. Axiom audit SHA-256
  `211e0f5c84350bf68aa1a5c73cb1a9fc2337e2d3d6733ff4f9d014ee3ff9c552` reports exactly the
  disclosed finite-certificate axiom boundary. `git diff --check` remains clean.
- With both opening-specific endpoints and the bounded aggregate imported, a fresh
  `lake --wfail build CatchUpResearch` passes all 8,160 jobs and a fresh full
  `lake --wfail build` passes all 9,010 jobs.
- Independent post-integration N28/through-28 audit PASS at the exact production hashes. It
  byte-compared both embedded payloads, reran the complete 7,784,628,224-label Bellman residual and
  one million scalar samples, checked all 1,185,599 strategy nodes and 9,850,848 child evaluations,
  and exhaustively verified that the aggregate covers exactly
  `{0,3,4,7,8,11,12,15,16,19,20,23,24,27,28}`. Warning-strict endpoint, aggregate, and theorem
  surface checks pass; no placeholder or unexpected axiom occurs. Report
  `HISTORICAL_TMP/CatchUpN28AndCertifiedThrough28IntegratedAudit_20260809.md`, SHA-256
  `315f59a6f8b7ddf9a7e75cc93df409e4479e2403e1e847e109f5e1362d2c5701`.

## Held-out shifted-tail package through twenty-eight — 2026-08-09 20:45 EDT

- The final report isolated the formal sufficient package
  `ShiftedUpperTailContinuationNonloss M 7 1 ∧ ShiftedUpperTailCatchNonwin M 6 1 ∧
  ShiftedUpperTailCatchNonwin M 7 3`. A bounded held-out audit exhaustively evaluated all three
  predicates at `M = 25,26,27,28`.
- All 61,746,189 antecedent-satisfying roots pass, with zero failures in every predicate. Exact
  counts in continuation-H7/catch-H6/catch-H7-q3 order are: M25
  `8,591,829 / 279,709 / 94,528`; M26 `11,989,664 / 355,786 / 117,358`; M27
  `16,514,172 / 448,386 / 144,483`; M28 `22,473,568 / 560,358 / 176,348`.
- Fresh C++ and Python enumerators agree on every count and value distribution. M25/M26 are exact
  smaller-mask subgames in the exhaustively audited N27 table; a separate cross-ambient replay in
  the N28 table agrees. Full report
  `HISTORICAL_TMP/REPORT.md`, SHA-256
  `eaf9b3a35b6086be89b75af28e689585810a18c628ac0c33e84cc2a8bfaf94f7`; independent source
  hashes are `320d2687c81c60cb2efeaaba118ae2ca2a3158bc2311ab8b98214b4c4ff47277`
  (C++) and `4b07ea534119183e61c215c69e2cdca1cd7696efadd5d847807696e5e15c3c67`
  (Python).
- This extends the exhaustive finite package evidence from `M=20,...,24` to `M=20,...,28`. It is
  not a Lean proof of any new instance and does not prove the all-`M` package. The structural gate
  remains open.

## Sharp seven-hole catch-rank reduction — 2026-08-09 21:12 EDT

- Added `scripts/catch_up/ShiftedUpperTailCatchRankReduction.lean`, 192 lines / 9,052 bytes,
  SHA-256 `3d0ee96a2d24905980bdea8778cfc6845e3706c6ac6f603e0d185ae96b405173`.
- The strongest theorem retains an actual winning-move witness. Under the exact catchability,
  upper-tail, even-parity, deficit-at-most-minimum, and seven-hole premises, a winning state either
  has zero deficit or has a winning move `x` for which `x ≤ 16`, the shifted predecessor
  `x - deficit` is already a tail hole, or deleting those two counters leaves an even tied winning
  residual with a globally unique winning opening `y > x - deficit`.
- This is a sharp reduction rather than the missing catch-nonwin theorem. The zero-deficit,
  finite-low-opening, predecessor-hole, and tied-residual cases remain open. Exact `M=19` replay
  places all fifteen `q ≥ 3` failures in three low-boundary states, so the data realize rather than
  contradict the exceptional alternatives.
- Direct warning-strict elaboration and `lake --wfail build
  catch_up.ShiftedUpperTailCatchRankReduction` PASS; the latter builds 8,056 jobs. All three public
  theorems use exactly `[propext, Classical.choice, Quot.sound]`. Production axiom-audit SHA-256 is
  `4cf4a9c2fc071d31e6f82fbd1d00e1c0d24264e57290eb110827ec14d2833943`; detailed reduction report
  SHA-256 is `042d313b27659acf8cda752b9a9a3fba89d8fe166ff76d1b5e331ebc3c6af5aa`.
- Independent integration audit PASS at the frozen production hash. It rechecked the retained
  winning-move polarity, exact child subtraction, even residual calculation, global uniqueness of
  the tied residual's winning opening, the upper-tail hole conversion, and the `m ≤ 8`/`x ≤ 16`
  arithmetic, with no soundness or style blocker.

## Final process-stop and readback — 2026-08-09 22:47 EDT

- Final warning-strict public-surface audit PASS, reading back the exact `N ≤ 28` bounded theorem,
  N27/N28 endpoints, dense `N=9,...,25` invariant, generic one-opening bridge, and seven-hole
  catch-rank theorem together with their exact axiom footprints. Audit source SHA-256 is
  `37284741360eae16b1118d6915c0bf760f219bab2729e7e28ec15f97a2751bd2`.
- Final Lake builds PASS: `catch_up.ShiftedUpperTailCatchRankReduction` 8,056 jobs;
  `catch_up.CatchUpCertifiedThrough28` 8,097; `CatchUpResearch` 8,161; full repository 9,010.
  `git diff --check` is clean.
- Final checkout is `codex/catchup-experiment` at
  `0b67426227811c55db98358c95e99ca5c4465e54`; `codex/lennon-pittel-conjecture` points to the same
  commit. Readback found five tracked-but-unstaged modifications, eighty-nine untracked paths, and
  zero staged paths. Nothing was committed, pushed, or submitted.
- Final report SHA-256 is `c55b31f17b32a2c2d63da603e2b768ed3591fbb4facc354777aa285a467b6e5f`.
  The general conjecture remains open; the strongest formal theorem is exactly the bounded draw
  theorem through twenty-eight recorded above.
