> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Catch-Up research checkpoint

> **Superseded checkpoint.** The later 2026-08-08/09 campaign is complete. Resume from
> `CATCHUP_FINAL_REPORT_20260808_2206_ET.md` (`CATCHUP_FINAL_REPORT_20260808_2206_ET.md`; historical path) and its
> chronological companion
> `CATCHUP_CAMPAIGN_20260808_2206_ET.md` (`CATCHUP_CAMPAIGN_20260808_2206_ET.md`; historical path). The strongest
> current theorem formally certifies every even-triangular interval root through `N = 28`; the
> general conjecture remains open. The material below is retained as an earlier historical
> checkpoint, not current state.

## Deadline and operating constraints

- Deadline: **2026-08-08 08:00 America/New_York**.
- Consolidation begins: **2026-08-08 07:15 America/New_York**.
- Worktree: `SOURCE_CHECKOUT`.
- Branch: `codex/catchup-experiment`.
- Do not commit, push, fetch, switch branches, create worktrees, or modify the two other registered
  worktrees.
- Preserve the pre-existing untracked `research-targets-2026-08-07.md`.

## Current repository state

Checkpoint initialized at **2026-08-07 23:44:43 EDT**.

- `git status --short --branch` initially showed only
  `?? research-targets-2026-08-07.md`.
- Other registered worktrees are separate checkouts at
  `SOURCE_CHECKOUT` and
  `SOURCE_CHECKOUT`; they must remain untouched.
- Process inspection with `ps` was denied by the sandbox. No Git evidence of another writer was
  found. Any delegated work must remain read-only.

## Rigorously or formally established before this checkpoint

- The normalized exact solver exports complete legal move graphs and agrees with an independent
  list recurrence through the checked small frontier.
- The independent strategy-certificate checker has a Lean soundness theorem connecting accepted
  certificates to `CatchUp.CanAvoidLoss`.
- `CanAvoidLossClassifier.check_eq_true_iff` proves that the recursive Boolean classifier is exact
  for the proof-level `CanAvoidLoss` predicate.
- `ThreeCounterSafety.can_avoid_loss_three_counters` proves a uniform safe three-counter family.
- `FourCounterEntry.can_avoid_loss_four_counter_entry` proves a uniform four-counter predecessor:
  the owner removes a designated old counter and enters that three-counter family.
- Boolean predicates selecting the proof-backed top-only, three-counter, and four-counter families
  have Lean soundness bridges to `CanAvoidLoss`.
- The most recent warning-strict full build completed successfully with 9,010 jobs.

## Computational evidence before this checkpoint

- The proof-backed combined endgame basin contains the opening-1 root for both owners at
  `N = 3, 4, 7, 8, 11, 12` where checked by the current experiments.
- Adding the proved four-counter predecessor family does not enlarge the already backward-closed
  basin at `N = 7, 8`: the basin counts remain respectively `(4621, 4701)` and
  `(10458, 10592)` for owners `(p1, p2)`.
- A small first-response rule is basin-preserving for both owners at `N = 7, 8, 11, 12`.
- A stronger common-complete-turn search finds no identical player-2 turn sequence across those
  four sizes after the line `1, 2, 5`. Thus a size-independent fixed counter sequence is not a
  viable full opening protocol. This is negative evidence, not an impossibility theorem for a
  richer state-dependent relation.
- Least-safe-move policy profiles grow to hundreds of coarse decision classes by `N = 11`; that
  policy is not a credible bounded phase relation.

## Failed or narrowed approaches

- Directly pairing arbitrary optimal strategies for `N` and `N+4` produced unmatched old moves and
  too many phase signatures.
- The tied-top-four target has a tiny basin and does not reach the relevant roots.
- Safe top-only targets alone fail at some roots; the explicit one-old family repairs them.
- Treating the four-counter predecessor as a new target does not enlarge the basin because it was
  already a one-step member of the basin.
- A uniform fixed complete first-turn sequence fails for player 2 on the tested sizes after
  opponent counter `5`.

## Current best routes

### Proof route

Find a genuinely small state-dependent or residue-dependent forcing invariant, likely by analyzing
the first obstruction after `1, 2, 5`, or prove a broader symbolic endgame classification whose
backward closure has a tractable parametric description. Any proposed phase relation must cover all
opponent moves and have size bounded independently of `N`.

### Counterexample route

Audit solver correctness and performance, then extend exact computation only where a complete
graph or independently checked certificate is feasible. A claimed counterexample must be supported
by a complete, independently verified loss certificate or a formally checked exhaustive result.

## Commands already run in this continuation

```text
date '+%Y-%m-%d %H:%M:%S %Z (%z)'
pwd
git branch --show-current
git status --short --branch
git worktree list --porcelain
```

## Active unit: audit before selecting the next experiment

- Timestamp: **2026-08-07 23:44:43 EDT**.
- Intended work: audit the formal statement, solver, independent checker, executable frontiers,
  and existing research tools; identify the highest-value rigorous proof and disproof experiments.
- Exact recovery action: read this file, run `date`, then inspect
  `FormalConjectures/Paper/CatchUpConjecture.lean`, `scripts/catch_up/ExactSolver.lean`,
  `scripts/catch_up/CertificateSoundness.lean`, and the current Catch-Up executables. Do not begin a
  long solve until its expected cost and verification path are recorded here.

## Precise next action

Audit declaration coverage and solver/certificate trust boundaries, while separately estimating
the feasible exact frontier and analyzing the `1,2,5` forcing obstruction. Update this checkpoint
before launching either experiment.

## Interim handoff report

At 23:44 EDT the conjecture remains unresolved. The checkout is on the intended branch with only a
pre-existing untracked research note. Existing Lean proofs rigorously establish the game semantics,
certificate soundness, an exact Boolean safety classifier, and useful three- and four-counter safe
families. Computation strongly supports opening-1 non-loss for both players at tested sizes, but the
attempted fixed opening protocol fails to remain uniform after the player-2 line `1,2,5`. The next
work is an audit followed by either a state-dependent analysis of that obstruction or a rigorously
verified extension of the exact frontier.

## Audit update — 2026-08-07 23:48:18 EDT

### Rigorously established from source inspection

- The formal conjecture is exactly
  `CatchUp.value (.Icc 1 N) = .draw` under
  `Even (N * (N + 1) / 2)`; this includes both strategic directions, not merely a safe selected
  opening.
- The formal API proves that `CanAvoidLoss` is equivalent to the appropriate inequality on the
  normalized minimax value (`can_avoid_loss_iff_value`), and that the full game is the best negated
  value over all post-opening states (`value_Icc_eq_best_after_opening`).
- Consequently, safety for both owners at the opening-1 root is **not** a proof of the full draw:
  player 1 needs one non-losing opening, whereas player 2 must be safe against every player-1
  opening. Previous basin experiments address a valuable one-opening subproblem only.
- The certificate checker independently decodes masks, checks bounded states, terminal safety,
  exact legal counter coverage at opponent nodes, legal owner moves, child containment, uniqueness,
  and strict decrease. Its Lean soundness theorem recursively derives `CanAvoidLoss`. An accepted
  certificate is therefore rigorous one-sided evidence; solver annotations alone are not.

### Current external computational status

- The CGTC III abstract by Bernhard von Stengel reports exact optimal play through `N = 28` and the
  expected draw pattern whenever `N` or `N+1` is divisible by four. No proof or counterexample was
  found in the initial current-status search. Repository code reproduces the original paper's exact
  table only through `N = 20`.

### Failed-proof warning

- Any proposed general theorem based only on even total must be tested on arbitrary counter sets:
  interval structure is likely essential. Likewise, a proof of player-1 non-loss alone cannot be
  presented as a draw proof.

## Active unit: test a broad structural draw hypothesis

- Timestamp: **2026-08-07 23:48:18 EDT**.
- Intended experiment: independently enumerate small finite counter sets of even total, compute the
  exact Catch-Up value, and test whether a natural `max counter ≤ half total` condition suffices for
  a draw. If false, extract minimal counterexamples and infer what interval-specific property is
  missing.
- Exact recovery command/next action: run a self-contained read-only JavaScript minimax enumeration
  over subsets of a small initial interval; cross-check any reported example with the Lean
  `CatchUp` evaluator or a second independent recurrence before treating it as evidence.
- Do not infer anything about the interval conjecture from failure on arbitrary sets; the purpose is
  only to accept or reject a possible proof generalization.

### Result — 2026-08-07 23:50:51 EDT

- A first attempted `node -e` command failed because `node` is not on this shell's `PATH`; no data
  were produced by that command.
- An independent Python recurrence tested all subsets of `{1,...,12}` satisfying even total and
  `2 * max ≤ total`: 1,954 sets were eligible and 390 were not draws. The smallest reported example
  was `{3,4,5}`, total 12, with a player-1 win.
- Extending to every even-total subset of `{1,...,15}` found 2,585 player-1 wins, 13,782 draws, and
  16 player-1 losses. Thus neither even total nor even total plus a no-dominant-counter condition is
  remotely sufficient. Interval structure is essential. These results are computational and were
  not separately Lean-checked because they only refute a prospective generalization, not the target
  conjecture.
- Exact commands and full output remain in the task transcript; the recurrence matches the formal
  transition: same-player recursion for `x < deficit`, negated child otherwise.

## Active unit: residue-specific common opening turns

- Timestamp: **2026-08-07 23:50:51 EDT**.
- Intended experiment: correct the earlier pooled comparison by intersecting complete first-owner
  turns separately along the two invariant `+4` chains, initially `N = 7,11` and `N = 8,12`, with
  special attention to the player-2 obstruction after `1,2,5`.
- Why: `N → N+4` preserves the residue class. The absence of one fixed sequence common to
  `7,8,11,12` does **not** refute a residue-specific phase protocol.
- Exact recovery action: parameterize or minimally adapt
  `scripts/catch_up/CommonOpeningTurnMain.lean` so discovery and validation sizes are supplied as
  arguments; run the two chains separately; report every opponent counter with an empty sequence
  intersection. Do not claim a parametric rule until the sequences are explained symbolically and
  checked beyond a single pair.

### Result — 2026-08-07 23:57:00 EDT

- `scripts/catch_up/CommonOpeningTurnMain.lean` was minimally parameterized to accept a nonempty
  list of sizes on the command line. The no-argument behavior remains the previous pooled
  `[7, 8, 11, 12]` run. The modified file compiles and both requested runs completed.
- Exact recovery commands:
  `lake env lean --run scripts/catch_up/CommonOpeningTurnMain.lean 7 11` and
  `lake env lean --run scripts/catch_up/CommonOpeningTurnMain.lean 8 12`.
- Every listed opponent reply has a nonempty common complete-turn intersection within each residue
  chain for both owners. Therefore the previous pooled failure does not survive the mathematically
  appropriate split by residue class.
- The sharp pooled obstruction after opening `1`, reply `2`, and player-2 reply `5` becomes:
  - for `N = 7, 11`, the only common player-2 complete turn is `[3, 4]`;
  - for `N = 8, 12`, common player-2 turns include `[4]`, `[6]`, `[7]`, `[8]`, `[3, 6]`, and
    `[3, 7]`.
  Thus a particularly small residue-dependent choice is `[3,4]` on the `N ≡ 3 (mod 4)` chain
  and `[4]` on the `N ≡ 0 (mod 4)` chain.
- This is discovery evidence about one opening phase only. It does not establish a parametric
  invariant, later-turn closure, player-2 safety against every opening, or the conjecture.
- Full output remains in the task transcript. The parameterization is the only tracked source edit
  in this continuation; no commit or staging action was performed.

## Corrected external frontier and solver trust boundary — 2026-08-07 23:57:00 EDT

- The literature frontier is **at least `N = 34`**, not `N = 28`: an official LSE seminar
  abstract dated 22 February 2019 reports von Stengel's exact optimal-play computation through
  `N = 34`, confirming draws at all parity-eligible sizes through that point. Therefore `N = 31`
  and `N = 32` are not novel computational targets.
- A 2023 paper by an original coauthor still describes Catch-Up as having no analytical solution
  and only empirical evidence for the draw pattern. No later proof or counterexample has yet been
  located in this audit.
- Existing packed tables in `/private/tmp` for `N = 23, 24, 27, 28` were independently scalar-
  verified by the available executable. Fresh packed solves at those sizes report every opening as
  a draw; representative solve times are 0.207 seconds at `N=23` and 8.970 seconds at `N=28`.
- The executable's self-test cross-checks packed transitions, terminal and turn semantics,
  completed-turn enumeration, three independent solver formulations on all internally consistent
  states through `N=10`, random `N=12` states, and the published `N=3..20` outcomes.
- These are strong computational checks, but the executable and tables are not Lean-verifiable
  certificates and are not formally connected to `CatchUp.value`. They cannot alone certify a
  counterexample or theorem.
- The experimental forcing basin also has a trust gap: `basinValid` checks recurrence against the
  same solver-selected edges, while target certificates certify only the leaves. A rigorous
  root-to-target result needs either a proof-producing partial-strategy DAG checker or a complete
  certificate checked by the existing Lean soundness theorem.

## Updated best next actions

1. Test the newly suggested natural transfer family exhaustively on the next pairs: draw-valued
   positions with at least four old counters remaining appear to stay draw-valued under the
   existing `addFourCounters` lift for `7 → 11` and `8 → 12`. Determine exact quantifiers,
   reachability assumptions, and all failures at `11 → 15` and `12 → 16` before proposing a Lean
   theorem.
2. In parallel, prove a small first-move wrapper theorem: one certified non-losing opening for
   player 1 plus certified player-2 safety after every opening implies the full game is a draw.
   This closes a logical packaging gap independently of whether the parametric reduction succeeds.
3. If the transfer family survives, mine residue-specific witnesses and formulate the weakest
   one-sided relation stable under legal moves. If it fails, preserve minimal boundary failures and
   use the already proved at-most-three-old-counter endgame families to absorb them.

## Interim handoff report — 2026-08-07 23:57:00 EDT

The conjecture remains unresolved, but the latest experiment made real progress on the original
`N → N+4` target: the alleged fixed-turn obstruction was an artifact of mixing the two invariant
residue chains. Separate exhaustive searches at `7,11` and `8,12` find a common safe complete first
turn for every tested reply and both owners. This is not yet a reduction theorem. The strongest
next test is a natural state family suggested by exact comparison: draw positions with at least
four old counters remaining appear to lift from `N` to `N+4`, while the known failures lie in the
small endgame already targeted by formal three- and four-counter lemmas. Separately, the formal
development needs an all-openings player-2 wrapper before any opening-1 certificate can imply the
full draw. The historical computation already reaches `N=34`, so recomputing `31,32` would verify
infrastructure rather than produce a novel result.

## Active unit: reachable-state draw-lift falsification at `11 → 15`

- Timestamp: **2026-08-07 23:58:32 EDT**.
- Intended experiment: run the exact memoized comparison at `N=11`, then determine whether every
  *reachable cached* draw state with at least four remaining old counters is still a draw after
  adding counters `12,13,14,15` at the same deficit. This directly tests the natural family that
  survived exhaustive `7 → 11` and `8 → 12` comparison.
- Scope warning: the cache contains every state reached recursively after every legal opening, but
  not necessarily every syntactically valid `Position`. Survival is evidence for choosing a
  theorem, not a theorem.
- Exact recovery command:
  `lake env lean --run scripts/catch_up_compare.lean 11`.
- If the current report's capped failure list is insufficient, add a read-only analysis/reporting
  field that counts outcome-changing draw failures by remaining-card count; do not alter solver
  semantics. If `11 → 15` already refutes the family, extract all minimal failures before trying
  `12 → 16`.

### Result — 2026-08-08 00:00:55 EDT

- The exact comparison completed twice after extending only its reporting fields. The solver
  recurrence was not changed. It visited 9,590 small states and 230,623 large states; every lifted
  small cached state was present in the large cache.
- The proposed family is false: of 3,965 reachable cached draw states with at least four old
  counters, 3,957 remain draws and 8 become wins for the player to move after the four-counter
  lift.
- All eight counterexamples were extracted:
  - `([5,6,7,8,9], d=11)`;
  - `([1,2,5,6,7], d=11)`;
  - `([2,5,6,8], d=11)`;
  - `([4,5,7,9], d=11)`;
  - `([1,5,7,8], d=11)`;
  - `([3,4,5,9], d=7)`;
  - `([1,5,6,9], d=11)`;
  - `([1,4,6,7], d=10)`.
- The failure is narrow but not explained solely by maximal deficit: two exceptions have deficits
  7 and 10. No failure has six or more old counters. Thus “at least six old counters” is the next
  obvious empirical boundary to test, but it has not yet earned theorem status.
- Modified artifact: `scripts/catch_up_compare.lean` now reports the exact count and full list of
  outcome-changing draw lifts with at least four old counters. It compiles and reproduces the
  independent-reference check through `N=8` before each comparison.

## Active unit: test the six-old-counter boundary at `12 → 16`

- Timestamp: **2026-08-08 00:00:55 EDT**.
- Intended experiment: run the same exhaustive reachable-cache comparison for `12 → 16`; inspect
  every outcome-changing draw lift with at least four old counters and determine whether any has
  six or more. This is a falsification test for a possible bounded endgame-exception formulation,
  not a proof.
- Exact recovery command:
  `lake env lean --run scripts/catch_up_compare.lean 12`.
- Stop and redesign the report if the full exception list becomes too large; preserve exact counts
  before moving to a later induction pair.

### Result — 2026-08-08 00:02:19 EDT

- The comparison completed in about 25 seconds including compilation, visiting 21,590 small states
  and 499,184 large states. Every lifted small cached state was found.
- Of 9,587 reachable cached draw states with at least four old counters, 9,574 remain draws and 13
  become wins. Thus the four-counter threshold again fails.
- Every one of the 13 failures has exactly four or five old counters; no failure has six or more.
  Their deficits vary (`7`, `8`, `9`, `11`, and `12`), so a simple deficit cutoff is not the
  explanation.
- Combined with `11 → 15`, the evidence now suggests a bounded exceptional endgame of at most five
  old counters. This remains empirical and may fail at the next pair.
- Exact command: `lake env lean --run scripts/catch_up_compare.lean 12`. Full exception output is
  preserved in the task transcript; the reporter remains the modified artifact.

## Active unit: test the six-old-counter boundary at `15 → 19`

- Timestamp: **2026-08-08 00:02:19 EDT**.
- Intended experiment: extend the exact reachable-cache comparison one induction step along the
  `N ≡ 3 (mod 4)` chain. First modify reporting to count draw lifts with at least six old counters
  and cap printed four-counter exceptions, avoiding unbounded output. Then run `15 → 19`.
- Exact recovery command after the reporting change:
  `lake env lean --run scripts/catch_up_compare.lean 15`.
- If any six-or-more-card draw becomes non-draw, extract minimal examples and abandon the bounded-
  five endgame hypothesis. If none do, test `16 → 20` before considering a conjectural family.

### Result — 2026-08-08 00:05:13 EDT

- The comparison completed in roughly two minutes, visiting 230,623 small states and 4,875,621
  large states. Every lifted small state was found; both interval games have draw value.
- The six-counter boundary fails decisively: only 105,712 of 106,633 reachable cached draw states
  with at least six old counters remain draws. There are **921 outcome-changing failures** in this
  allegedly safe region.
- Examples occur with 6, 7, 8, and 9 old counters and widely varying deficits. One lifted draw even
  becomes a loss rather than a win, so no one-sided monotonicity survives either.
- This refutes the entire proposed route “draw value plus a fixed lower bound on old-card count is
  preserved by `addFourCounters`.” Testing `16 → 20` is no longer warranted.
- The result does **not** refute a strategy-specific `N → N+4` simulation. It shows that the
  invariant must remember strategic phase/history or a restricted forcing relation; raw minimax
  value and card count are too coarse.
- Exact command: `lake env lean --run scripts/catch_up_compare.lean 15`. The report records exact
  six-card counts and 32 representative failures; complete aggregate counts and output are
  preserved in the task transcript.

## Active unit: prove the all-openings draw bridge

- Timestamp: **2026-08-08 00:05:13 EDT**.
- Intended theorem: for nonempty `S`, prove that `CatchUp.value S = .draw` iff (i) player 1 can
  avoid loss after at least one legal opening and (ii) player 2 can avoid loss after every legal
  opening. This closes a genuine logical gap in the certificate program and is independent of the
  failed transfer family.
- Exact recovery action: inspect `Outcome.best_ne_loss_iff`, `Outcome.best_ne_win_iff`,
  `can_avoid_loss_iff_value`, and `value_eq_best_after_opening` in
  `FormalConjectures/Paper/CatchUpConjecture.lean`; develop the proof one tactic at a time in a
  scratch file; add the theorem to the main formalization only when warning-strict compilation
  succeeds with no `sorry`.
- Do not use the opening-1 basin as evidence for the universal player-2 clause. This theorem merely
  packages the exact obligations; finite or parametric certificates must still discharge them.

### Result — 2026-08-08 00:07:56 EDT

- Added and compiled the fully proved API theorem
  `value_eq_draw_iff_can_avoid_loss_after_opening` in
  `FormalConjectures/Paper/CatchUpConjecture.lean`. It states the exact existential player-1 and
  universal player-2 opening obligations for every nonempty finite counter set.
- Added the helper `Outcome.eq_draw_iff`: an outcome is a draw iff it is neither a loss nor a win.
- The proof uses only the existing formally proved opening decomposition, `Outcome.best` lemmas,
  and `can_avoid_loss_iff_value`; it contains no `sorry` and does not rely on a solver.
- A direct Lean compile succeeds. The only emitted `sorry` warning is the repository's pre-existing
  open conjecture itself, not either new theorem.
- Contributor lesson preserved: initially placing the new `[simp]` helper before the existing
  `Outcome.best` proofs altered their later simplification behavior. Moving it after those proofs
  restored proof stability. Lean declarations and simp sets are processed top-to-bottom.

## Active unit: proof-producing partial-strategy certificates

- Timestamp: **2026-08-08 00:07:56 EDT**.
- Intended work: extend the independent certificate checker with target leaves justified by a
  supplied Lean theorem. Reuse the existing DAG structures; accept `.terminal` as a partial leaf
  only when a Boolean target recognizes the decoded state and a `TargetSound` hypothesis proves
  every recognized valid state satisfies `CanAvoidLoss`.
- Why this is next: it closes the trust gap between solver-selected forcing basins and the already
  proved endgame targets. Unlike more value-lift mining, it produces reusable rigorous evidence.
- Exact recovery action: read `CertificateChecker.lean`, `CertificateSoundness.lean`,
  `StrategyExtraction.lean`, and `ExplicitTargetSoundness.lean` completely; add definitions first,
  then prove soundness by adapting the existing decreasing-cardinality recursion one branch at a
  time. Do not alter the existing full checker.
- First finite target after generic soundness: generate a shared player-2 partial DAG containing
  every opening root at `N=11` and one player-1 DAG for a safe opening, using a proof-backed small-
  state target. Combine the checked results through the new draw bridge. Any generated artifact
  must be preserved with an exact reproduction command.

### Generic checker result — 2026-08-08 00:11:34 EDT

- Added `scripts/catch_up/PartialCertificateChecker.lean`. It leaves the ordinary checker and data
  structures unchanged, and defines `PartialNodeValid`, `PartialDAGValid`, and
  `checkPartialCertificate` for proof-backed target leaves.
- Added `scripts/catch_up/PartialCertificateSoundness.lean`. Its fully proved recursive theorem says
  every position contained in an accepted partial DAG satisfies `CanAvoidLoss`, provided a
  `TargetSound` proof covers every recognized bounded state. A root-level checker theorem and an
  arbitrary-contained-state theorem are both supplied.
- The proof trusts neither solver outcomes nor basin edges. Ordinary nodes retain exact legal-move
  coverage and strictly decreasing child checks; target nodes close only through the supplied Lean
  theorem.
- `lake --wfail build CatchUpResearch` succeeds for all 8,078 jobs. The first run caught a namespace
  linter warning in the earlier parameterized executable `main`; adding the same local linter
  exemption used by neighboring `*Main.lean` files fixed it.
- No `sorry`, commit, staging, push, or GitHub action was introduced.

## Active unit: extract and check an all-openings partial certificate at `N=11`

- Timestamp: **2026-08-08 00:11:34 EDT**.
- Intended work: implement an untrusted target-stopping extractor that can traverse several roots
  into one shared DAG. Define a proof-backed small-state target using the exact Boolean
  `CanAvoidLoss` classifier only below a chosen remaining-card limit; prove its `TargetSound`
  property. Then solve `N=11`, extract one player-1 root and every player-2 opening root, and run the
  independent partial checker.
- Exact recovery action: add `PartialStrategyExtraction.lean` by copying the existing extractor's
  traversal and checking `target state` before branch selection; add target soundness separately;
  add executable regressions that report node counts and require every requested root to be
  contained. Start with remaining-card limit 6.
- A successful runtime checker result is rigorous evidence only if the target-soundness theorem and
  checker-soundness theorem instantiate together. To produce a durable kernel theorem for fixed
  `N=11`, the generated certificate must subsequently be serialized or otherwise reflected into a
  closed Lean term.

### Execution checkpoint — 2026-08-08 00:14:38 EDT

- The target-stopping shared-cache extractor, proof-backed six-counter target, and executable
  regression now compile in a warning-strict `CatchUpResearch` build.
- Exact command now being launched:
  `lake env lean --run scripts/catch_up/PartialCertificateMain.lean 11 6`.
- The run must cross-check the complete solver graph, independently accept both partial DAGs, and
  confirm that all 11 player-2 opening roots occur in the shared DAG. Preserve node counts and any
  failure message before changing the cutoff.

### Interrupted validation attempt — 2026-08-08 00:17:32 EDT

- The first command was manually interrupted after about 2.5 minutes while still inside
  `ExactSolver.outputAgreesWithReference`; extraction and certificate checking had not begun.
- Cause: that regression performs list-based child containment across the complete graph and
  recursively recomputes reference values for every node. At `N=11` this is deliberately redundant
  but asymptotically unsuitable.
- This does not weaken the certificate argument: the solver and extractor are untrusted inputs, and
  the accepted partial DAG independently checks exact moves, transitions, opponent coverage,
  progress, and proof-backed target leaves. The executable will retain
  `referenceAgreesThrough 8` as a solver regression, then omit the unnecessary complete-output
  cross-check at `N=11`.
- Revised exact recovery command after that single executable change remains:
  `lake env lean --run scripts/catch_up/PartialCertificateMain.lean 11 6`.

### Accepted runtime certificates — 2026-08-08 00:18:56 EDT

- The revised exact command completed in 6.45 seconds.
- The solver produced 19,169 absolute states; the independent reference regression passed through
  `N=8`.
- The proof-backed partial checker accepted:
  - an 83-node player-1 DAG rooted after opening `1`;
  - one 124-node player-2 DAG containing all 11 legal post-opening roots.
- Every player-2 opening root was independently confirmed present. Because the generic target-
  soundness theorem and partial-checker soundness theorem are fully proved, these accepted DAGs are
  rigorous runtime certificates of the required one-sided facts, conditional only on retaining the
  concrete certificate data.
- Exact output:
  `N=11, target limit=6: partial certificates accepted; player 1 nodes=83; player 2 nodes=124;
  covered player-2 roots=11`.

## Active unit: serialize the `N=11` certificates and prove the full draw in Lean

- Timestamp: **2026-08-08 00:18:56 EDT**.
- Intended work: emit deterministic Lean literals for the two accepted DAGs, add them as a
  generated research artifact, prove both checker equalities with kernel evaluation, derive
  `CanAvoidLoss` at opening `1` for player 1 and at every opening for player 2, and apply
  `value_eq_draw_iff_can_avoid_loss_after_opening` to prove `value (Finset.Icc 1 11) = .draw`.
- Exact recovery action: add a deterministic formatter to the existing executable (or a separate
  emitter) that prints Lean source for both DAGs; capture stdout, then add the generated file using
  `apply_patch` only. Verify the opening-state decoder for every `x ∈ Icc 1 11`; do not trust the
  solver's `openingRoots` list as a formal bridge.
- Required final checks: no `sorry` in any new research module, warning-strict `CatchUpResearch`
  build, ordinary `decide` if feasible, and explicit theorem use of partial-certificate soundness
  plus the all-openings draw bridge.

### Formally checked full draw at `N=11` — 2026-08-08 00:25:25 EDT

- Added `scripts/catch_up/N11Certificate.lean` containing the deterministic 83-node player-1 DAG
  and 124-node all-openings player-2 DAG as literal Lean data.
- Lean proves both closed checker equalities with `native_decide`. This tactic is confined to a
  `@[category test]` finite certificate artifact under `scripts/`; it is not used in
  `FormalConjecturesForMathlib`. The logical soundness theorem, target safety bridge, opening
  decoding, root containment, and final game theorem are ordinary Lean proofs.
- Formally established theorem:
  `CatchUpSearch.N11Certificate.value_Icc_eleven :
   CatchUp.value (Finset.Icc 1 11) = .draw`.
- The proof does not trust solver values or the solver's opening table. It finite-checks that each
  explicit encoded opening state decodes to the formal post-opening position and occurs in the
  player-2 DAG, derives one-sided safety through `check_partial_certificate_sound`, and applies the
  generic all-openings draw bridge.
- Direct module compilation succeeds without output. `lake --wfail build CatchUpResearch` succeeds
  for all 8,082 jobs.
- Reproduction commands:
  - regenerate/inspect data:
    `lake env lean --run scripts/catch_up/PartialCertificateMain.lean 11 6 --emit`;
  - verify the formal artifact:
    `lake env lean scripts/catch_up/N11Certificate.lean`;
  - verify the research library:
    `lake --wfail build CatchUpResearch`.
- SHA-256 of `N11Certificate.lean` at this checkpoint:
  `4fe0d76485aa022074386758ea0991e8c0cf3a1dd43331c16d394ebd2bb9a5da`.

## Active unit: repeat the complete formal certificate at `N=12`

- Timestamp: **2026-08-08 00:25:25 EDT**.
- Intended work: run the same proof-backed six-counter extraction for `N=12`, preserve node counts,
  serialize the accepted DAGs if they remain small, and prove the full all-openings draw with the
  same trust boundary.
- Exact recovery command:
  `lake env lean --run scripts/catch_up/PartialCertificateMain.lean 12 6 --emit`.
- Do not begin serialization unless the runtime partial checker accepts both DAGs and confirms all
  12 player-2 opening roots. Keep the `N=11` artifact untouched while validating the next size.

### Formally checked full draw at `N=12` — 2026-08-08 00:28:00 EDT

- The runtime checker accepted a 170-node player-1 opening-1 DAG and one 228-node player-2 DAG
  containing all 12 opening roots; the complete solver graph had 43,168 states and the independent
  recurrence regression passed through `N=8`.
- Added `scripts/catch_up/N12Certificate.lean` with both literal DAGs, native-decided closed checker
  equalities, finite opening decoding/containment proofs, one-sided safety theorems, and the full
  theorem
  `CatchUpSearch.N12Certificate.value_Icc_twelve :
   CatchUp.value (Finset.Icc 1 12) = .draw`.
- Direct module compilation and `lake --wfail build CatchUpResearch` both succeed; the latter now
  covers all 8,083 jobs.
- Reproduction commands mirror `N=11` with game size `12`. SHA-256 of `N12Certificate.lean`:
  `8779dfb7010cbed7719ebbb3b383cf82e63833d46d545be830feed8739ba07d9`.
- These two complete finite certificates repair the previous opening-1 scope problem at `N=11,12`.
  They do not themselves establish an `N → N+4` theorem.

## Active unit: replace the recursive top-four target by a symbolic classification

- Timestamp: **2026-08-08 00:28:00 EDT**.
- Intended work: audit and prove, if correct, a closed parametric formula for
  `Position.value` when exactly the four counters `N+1,...,N+4` remain. This removes the current
  `isExplicitSafeTopOnly` dependence on running the full recursive classifier and resumes the
  theoretical sequence requested before a parametric forcing-basin argument.
- Exact recovery action: read `FourCounterEndgame.lean` and its executable completely; run the
  existing bounded table to confirm the proposed formula across its stated hypotheses; state the
  weakest correct theorem; prove the hardest deficit region first using `Position.value.eq_def`
  and arithmetic, one tactic at a time.
- Candidate formula to falsify before proving (for suitable `N` and `d ≤ N+4`): value is draw at
  `d=0` or `d=2`, loss for the remaining `d ≤ N+1`, and win for `N+1<d`. Do not formalize it if the
  table exposes an exception.

### Formula audit and failed brute-force proof — 2026-08-08 00:34:31 EDT

- `FourCounterEndgameMain.lean 20` confirms the candidate profile for every displayed `N ≥ 4` and
  every relevant deficit through `N+4`. It fails at smaller `N` (for example `N=3,d=4` is an extra
  draw), so the correct lower-bound hypothesis is at least `4 ≤ N`, not `3 ≤ N`.
- Independently enumerated first-move outcomes show a rigid structure for `a=N+1 ≥ 5`:
  - at deficit 0, removing `a+1` or `a+3` enters a draw; the other two moves lose;
  - at deficit 2, only removing `a+3` enters a draw;
  - for every other deficit through `a`, all first moves lose;
  - at deficits `a+1,a+2,a+3`, taking respectively one of the counters still below the deficit
    gives the mover a win.
  Every relevant first-move child is a three-counter win or draw; none is a loss.
- A direct proof attempt unfolded `Position.value.eq_def` recursively over the four explicit
  counters and invoked `simp`/`omega`. It exceeded the default 200,000 heartbeats, then exceeded a
  locally raised 2,000,000-heartbeat budget after about one minute. The incomplete experimental
  module was removed so the worktree remains buildable.
- Conclusion: blind full unfolding is too expensive and brittle. The next proof must expose named
  three-counter child classifications or prove the owner-safety cases directly through the
  `CanAvoidLoss` API. The computational formula remains conjectural until that structured proof is
  complete.

## Active unit: derive structured top-four child lemmas

- Timestamp: **2026-08-08 00:34:31 EDT**.
- Intended work: identify the minimal exact three-counter lemmas needed for the three draw children
  and the uniform win children, then prove the hardest family explicitly. Prefer strategy-level
  `CanAvoidLoss` lemmas if exact `Position.value` classification introduces unnecessary negative
  obligations.
- Exact recovery action: use the first-move table above and the existing singleton/pair proof style
  in `ThreeCounterSafety.lean`; formulate child states with explicit Finsets and prove transitions
  using `can_avoid_loss_iff_exists_safe_move` / `can_avoid_loss_iff_forall_safe_moves`. Await the
  parallel mathematical/API audits before committing to a large case tree.

### Verified empty and singleton value formulas — 2026-08-08 00:43:30 EDT

- Added `scripts/catch_up/TopFourClassification.lean` with ordinary Lean proofs of the terminal
  formula and the exact one-counter formula:
  `value {c} d = win` for `d<c`, `draw` for `d=c`, and `loss` for `c<d`.
- The proof names the empty-position recursion equation and explicitly normalizes the attached
  singleton move list. This avoids recursively expanding unrelated game trees and makes the
  current trust boundary purely kernel-checked; no solver, `native_decide`, or `sorry` is used.
- Direct command `lake env lean scripts/catch_up/TopFourClassification.lean` succeeds.
- Next unit: prove a reusable exact two-counter formula for the consecutive/gap-bounded pairs that
  occur as children of the four-counter position, then use those results to classify the needed
  three-counter children.

### Verified exact close-pair classification — 2026-08-08 00:55:39 EDT

- `TopFourClassification.value_pair_exact` is now an ordinary, sorry-free Lean theorem. For
  `0 < p < q` and `q-p ≤ p`, it proves the complete six-region profile: win below `q-p`, draw at
  `q-p`, loss through `p`, win below `p+q`, draw at `p+q`, and loss above the total.
- An initial proof that normalized the attached two-move list directly was abandoned: despite a
  correct formula, indiscriminate nested `split_ifs` produced a large and brittle arithmetic tree.
  The replacement uses exact minimax characterizations (`some` move for win, `all` moves for loss,
  and the two non-loss/non-win obligations for draw) and compiles in about four seconds.
- Direct command `lake env lean scripts/catch_up/TopFourClassification.lean` succeeds with no
  warnings; `rg sorry` finds nothing in the module.
- Next unit: prove the four three-counter values obtained by deleting each of `a,a+1,a+2,a+3`,
  using `value_pair_exact` as the child theorem. These are the final nontrivial ingredients before
  the complete four-counter formula.

### First exact three-counter table proved — 2026-08-08 01:01:10 EDT

- Added a reusable theorem expressing any triple move in terms of `pairFormulaExact`, with the
  correct same-player versus perspective-negated branch determined by `chosen < deficit`.
- Proved `value_triple_without_first`: for `a ≥ 5`, the position on
  `{a+1,a+2,a+3}` at every `d ≤ a+3` is a win except for a draw at `d=a+2`.
- The proof records concrete winning witnesses in each region and verifies all three moves at the
  draw point; direct compilation succeeds and remains warning-free.
- Proof-engineering failure resolved: `try simp ... <;> omega` had scoped `omega` inside `try`,
  silently swallowing failed arithmetic branches. Parenthesizing `(try simp ...) <;> omega`
  restores the intended tactic sequencing.
- Next unit: prove the `{a,a+2,a+3}` table, including its genuine losing state at `d=a+2`.

### Complete exact three-counter child classification — 2026-08-08 01:04:48 EDT

- All four subsets obtained by deleting one counter from `{a,a+1,a+2,a+3}` are now classified for
  `a ≥ 5` and `d ≤ a+3`, with ordinary Lean proofs:
  - `{a+1,a+2,a+3}`: draw only at `a+2`, otherwise win;
  - `{a,a+2,a+3}`: draw at `a+1`, loss at `a+2`, otherwise win;
  - `{a,a+1,a+3}`: always win;
  - `{a,a+1,a+2}`: draw at `a+1` and `a+3`, otherwise win.
- Each theorem exhibits region-specific winning moves and proves the universal minimax obligations
  at every draw/loss point by reducing all children to `value_pair_exact`.
- `TopFourClassification.lean` is 607 lines, contains no `sorry`, and compiles warning-free.
- Next unit: derive the five-region exact value formula for the full four-counter position from
  these four child tables, then connect the result to a solver-independent top-only target.

### Parametric full top-four theorem proved — 2026-08-08 01:08:45 EDT

- Proved `TopFourClassification.value_top_four` for every `a ≥ 5` and `d ≤ a+3`:
  draw at `d=0,2`; loss at all other `d≤a`; win at `a<d≤a+3`.
- The proof records four exact first-move equations, rewrites each child through the corresponding
  three-counter theorem, and closes the final draw/loss/win regions through the minimax API.
- This is a kernel-checked parametric theorem, not bounded computation. The module contains no
  `sorry`, uses no solver or `native_decide`, and compiles warning-free in about 18 seconds.
- This proves the isolated four-counter classification needed by the proposed endgame target. It
  does not yet prove a forcing basin or an `N→N+4` reduction.
- Next unit: dispatch over all 16 subsets of the four counters and prove one sound `Option Outcome`
  classifier, then use it to replace the recursive `isExplicitSafeTopOnly` implementation.

### Solver-independent all-subsets integration — 2026-08-08 01:13:30 EDT

- Added `topSubsetValue?` and proved `top_subset_value?_sound`: every returned outcome is exactly
  `Position.value` for the decoded list. The guarded singleton/pair branches plus four triples,
  empty, and full cases cover all 16 ordered subsets.
- Replaced `FourCounterAttractor.isExplicitSafeTopOnly` with a symbolic `Option Outcome` wrapper
  guarded by `4≤N` and `state.deficit≤N+4`; it no longer imports or calls
  `CanAvoidLossClassifier`.
- Replaced its soundness proof with `top_only_outcome?_sound` followed by
  `can_avoid_loss_iff_value`. The public target name and downstream combined-target API are
  unchanged.
- `lake --wfail build CatchUpResearch` succeeds for all 8,084 jobs.

## Active unit: regression-test symbolic top-only coverage and basin behavior

- Timestamp: **2026-08-08 01:13:30 EDT**.
- Intended work: compare the new predicate with exact solved annotations on every reachable
  top-only node for representative `N≥4`, then run the existing target/certificate/basin analysis
  to detect unintended coverage changes. Treat agreement as regression evidence only; formal
  soundness already follows from the Lean theorem.
- Compatibility note: `N=3` is intentionally rejected because the symbolic theorem assumes
  `N≥4`; do not reintroduce the recursive classifier as an unmarked fallback.

### Complete-domain classifier regression passed — 2026-08-08 01:17:10 EDT

- Added `TopOnlyRegressionMain.lean`, which compares the new symbolic predicate with the old
  proof-level recursive classifier on all 16 masks, deficits `0..N+4`, both movers, and both
  protected owners, then compares against exact annotations on every reachable top-only node.
- Command
  `lake env lean --run scripts/catch_up/TopOnlyRegressionMain.lean 4 7 8 11`
  passes at all four sizes. Thus the target predicate is extensionally unchanged on the complete
  intended domain for these representatives, not merely sound on a sampled basin.
- `lake --wfail build CatchUpResearch` succeeds for all 8,085 jobs including the regression tool.
- Next experiment: run the existing forcing-basin analyzer with the new implementation to verify
  target certificate extraction and basin recurrence continue to operate end-to-end.

### Symbolic target basin integration passed — 2026-08-08 01:21:30 EDT

- Command
  `lake env lean --run scripts/catch_up/FourCounterAttractorMain.lean 4 7 8 11`
  completes for all four sizes, all four target kinds, and both owners. Target certificates and
  basin recurrences are accepted throughout.
- At the two research sizes, safe-top-only alone misses both opening-1 roots:
  - `N=8`: p1 basin 9,084; p2 basin 9,206; both roots false;
  - `N=11`: p1 basin 89,644; p2 basin 90,654; both roots false.
- Adding the proved one-old-pair family reaches both roots:
  - `N=8`: p1 basin 10,458; p2 10,592;
  - `N=11`: p1 basin 107,051; p2 107,944.
- Adding the four-counter-entry family increases target-node counts but not these basin sizes, so
  that family is currently a structural explanation/predecessor layer rather than extra reach.
- Since the new predicate agrees exhaustively with the prior classifier, these target/basin facts
  preserve the earlier experiment while removing recursive evaluation from the top-only leaf.

## Active unit: test residue-specific complete-turn protocols at the next sizes

- Timestamp: **2026-08-08 01:21:30 EDT**.
- Intended work: run the common-turn filter separately on the `N≡3 (mod 4)` chain `7,11,15` and
  the `N≡0 (mod 4)` chain `8,12,16`. A `+4` induction never crosses these classes, and earlier
  pooling created a false obstruction after reply `1,2,5`.
- Success criterion: a nonempty common complete-turn response for every first opponent counter at
  each owner, preferably with short sequences that stabilize across three sizes. Failure still
  identifies the earliest counter/residue where the current explicit basin is too narrow.

### Three-size common-turn run stopped on cost — 2026-08-08 01:31:00 EDT

- Command `lake env lean --run scripts/catch_up/CommonOpeningTurnMain.lean 7 11 15` completed the
  `N=7` discovery and `N=11` filter, then spent over ten minutes constructing/filtering the
  `N=15→19` stage without output or failure. It was interrupted cleanly with Ctrl-C.
- This is not mathematical evidence against a residue-specific protocol. It is an implementation
  cost result: the current executable rebuilds complete solved graphs and both explicit-endgame
  basins, then tests a large candidate collection sequentially.
- No result for `N=15` was recorded, and the `N≡0` three-size chain has not yet been attempted with
  this implementation.
- Next unit: profile the candidate/filter structure and reduce the higher-size query to the small
  set of already-surviving `N=7,11` sequences (especially reply counter `5`), avoiding exhaustive
  rediscovery or unnecessary whole-basin passes where possible.

### Indexed protocol filter and successful `N≡3` three-size result — 2026-08-08 01:39:30 EDT

- Replaced every repeated linear `findNode?` lookup in `CommonOpeningTurnMain.lean` with the existing
  `SolvedIndex` hash map and added graph/basin progress markers. The module compiles cleanly.
- The remaining dominant cost is full graph/basin construction: the `N=15→19` opening graph has
  4,836,541 reachable states. Once constructed, indexed candidate filtering completes promptly.
- Command `lake env lean --run scripts/catch_up/CommonOpeningTurnMain.lean 7 11 15` succeeds.
  Every listed opponent counter retains a nonempty common complete turn for both owners across all
  three sizes.
- Stable high-value examples:
  - owner p2, opponent counter 5: uniquely `[3,4]` at `N=7,11,15`;
  - owner p1, counter 5: `[4]`, `[2,4]`, `[2,6]`, and `[3,4]` remain common;
  - owner p1, counter 2: `[3]` and `[4]` remain common;
  - owner p2, counters 3 and 4: `[5]`, `[6]`, and `[7]` remain common.
- This does not prove a protocol parametrically, because basin membership still comes from finite
  solved graphs. It materially strengthens the evidence that a separate `N≡3 mod 4` controller is
  small and stable.

## Active unit: run the `N≡0 mod 4` three-size protocol test

- Timestamp: **2026-08-08 01:39:30 EDT**.
- Intended command:
  `lake env lean --run scripts/catch_up/CommonOpeningTurnMain.lean 8 12 16`.
- Primary diagnostic: whether owner p2 after opponent counter 5 retains the short response `[4]`
  through `N=16→20`, and whether every discovery counter retains at least one common turn.

### Indexed `N≡0 mod 4` three-size result, with quantifier caveat — 2026-08-08 01:57:30 EDT

- Command `lake env lean --run scripts/catch_up/CommonOpeningTurnMain.lean 8 12 16` completed.
  The `N=16→20` opening graph contained 10,258,853 reachable states; both explicit-endgame
  basins were computed exactly before candidate filtering.
- Every opponent counter carried forward from the discovery size retained a nonempty common
  complete turn for both owners through all three sizes. In particular, owner p2 after counter 5
  retains `[4]` (as well as several other responses), so the earlier pooled-residue obstruction is
  absent on the `N≡0 mod 4` chain.
- Important scope correction: `CommonOpeningTurnMain.run` sets `maximumCounter := discoveryN + 4`.
  Consequently this run checks only counters available at the discovery size (through 12); it does
  **not** quantify over the newly available counters 13…20 at the largest stage. The same caveat
  applies to the earlier `7,11,15` run, whose stored candidates cover counters only through 11.
- Therefore the exact conclusion is stability of the small-counter response table across three
  sizes, not a complete finite validation of a parametric controller. The next experiment must
  define response formulas and test them against every legal opponent counter separately at each
  size, including the growing upper range.

## Active unit: discover an all-replies residue-specific response formula

- Timestamp: **2026-08-08 02:00:42 EDT**.
- Intended work: inspect complete first-owner-turn profiles separately for old replies `y ≤ N`
  and the four new replies `y = N+1,…,N+4`, then propose a bounded-length formula for each residue
  class and protected owner.
- Success criterion: a policy whose sequence is defined for every legal reply at every test size,
  is legal, preserves the explicit-endgame forcing basin after every pick, and ends exactly when
  the owner's turn changes. A passing finite test remains discovery evidence; the next obligation
  is to replace basin membership with an algebraic invariant and Lean proof.

### Corrected profiler and small-size output — 2026-08-08 02:09:11 EDT

- Added warning-clean `scripts/catch_up/AllReplyTurnMain.lean`. It enumerates `firstOwnerStates`
  afresh at each size, so it cannot omit validation-only counters, and prints a shortest complete
  basin-preserving owner turn for every legal reply.
- Command `lake env lean --run scripts/catch_up/AllReplyTurnMain.lean 7 8 11 12` passes. The dominant
  response is the adjacent counter `y-1`, ending at deficit zero; the small number of exceptions
  are the prospective phase boundaries rather than evidence for one universal two-move formula.
- Held-out all-reply profiles for `N=15` and `N=16` are running independently. Their top-counter
  cases will test whether the exceptional patterns shift predictably with `N`.

## Parallel unit: retest the at-least-four-old draw-lift family

- Timestamp: **2026-08-08 02:09:11 EDT**.
- Intended command: `lake env lean --run scripts/catch_up_compare.lean 11 12`.
- Hypothesis under test: every solver-reachable draw state with at least four remaining old
  counters stays a draw after adjoining `N+1,…,N+4`. This held exhaustively in the cached state
  sets for `N=7,8`; failure at `N=11` or `12` will reject it as the current reduction family.
- This comparison is exact finite evidence from the memoized recurrence, independently
  cross-checked only through `N=8`; it is not a Lean proof of a parametric statement.

### Four-old threshold refuted; six-old threshold survives — 2026-08-08 02:10:17 EDT

- Command `lake env lean --run scripts/catch_up_compare.lean 11 12` completed.
- At `N=11`, only 3,957 of 3,965 cached draw states with at least four old counters remain draws
  after adding four counters. At `N=12`, the count is 9,574 of 9,587. Thus the proposed
  at-least-four family is false and must not be formalized.
- Every cached draw state with at least six old counters did remain a draw:
  `2,308/2,308` at `N=11` and `6,843/6,843` at `N=12`. The same threshold also had no failures in
  the earlier `N=7,8` reports.
- The six-old condition is now a candidate natural reduction family, not a theorem. It needs a
  held-out higher-size test and, if it survives, a strategy relation explaining why six old
  counters suffice; cardinality alone may still fail later or outside solver-reachable caches.
- Held-out command now running: `lake env lean --run scripts/catch_up_compare.lean 15`. Primary
  diagnostic: `drawsRemainDrawsAtLeastSix / smallDrawStatesAtLeastSix`; any strict inequality
  rejects the candidate in its current form.

### Six-old threshold refuted at the held-out size — 2026-08-08 02:12:30 EDT

- Command `lake env lean --run scripts/catch_up_compare.lean 15` completed. Of 106,633 cached draw
  states with at least six old counters, only 105,712 remain draws after adjoining counters
  16…19. Thus 921 failures refute the six-old family decisively.
- Failures include positions with six, seven, eight, and nine remaining old counters, so this is not
  a small endgame-only leak. Raw cardinality is not the invariant needed for a parametric lift.
- The viable proof route must be strategy-specific: old moves should be matched against a chosen
  safe small-game move, while new top moves enter a bounded phase or a proved endgame family.

### Corrected all-reply profile at `N=15` — 2026-08-08 02:12:30 EDT

- `lake env lean --run scripts/catch_up/AllReplyTurnMain.lean 15` completed in about six minutes and
  covers all replies through the actual game size 19.
- New-reply shortest turns for owner p1 are `16→[15]`, `17→[5,14]`, `18→[3,14]`,
  `19→[3,15]`; for owner p2 they are `16→[15]`, `17→[3,14]`, `18→[5,14]`,
  `19→[3,15]`.
- These are exact basin-preserving complete turns, but shortest-selection remains unstable and is
  not itself a parametric policy. The `N=16` held-out profile is still running.

### Corrected all-reply profile at `N=16` — 2026-08-08 02:23:45 EDT

- `lake env lean --run scripts/catch_up/AllReplyTurnMain.lean 16` completed in about 13m45s and
  covers every reply through actual game size 20.
- New-reply shortest turns for owner p1 are `17→[16]`, `18→[3,6,8]`,
  `19→[2,3,5,6,7]`, `20→[3,16]`; for owner p2 they are `17→[16]`,
  `18→[6,11]`, `19→[3,7,8]`, `20→[3,16]`.
- The top replies are all covered, but the shortest representative can grow to five picks and is
  visibly unstable across sizes. This rejects shortest-path selection as a credible bounded
  parametric controller; it does not refute a different finite-phase simulation.

## Active unit: solve the old-matched/new-stuttering product simulation

- Timestamp: **2026-08-08 02:23:45 EDT**.
- Intended work: pair a safe small state with a large state having the same remaining old mask.
  A large old-counter move advances both states by that counter; a large new-counter move stutters
  the small state. At large owner nodes choose one recursively safe transition; at large opponent
  nodes require every transition. Stop only at a proof-backed explicit-endgame target or a directly
  safe terminal state.
- Why this is closer to the theorem: it chooses the small safe strategy jointly with the large
  implementation instead of comparing two arbitrary extracted optimal strategies. If the opening
  pair lies in this product basin, its visited `(top mask, mover alignment, deficit offset)` shapes
  are genuine candidates for a bounded `FourLift` relation.
- This remains discovery computation until the transition obligations and leaf soundness are
  re-expressed and proved in Lean without trusting solver annotations.

### First product result and exact residue-0 obstruction — 2026-08-08 02:28:30 EDT

- `lake env lean --run scripts/catch_up/SimulationBasinMain.lean 7 8` completed after the new
  warning-clean product solver was added.
- For `7→11`, both protected-player opening-1 root pairs are in the product basin. One
  deterministically extracted witness still has 227 phase signatures for p1 and 187 for p2
  (60 and 56 mover/top-mask shapes), so arbitrary first-choice extraction does not yet reveal a
  small relation.
- For `8→12`, both roots are outside the simple product basin. A locally first obstruction for
  each stays at full top mask 15, aligned movers, and deficit offset zero while consuming only old
  counters, eventually reaching a small child that is not safe for the matched strategy.
- Interpretation: exact same-old-move matching is too restrictive even before a top counter is
  chosen. A successful simulation must permit a different large owner move (possibly proactive use
  of a top counter) while relating it to the selected small strategy. The failure is of this
  relation, not of non-loss at either root.
- Next validation: run the same product recurrence at `11→15` and `12→16` to learn whether
  success/failure is stable by residue before changing the matching rule.

### Exact old matching rejected as the uniform relation — 2026-08-08 02:38:30 EDT

- The next-size product run completed after searching roughly 1.6 million pairs per owner at
  `11→15` and 4.0 million pairs per owner at `12→16`.
- All four opening-1 root pairs are outside the exact old-matched/new-stuttering product basin.
  The local obstruction traces again keep top mask 15, aligned movers, and offset zero while an
  old-only line exhausts the matched small strategy's safe children.
- The isolated `7→11` success is therefore a small-size coincidence, not residue-3 evidence for
  this relation. Stop expanding or formalizing exact old matching.
- Smallest principled enlargement: allow asynchronous matching with a bounded old-mask discrepancy.
  A large move may stutter the small state or be paired with a different safe small move; initially
  test discrepancy bounds one and two. A successful bounded relation would interpret the differing
  old counter(s) as pending bookkeeping parameters rather than as new numerical phase constructors.

## Active unit: test the one-pending-counter asynchronous relation

- Timestamp: **2026-08-08 02:42:30 EDT**.
- Added warning-clean `--async LIMIT` mode to `SimulationBasinMain.lean`. For each large move it may
  stutter the safe small state or advance it by any safe small child, while requiring the symmetric
  difference of remaining old masks to have cardinality at most `LIMIT`.
- First corrected result: `--async 1 8` puts both `8→12` opening-1 root pairs in the product basin
  (`7,978` searched pairs for p1 and `4,553` for p2). Thus one pending old counter repairs the exact
  matching obstruction without needing discrepancy two.
- The reported 708/473 phase signatures count every winning alternative in the memo cache, not one
  selected witness. Next: validate bound one at `N=7,11,12`, then extract one strategy and measure
  its actual pending-counter orientation, top-mask/mover shapes, and affine deficit offsets.

### Ownership-aligned asynchronous matching succeeds, but unrestricted replacement is too loose — 2026-08-08 03:05:03 EDT

- After correcting the recurrence so that the small game advances only when the actual players to
  move agree, `--async 1 7 8 11 12` puts both protected-player opening-1 roots in the product basin
  at every tested size. Thus the earlier success did not depend on matching moves across different
  players' turns.
- A stricter `--async-noswap 1` mode permits a pending old counter to persist or be discharged but
  not to be replaced by another pending counter. This succeeds at `7→11` and `8→12` but fails for
  both owners at `11→15` and `12→16`. Hence the one-counter relation's success relies on repeated
  replacements and does not yet give a bounded-history controller.
- Raising the no-swap discrepancy bound to two recovers `11→15`, but one owner search visits about
  9.2 million pairs. This shows that two simultaneous pending old counters have real explanatory
  power, while the no-swap state space by itself is not a compact proof invariant.

### Exact score-debt invariant and two-pending relation — 2026-08-08 03:05:03 EDT

- Added `--async-debt LIMIT`. In addition to the asynchronous transition rules, every admitted pair
  must satisfy a local exact equation: the difference between the two mover-oriented score balances
  is a signed sum of the consumed new top counters and the currently unmatched old counters. The
  signs are presently chosen afresh at each pair, so this is not yet a persistent history invariant.
- With one pending old counter this invariant is too strong: almost all base roots fail. With two
  pending counters, both protected-player roots succeed at `7→11` and `8→12`.
- The reporting layer now represents each pending counter symbolically by its side (small-only or
  large-only) and its score sign. Regression command
  `lake env lean --run scripts/catch_up/SimulationBasinMain.lean --async-debt 2 7 8` gives:
  - `7→11`: p1 root true, 1,361 selected pairs, 304 debt phases; p2 root true, 578 selected,
    248 debt phases;
  - `8→12`: p1 root true, 3,571 selected pairs, 416 debt phases; p2 root true, 1,508 selected,
    338 debt phases.
  In every case all selected pairs decompose under the symbolic invariant.
- This is the strongest simulation hypothesis so far, but it remains finite discovery evidence.
  The decisive next validation is the command
  `lake env lean --run scripts/catch_up/SimulationBasinMain.lean --async-debt 2 11 12`.
  If it passes, inspect whether its phase families stabilize and formulate a solver-independent
  transition relation; if it fails, extract the first obstruction before enlarging the invariant.

### Two-pending exact-debt relation passes the next validation sizes — 2026-08-08 03:10:30 EDT

- The unchanged validation command
  `lake env lean --run scripts/catch_up/SimulationBasinMain.lean --async-debt 2 11 12` completed
  successfully. Both protected-player opening-1 roots are in the relation at both lifts:
  - `11→15`: p1 searched 1,000,035 pairs, selected 47,635, 745 debt phases; p2 searched
    737,758, selected 30,034, 641 debt phases;
  - `12→16`: p1 searched 3,064,360 pairs, selected 122,145, 878 debt phases; p2 searched
    1,936,475, selected 56,024, 730 debt phases.
- Every selected pair is reported with a decomposition (`decomposed=selected`) in all four runs.
  This checks that the symbolic reporter agrees with the search predicate, but it is not an
  independent validation because the recurrence already rejects pairs without some decomposition.
  Together with `7→11` and `8→12`, one fixed relation succeeds for the first four tested
  parity-eligible base sizes and both protected players.
- These sizes are not perfectly held out: the earlier `11→15` no-swap experiment helped motivate
  discrepancy bound two. The exact signed-debt restriction was introduced afterward, so this is
  useful out-of-sample evidence for that restriction but should be called validation rather than a
  clean held-out test.
- The current predicate also chooses signed decompositions independently at successive states. Its
  established interpretation is only that every score gap belongs to a bounded signed-sum family;
  it does not yet track a persistent historical owner for each consumed or pending counter.
- This materially supports a parametric `N↦N+4` simulation, but is not yet a proof. The number of
  extracted phase signatures still grows with `N`; the next gate is to determine which fields are
  merely numeric parameters and to replace solver-selected witnesses by a small list of symbolic
  transition templates. Do not promote the finite basin result to a theorem before that closure
  argument and its Lean soundness proof exist.

### Edge-template audit rejects the local-debt phases as a compact controller — 2026-08-08 03:27 EDT

- Instrumented the selected witness without changing the forcing recurrence. Each parameter-free
  edge template records top-mask change, movers relative to the protected owner, old/top large
  action, stutter/same/different small action, discrepancy change, pending-set change, and local
  debt-ambiguity buckets.
- Smallest rerun
  `lake env lean --run scripts/catch_up/SimulationBasinMain.lean --async-debt 2 7` remains root true
  for both owners, but the chosen witnesses are not compact:
  - p1 uses 548 edge templates across 1,361 selected pairs;
  - p2 uses 429 edge templates across 578 selected pairs.
- Those raw template counts are intentionally over-fragmented by top masks, mover flags, and
  ambiguity buckets; they rule out enumerating the observed templates verbatim, not the generic
  existential relation by themselves.
- Different-counter moves with one-for-one pending-counter replacement are among the most frequent
  templates. Local signed-debt ambiguity is limited in this run (836/1,361 p1 states and 354/578 p2
  states have a unique decomposition; every other selected state has two to four), so the main
  source of complexity is the freely changing pending identity rather than a huge number of equal
  signed-sum representations.
- Stop treating the locally re-guessed debt phases as prospective theorem cases. The next
  parametric experiment must carry a persistent ledger in the cache key: actual mover signs for
  consumed top counters and identity/side/consuming-player data for pending old counters. Begin by
  rejecting incompatible resolutions; add an explicit residual token only if a concrete failure
  demonstrates that it is necessary.

### Persistent same-owner ledger fails at the smallest lift — 2026-08-08 03:33 EDT

- Added warning-clean `--async-ledger LIMIT`. Its cache key includes persistent ownership masks for
  consumed top counters and currently pending old counters. Ledger updates are deterministic from
  the actual parent movers. An old counter may disappear from the pending set only when both games
  assign it to the same player; a cross-owner resolution, which would leave residual `±2x`, is
  rejected.
- Command `lake env lean --run scripts/catch_up/SimulationBasinMain.lean --async-ledger 2 7` gives
  `ledgerRoot=false` for both protected players even though the broader local-debt roots are true:
  - p2: 243 ledger states, 63 winning, 242 state pairs, maximum two ledger labels per pair;
  - p1: 199 ledger states, 64 winning, 182 state pairs, maximum three ledger labels per pair.
- This refutes the strongest bounded-history candidate in its present form. It does not refute the
  large-game strategy or the local existential score filter. Next extract the first failed branch
  and distinguish: cross-owner resolution, discrepancy overflow, or failure of the underlying
  forcing child. Add at most one explicit residual token only if the obstruction specifically
  requires `±2x`; do not introduce an unbounded numeric debt.

### Persistent ledger succeeds with six pending old counters at `7→11` — 2026-08-08 03:36 EDT

- Obstruction traces show that bounds two through four encounter both discrepancy overflow and
  forced-looking cross-owner `±2x` closures. These traces follow one failing line and do not by
  themselves prove the closure is globally unavoidable.
- Removing the discrepancy restriction (`LIMIT=7`) makes the same-owner persistent ledger root true
  for both players, so residual historical tokens are not inherently necessary.
- Threshold search with unchanged code gives:
  - `LIMIT=5`: p2 true, p1 false;
  - `LIMIT=6`: p2 true and p1 true.
  Thus six is the smallest common bound found at `7→11`.
- At limit six, p2 visits 655 ledger states over 553 normalized pairs with at most five labels per
  pair; p1 visits 671 ledger states over 462 pairs with at most six labels. Persistent ownership
  therefore adds modest nondeterminism rather than the theoretical worst-case factor.
- This rescues a coherent bounded-history candidate, but bound six may be a small-size artifact.
  The next preregistered test is the unchanged command
  `lake env lean --run scripts/catch_up/SimulationBasinMain.lean --async-ledger 6 8`; both roots must
  remain true before testing larger sizes.

### No-residual ledger width grows immediately — 2026-08-08 03:38 EDT

- At `8→12`, unchanged limit six succeeds for p2 but fails for p1 with six old counters already
  pending. Limit seven succeeds for both owners.
- The minimum common bound therefore rises from six at `N=7` to seven at `N=8`. Stop enlarging this
  no-residual relation: the data strongly suggests width `N-1`, which is honest bookkeeping but not
  a fixed-width parametric `N↦N+4` controller.
- The obstruction reports repeatedly identify cross-owner synchronization with residual coefficient
  `±2x`. This now justifies the smallest controlled enlargement: at most one resolved-old residual
  token `(x, ±2)`, while returning the visible pending-counter bound to two or three. If a second
  residual becomes necessary, record the obstruction rather than immediately permitting an
  unbounded residual sum.

### One residual plus two pending counters passes both base lifts — 2026-08-08 03:39 EDT

- Added warning-clean `--async-residual LIMIT`. It carries the persistent top/pending ledger plus at
  most one resolved old counter with coefficient `±2`. A second ownership-mismatched resolution is
  rejected. Unlike `--async-ledger`, this search cannot use the old local-debt basin as a pruning
  cache because a resolved counter is absent from both masks.
- With unchanged limit two, both protected-player roots pass at both base sizes:
  - `7→11`: p2 8,799 cached ledger states, p1 19,194;
  - `8→12`: p2 30,292 cached ledger states, p1 83,166.
- The residual is central rather than exceptional: most cached states use it. Nevertheless the
  history shape is uniformly bounded by four top-owner bits, signs for at most two visible pending
  counters, and one `(counter, ±2)` token.
- Provenance before the next-size run: branch `codex/catchup-experiment`, HEAD
  `0b67426227811c55db98358c95e99ca5c4465e54`, SHA-256 of
  `SimulationBasinMain.lean` is
  `b7ce568869bc8d60042841e9eb190dae00a9a50fdfb6bae54613fc575e91fa55`.
- Next preregistered command:
  `lake env lean --run scripts/catch_up/SimulationBasinMain.lean --async-residual 2 11`.
  Success requires both owners `residualRoot=true` with no source change.

### One-residual relation passes `11→15` unchanged — 2026-08-08 03:45 EDT

- The preregistered command completed with the same source SHA-256
  `b7ce568869bc8d60042841e9eb190dae00a9a50fdfb6bae54613fc575e91fa55` and both roots true:
  - p2: 1,311,265 cached ledger states, 137,523 winning, maximum 38 ledger labels per normalized
    pair;
  - p1: 2,420,940 cached ledger states, 233,486 winning, maximum 46 labels per pair.
- This fixed relation now succeeds at base sizes 7, 8, and 11 without increasing two visible
  pending counters or the single residual allowance. It remains discovery evidence rooted after
  opening 1, not a Lean proof or a full-game draw theorem.
- Next validation is `--async-residual 2 12` with unchanged source. Based on observed growth, expect
  materially more runtime and memory; do not bundle a further size into the same process.

### One-residual relation passes `12→16` unchanged — 2026-08-08 03:59 EDT

- Command `lake env lean --run scripts/catch_up/SimulationBasinMain.lean --async-residual 2 12`
  completed with the same source SHA-256 and both roots true:
  - p2: 3,331,114 states, 310,256 winning, 2,123,553 normalized pairs, maximum 47 ledger labels;
  - p1: 8,393,471 states, 660,109 winning, 5,028,892 pairs, maximum 53 labels.
- The identical fixed-width, persistent-history relation now succeeds for both owners at all four
  tested parity-eligible bases `7,8,11,12`. This is the strongest evidence so far for an actual
  `N↦N+4` simulation rather than an unconstrained finite strategy search.
- Scope remains precise: opening 1 only; solver-guided discovery; large branches end at the proved
  explicit top-subset target or a directly checked terminal. The result does not yet prove relation
  closure for arbitrary `N`, all openings, or the full draw conjecture.
- Stop larger finite runs here. Next formal task: add a generic, solver-independent Lean theorem
  transferring `CanAvoidLoss` along any relation with aligned safe ghost steps, owner existential
  closure, opponent universal closure, and sound target/terminal leaves. Then state the residual
  ledger relation mathematically and isolate its finite symbolic closure obligations.

### Generic simulation soundness is formally proved — 2026-08-08 04:04 EDT

- Added warning-clean `scripts/catch_up/SimulationSoundness.lean` with no `sorry`:
  - `GamePosition.AlignedSafeGhostStep` and its `can_avoid_loss` theorem;
  - `StrategySimulation`, packaging target, terminal, owner-existential, and
    opponent-universal local obligations;
  - `StrategySimulation.can_avoid_loss`, a solver-independent transfer proof by well-founded
    induction on the large position's remaining-cardinality;
  - `GamePosition.p1_score_balance_after_pick`, proving that one pick changes the encoded p1 score
    lead by the parent mover's signed counter value.
- `lake --wfail build CatchUpResearch` passes all 8,088 jobs. No files were staged, committed,
  pushed, or submitted.
- This proves the framework theorem, not closure of the concrete one-residual ledger relation. The
  remaining mathematical gate is to state that relation semantically, require ledger-compatible
  child witnesses in the local obligations, and prove or sharply characterize its owner/opponent
  closure without consulting exact solver outcomes.

### Semantic one-residual forcing basin is formally sound — 2026-08-08 04:15 EDT

- Added warning-clean `scripts/catch_up/SimulationLedger.lean`, with no `sorry`. It defines:
  - old/top/pending counter supports and signed finite sums;
  - `FourLiftLedger` with persistent top/pending signs and one optional resolved `±2x` residual;
  - separate static support and score consistency;
  - pointwise `HistoryStep` equations preventing sign or residual reassignment;
  - `FourLiftGhost.Advances`, combining aligned safe ghost motion, history persistence, child
    support, and the aggregate score update;
  - the proof-backed semantic explicit endgame target;
  - `ExplicitFourLiftBasin`, the least owner-existential/opponent-universal forcing basin inside the
    persistent relation;
  - `ExplicitFourLiftBasin.can_avoid_loss`, proving every basin member safe by well-founded
    induction on the large remaining-cardinality.
- The empty-ledger root consistency theorem and conditional aligned-root transfer corollaries also
  compile. `lake --wfail build CatchUpResearch` passes all 8,089 jobs; `git diff --check` is clean.
- Precise remaining theorem: prove `ExplicitFourLiftBasin N player ⟨small, emptyLedger⟩ large` for a
  natural parametric family of aligned reachable roots (initially the opening-1 roots), uniformly
  under `N↦N+4`. Computation establishes this at bases `7,8,11,12` for both players, but no uniform
  Lean membership proof has yet replaced the solver-selected owner moves and opponent responses.

## Active unit: controller extraction plus rigorous finite-certificate extension

- Timestamp: **2026-08-08 04:17 EDT**.
- Deadline policy: continue research until 07:15 EDT, then stop new lines and consolidate for the
  08:00 EDT final report.
- Parametric action: audit the semantic ledger against the executable, then add a selected-witness
  reporter classifying moves relative to the two pending counters, the four top offsets, stutter,
  and matched/different old moves. Start only with `N=7`; run `N=8` only if the normalized template
  count is small enough to suggest a proof.
- Finite-proof action: inspect `PartialCertificateMain.lean`, `N11Certificate.lean`, and
  `N12Certificate.lean` to determine whether a complete Lean-checked draw certificate for `N=15`
  or `N=16` fits before consolidation. Do not begin a run without a time/memory estimate and an
  exact recovery command.
- Exact recovery if interrupted: first run `date '+%Y-%m-%d %H:%M:%S %Z'`, then read this section;
  no new large-size computation has started at this checkpoint.

### Launching `N=15` partial-certificate feasibility run — 2026-08-08 04:20 EDT

- Based on complete-graph sizes 19,169 at `N=11` and 43,168 at `N=12`, `N=15` is expected to be a
  few hundred thousand states and should finish well before consolidation.
- Exact command:
  `lake env lean --run scripts/catch_up/PartialCertificateMain.lean 15 8`.
- Target limit eight is still proof-backed by `CanAvoidLossClassifier`; it trades more native target
  evaluation for a substantially smaller literal DAG. Required success: independent acceptance of
  the p1 opening-1 DAG, independent acceptance of one p2 all-openings DAG, and all 15 p2 roots
  present. Do not serialize on any weaker result.

### `N=15` partial-certificate feasibility result — 2026-08-08 04:22 EDT

- The run completed successfully with exit code zero after solving 461,231 full-game states.
- The independent partial-certificate checker accepted both required certificates:
  - player 1 after opening one: 403 nodes;
  - player 2 across all openings: 532 nodes;
  - covered player-2 opening roots: all 15.
- This is sufficient finite data for a fully Lean-checked proof that the `N=15` game is a draw,
  once the two accepted DAGs are serialized and packaged like `N11Certificate.lean` and
  `N12Certificate.lean`.
- The next action is to choose and test the least bulky faithful serialization. No claim about
  `N=15` is added to the theorem namespace until the emitted data is rechecked from its literal
  representation.

### Trust-boundary and serialization audit — 2026-08-08 04:25 EDT

- A line-by-line semantic audit found no sign, score-gap, support, or residual-value mismatch
  between the one-residual executable and `SimulationLedger.lean`. The executable AND/OR recurrence
  also has the same owner-existential/opponent-universal shape as `ExplicitFourLiftBasin`.
- However, there is still no reflection theorem from `residualRoot = true` (or its cache) to an
  `ExplicitFourLiftBasin` proof. Therefore the residual runs remain strong discovery evidence, not
  Lean-certified basin membership. The formal relation fixes pending width at two; only CLI runs
  with limit two model it.
- By contrast, the partial-certificate checker does not trust the exact solver or extractor. Its
  accepted literal DAGs independently verify state bounds, legal exact transitions, the selected
  owner move, every opponent move, and proof-backed target leaves.
- The least-risk `N=15` packaging is therefore a single literal module, following the existing
  `N12Certificate.lean` pattern with target limit eight. The 935 total nodes predict roughly 50–55
  KB of source and a 10–30 second direct compile. Compression or a new certificate API would add
  unnecessary proof risk.

### Launching deterministic `N=15` certificate emission — 2026-08-08 04:26 EDT

- Exact command: `lake env lean --run scripts/catch_up/PartialCertificateMain.lean 15 8 --emit`.
- The output will be retained in memory, not redirected into the repository. Only the text between
  the generated-certificate markers may be inserted, and insertion must use `apply_patch`.
- Before treating the literal data as stable, rerun the same command and compare generated-block
  hashes. Then add the 15 explicit opening masks and re-run the independent checker from the literal
  module.

### First `N=15` emission captured — 2026-08-08 04:31 EDT

- The command completed successfully. The generated block is 36,066 characters and 940 lines,
  with exactly one player-1 DAG definition and one player-2 DAG definition.
- The block is retained in session memory; it has not yet been written to the repository.
- A second independent invocation of the identical command is now required. Acceptance criterion:
  the two generated blocks must be byte-for-byte identical, not merely checker-equivalent.

### Formally checked `N=15` draw certificate — 2026-08-08 04:39 EDT

- The second independent emission was byte-for-byte identical to the first: 36,066 characters,
  940 generated lines, local FNV-1a fingerprint `a9e00d4f`.
- Added `scripts/catch_up/N15Certificate.lean` through `apply_patch` only. It contains the literal
  403-node player-1 DAG and 532-node all-openings player-2 DAG, target limit eight, a fixed-size
  post-opening decoder, the two independent checker equalities, both one-sided safety theorems, and
  `value_Icc_fifteen`.
- The first direct compile exposed only wrapper-scale recursion issues. The certificate data was not
  changed. Player-2 root containment now uses `native_decide`, and the player-1 proof concretizes
  the DAG root before simplification so the simplifier does not unfold the 403-node list.
- `lake env lean scripts/catch_up/N15Certificate.lean` now exits zero with no output. The file has
  1,055 lines / 48,515 bytes and SHA-256
  `bb90ec85b7c9160ef53d89e39ba31f921f084e5b824451b7e5b9125d1138d010`.
- The file contains no `sorry`, `admit`, or `axiom`; `git diff --check` is clean. Remaining checks:
  print the final theorem's axioms and run the warning-strict `CatchUpResearch` build.

### `N=15` module build and trust report — 2026-08-08 04:42 EDT

- `lake --wfail build catch_up.N15Certificate` completed successfully: 8,059 jobs, with the new
  module built in 85 seconds and no warnings.
- Lean reports that `value_Icc_fifteen` depends on exactly
  `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`, matching the
  existing `N=11`/`N=12` certificate trust boundary. The two closed checker equalities and the
  finite player-two opening-root containment cases use `native_decide` and therefore rely on Lean's
  native compiler. The generic certificate-soundness and strategy reductions are ordinary proved
  theorems.
- The temporary in-checkout axiom-query module was deleted after capturing this report. It is not a
  retained artifact. Next: the full warning-strict `CatchUpResearch` build from the final file set.

### `N=15` certificate complete — 2026-08-08 04:43 EDT

- `lake --wfail build CatchUpResearch` passes all 8,090 jobs from the final retained file set.
- The repository now contains a fully checked `N=15` draw theorem in addition to `N=11` and
  `N=12`. This is rigorous finite progress but does not discharge, or substitute for, the
  parametric `N↦N+4` basin-membership theorem.
- Next bounded unit: run `PartialCertificateMain.lean 16 8` without emission. Abort the finite track
  if runtime or node counts make serialization implausible before 07:15 EDT.
- In parallel, review a normalized one-residual witness reporter design. The report must enumerate
  winning child templates per exact `ResidualPairKey`; it must not present the search's
  ascending/stutter-first witness as a natural controller.

### `N=16` partial-certificate feasibility result — 2026-08-08 04:52 EDT

- `lake env lean --run scripts/catch_up/PartialCertificateMain.lean 16 8` completed successfully.
  It solved 998,352 states and the independent checker accepted:
  - player 1 after opening one: 764 nodes;
  - player 2 across all openings: 945 nodes;
  - covered player-2 opening roots: all 16.
- The 1,709-node total is below the predefined 2,500-node continuation threshold; neither DAG is
  near the 1,500-node individual stop. Proceed with one literal emission and formal checking.
- Exact next command:
  `lake env lean --run scripts/catch_up/PartialCertificateMain.lean 16 8 --emit`.
  A second emission is omitted to preserve the parametric-research window: N=15 already established
  deterministic emission byte-for-byte, while the literal checker and finite opening-root
  containment proofs form the N=16 native-computation trust boundary.

### Formally checked `N=16` draw certificate — 2026-08-08 05:05 EDT

- The single emission completed successfully. Its generated block contains 66,325 characters and
  1,714 lines, with local FNV-1a fingerprint `03718ebf`.
- Added `scripts/catch_up/N16Certificate.lean` through `apply_patch` only: literal 764-node player-1
  DAG, literal 945-node all-openings player-2 DAG, target limit eight, 16-opening decoder and
  containment proof, both one-sided safety theorems, and `value_Icc_sixteen`.
- `lake env lean scripts/catch_up/N16Certificate.lean` exits zero with no output. The retained file
  has 1,830 lines / 84,967 bytes and SHA-256
  `0c2d2a40cc76a4e0c5558d74efb7402f676d51157d7271e097229b48a1a26304`.
- No `sorry`, `admit`, or `axiom` occurs in the file, and `git diff --check` is clean. Remaining
  finite-track check: warning-strict module/library build. Then return immediately to the normalized
  residual-witness reporter; do not extend the literal-certificate frontier further.

### `N=16` certificate complete; finite track closed — 2026-08-08 05:09 EDT

- `lake --wfail build CatchUpResearch` passes all 8,091 jobs; the new N=16 certificate module built
  in 156 seconds with no warnings.
- Do not run N=17 or enlarge the literal finite frontier. The repository now has fully checked draw
  theorems at 11, 12, 15, and 16, covering two successive `+4` pairs while leaving the parametric
  implication explicitly open.

## Active unit: normalized one-residual witness report

- Add a new `--async-residual-witness LIMIT N...` mode to `SimulationBasinMain.lean`.
- Traverse only exact cache entries keyed by `ResidualPairKey`. At owner nodes select one cached
  winning child; at opponent nodes select one cached winning response for every legal large move.
- Normalize players and score signs relative to the protected owner; separate `N % 4`; classify
  top offsets, matched old moves, pending resolution, ghost stutter/same/different/pending moves,
  catch-versus-continue comparisons, pending changes, and residual creation.
- Report the selected witness as `selection=solver-order`. It is discovery data, not a theorem and
  not evidence that ascending moves or stutter are intrinsically preferred.
- Required internal audits: every visited key is cached true; ledger validity and discrepancy bound
  hold; every selected child is cached true under its updated ledger; selected-edge count equals
  owner nodes plus opponent obligations; visited-state count partitions into internal and leaf
  nodes. First run only `LIMIT=2` at N=7 and N=8.

### Reporter implementation compiled — 2026-08-08 05:16 EDT

- Added normalized residual phases, structural large/ghost action classification, pending/residual
  transition labels, one raw example per edge kind, exact-cache witness replay, count audits, output
  formatting, runner, and `--async-residual-witness` CLI mode.
- The first compile caught one Lean lexical issue: `example` is a reserved command word. Renaming the
  local binding to `rawExample` resolved the parser cascade.
- `lake --wfail build catch_up.SimulationBasinMain` now passes all 8,062 jobs in five seconds.
- First smoke test is intentionally N=7 only:
  `lake env lean --run scripts/catch_up/SimulationBasinMain.lean --async-residual-witness 2 7`.
  Run N=8 only after all N=7 audits say `audit=ok` and no selected move is unclassified.

### N=7 selected-witness result and coarse projection — 2026-08-08 05:19 EDT

- Both owners returned `root=true` and `audit=ok`; no move or residual transition was unclassified.
- Player 2: searched 8,799 labels, selected 502, 268 exact normalized phases, 630 selected edges,
  80 exact edge kinds, 383 phase-actions, 398 phase transitions.
- Player 1: searched 19,194 labels, selected 1,902, 563 exact normalized phases, 2,223 selected
  edges, 138 exact edge kinds, 1,081 phase-actions, 1,119 phase transitions.
- This rejects a direct case-by-case table of exact selected phases. However, an in-memory projection
  that erases top offset, pending slot/sign, and catch comparison yields exactly 16
  `(large action, ghost action, pending change, residual change)` kinds for each owner, and only
  seven action pairs after also erasing ledger changes.
- Add those two projections to the executable report, then run N=8. The N=8 run is now testing a
  concrete hypothesis: the other residue class should preserve the same small structural ledger
  skeleton even if its arithmetic specializations differ.

### N=8 selected-witness result — 2026-08-08 05:22 EDT

- The reporter rebuild passed warning-strict after adding explicit `actionKinds` and `coarseKinds`.
- Both N=8→12 owners returned `root=true`, `selection=solver-order`, and `audit=ok`.
- Player 2: searched 30,292 labels, selected 1,959, 558 exact phases, 2,270 edges, seven action
  kinds, 18 coarse ledger kinds, 143 exact edge kinds, 1,060 phase-actions, 1,101 transitions.
- Player 1: searched 83,166 labels, selected 5,137, 797 exact phases, 6,179 edges, seven action
  kinds, 19 coarse ledger kinds, 188 exact edge kinds, 1,990 phase-actions, 2,097 transitions.
- The seven action pairs are identical to N=7 for both owners:
  `(T,Z)`, `(T,SP)`, `(T,DIFF)`, `(M,Z)`, `(M,SAME)`, `(M,SP)`, `(LP,Z)`.
- Relative to N=7, all new coarse cases merely vary the residual status on `LP/Z/removed` or
  `T/DIFF/added`; no eighth action pair appears. Thus the fixed-width relation has a compact local
  transition algebra, but the solver-selected strategic controller remains noncompact (hundreds of
  phases and thousands of phase-actions).
- Do not claim a parametric proof from this. The next decision is whether to (a) prove reusable
  semantic lemmas for these seven action forms, or (b) enumerate all cache-known winning
  alternatives and solve a template-cover problem to reduce strategic selection.

### Launching same-residue witness validation at N=11 — 2026-08-08 05:25 EDT

- Exact command:
  `lake env lean --run scripts/catch_up/SimulationBasinMain.lean --async-residual-witness 2 11`.
- This compares N=11→15 against N=7→11 in the same residue-three induction chain. Required success:
  both roots true, both internal audits OK, no eighth action pair, and only residual/pending variants
  of the existing coarse transition algebra.
- Even perfect stability is computational evidence only; the strategic phase-selection theorem is
  still missing.

### N=11 selected-witness result; solver-selected seven-action pattern fails — 2026-08-08 05:26 EDT

- Both N=11→15 owners returned `root=true` and `audit=ok`.
- Player 2: searched 1,311,265 residual labels, selected 38,479, 1,357 exact phases, 49,442 edges,
  eight action kinds, 21 coarse ledger kinds, 270 exact edge kinds.
- Player 1: searched 2,420,940 labels, selected 73,193, 1,618 exact phases, 97,254 edges, nine
  action kinds, 23 coarse ledger kinds, 295 exact edge kinds.
- New selected action forms are `M/DIFF` for both owners and one `LP/DIFF` edge for player 1. Raw
  examples include `(large x, ghost y)=(9,11)`, `(8,6)`, and pending-large `(10,5)`.
- Therefore the seven-pair skeleton seen at N=7/8 is not stable even within the residue-three chain.
  This does not refute a better controller because owner/opponent searches short-circuit and leave
  later alternatives unclassified. A genuinely order-independent cover experiment must lazily run
  the recurrence on every missing candidate, not merely scan the current cache.
- Before another controller search, add rigorous semantic normalization lemmas to
  `SimulationLedger.lean`: old support after a pick, consumed-top support after a pick, pending
  support after paired/large-only picks, and score-gap evolution. These lemmas underlie every
  eventual action constructor and remain useful even if the controller changes again.

### Semantic transition-normalization block — 2026-08-08 05:26 EDT

- Added and warning-strict compiled six reusable theorems in `SimulationLedger.lean`:
  - `GamePosition.four_lift_old_remaining_after_pick`;
  - `four_lift_pending_counters_after_picks`;
  - `four_lift_pending_counters_after_large_pick`;
  - `four_lift_consumed_top_counters_after_pick`;
  - `GamePosition.p1_score_gap_after_paired_pick`;
  - `FourLiftLedger.value_step_iff_consistent_after_pick`.
- These reduce every future concrete action constructor to explicit erasures, symmetric difference,
  top insertion, and one integer balance equation. They do not assert strategic closure.
- Pedagogical proof details: `change` exposed the structure-projection definition for the first
  finset identity; `ext` plus `simp` proved membership equality; the top lemma used cases on both
  top membership and counter equality; the score-gap identity used the existing one-pick theorem
  followed by `ring`.
- `lake --wfail build catch_up.SimulationLedger` passes 8,064 jobs after each retained lemma.

## Active unit: lazy all-alternatives context intersections

- Scope only the exact parent labels in the audited selected witness. At each owner node enumerate
  every coherent `(large move, ghost move, child ledger)`; at each opponent obligation enumerate
  every coherent ghost response to the fixed large move.
- For a missing child cache key, call `residualForceAux` lazily with the shared cache. Record missing,
  newly true, and newly false counts. This removes short-circuit enumeration bias at the analyzed
  obligations without eagerly exploring the complete all-winning supergraph.
- Group obligations by owner-relative residual phase; opponent groups also include the precise
  challenged large-action class and catch comparison. Intersect available action templates and
  available coarse ledger templates within each group.
- Success criterion for a controller experiment: every group has a nonempty action intersection,
  preferably every ledger intersection too, and the chosen group rules remain small. Empty
  intersections show that the current phase omits a necessary arithmetic feature; they are not a
  mathematical refutation because only selected parent states are analyzed.
- Implement and compile by 06:15 EDT or stop this line. First run N=7 only.

### Lazy N=7 context-intersection results — 2026-08-08 05:34 EDT

- Initial phase grouping (ledger/top/movers only) found common coarse action classes in 289/299
  player-2 groups and 637/679 player-1 groups. At encounter time, lazy classification found 514
  winning direct candidates absent from the then-current cache for player 2 and 2,233 for player 1.
- Adding deficit offset and the challenged counter's comparison with the ghost deficit reduced
  conflicts to 3 player-2 and 37 player-1 groups.
- Adding the finite signature of safe ghost-option kinds (`Z`, matched/pending, and catch relation)
  reduced player 2 to zero conflicts: all 533 groups have common coarse action and ledger classes.
  Player 1 has common coarse actions in 1,572/1,578 groups and common coarse ledger classes in
  1,568/1,578; ten combined conflicts remain.
- The current signature cannot distinguish those ten groups. Their raw examples differ in pending
  identities and exact old-state geometry, but a smaller derived arithmetic feature may still
  separate them. Stop phase-tag refinement here rather than add exact masks.

### Parametric old-opening and draw reductions — 2026-08-08 05:38 EDT

- Added `ExplicitFourLiftClosure.can_avoid_loss_after_opening`: for every legal old opening `x`,
  explicit four-lift closure transfers `CanAvoidLoss player` from the size-N opening root to the
  size-(N+4) root with the same opening.
- Retained opening one as the corollary
  `ExplicitFourLiftClosure.can_avoid_loss_after_opening_one`.
- Added `value_Icc_add_four_eq_draw_of_explicit_four_lift_closure`: a draw at N, one closure for
  each protected player, and player-2 safety after the four new openings imply a draw at N+4.
- This is a genuine conditional parametric reduction theorem. It does not prove either closure or
  the four new-opening boundary conditions. For this reduction, those are sufficient remaining
  obligations; this does not replace the earlier, weaker target of proving basin membership only at
  the natural roots.
- `lake --wfail build catch_up.SimulationLedger` passes all 8,064 jobs.

### Lazy N=8 context-intersection result; controller refinement frozen — 2026-08-08 05:41 EDT

- Both roots and all witness audits pass after lazy classification of every candidate generated by
  `alignedSmallOptions` and accepted by `updateResidualLedger?` at the selected parent obligations.
- Player 2: 2,270 obligations / 1,516 contexts; a common coarse action and ledger class occurs in
  1,510 contexts; six conflicts. Of 7,725 encounter-time cache misses, 2,502 are winning and 5,223
  losing.
- Player 1: 6,179 obligations / 4,076 contexts; a common coarse action class occurs in 4,044
  contexts and a common coarse ledger class in 4,036, with 40 combined conflicts. Of 19,524
  encounter-time cache misses, 5,221 are winning and 14,303 losing.
- Thus the diagnostic intersection rates exceed 99%, but many groups may be singletons and the
  current phase signature remains insufficient. Raw conflicting contexts differ in pending
  identities and old-state geometry, but a smaller derived arithmetic feature may still separate
  them. The grouping produces thousands of distinct contexts, and no roughly ten-rule symbolic
  controller has been extracted from them.
- Freeze this search rather than add exact masks or pending values as phase tags. A future attempt
  should synthesize symbolic guarded rules in pending variables, or use an AND/OR Pareto-template
  dynamic program; neither result should be claimed from the present data.

### Full retained-work audit — 2026-08-08 05:41 EDT

- `lake --wfail build CatchUpResearch` passes all 8,091 jobs.
- No `sorry`, `admit`, or `axiom` occurs in `SimulationLedger.lean`,
  `SimulationBasinMain.lean`, `N15Certificate.lean`, or `N16Certificate.lean`.
- `git diff --check` is clean. Branch remains `codex/catchup-experiment`; none of the current
  working-tree changes is staged or committed, and no push or PR action was taken.

### Independent-review corrections and root-specific reduction API — 2026-08-08 05:53 EDT

- Three read-only reviews independently audited the formal reduction, executable scanner, and
  checkpoint. No mathematical error was found in the normalization lemmas, local lazy
  classification, or conditional draw proof.
- Weakened `ExplicitFourLiftClosure.owner_exists` and `.opponent_forall`: child safety and child
  relatedness are now derived from `Advances` by `safe_after_advance` and
  `related_after_advance`, rather than demanded as redundant closure hypotheses.
- Strengthened `value_step_iff_consistent_after_pick` to expose the exact decomposition
  `child Supports ∧ ValueStep ↔ child Consistent`, assuming parent consistency.
- Added the minimal interface `FourLiftOldOpeningTransfer`, plus
  `ExplicitFourLiftOldOpeningBasin` and `ExplicitFourLiftOldOpeningBasins`. The latter records
  proof-carrying basin membership only at safe natural roots, matching a future certificate route
  and avoiding the much stronger universal-closure requirement.
- Added the primary conditional theorem
  `value_Icc_add_four_eq_draw_of_old_opening_transfers_and_new_opening_safety`, its root-basin
  corollary, and retained the global-closure theorem as a stronger sufficient corollary. The four
  new player-two openings remain explicit boundary obligations.
- Renamed the closure lemma to `can_avoid_loss_after_old_opening` to make its quantifier scope
  unambiguous. Warning-strict `catch_up.SimulationLedger` build passes.
- Calibrated the scanner output as `alternatives=selected-parent-local`; canonicalized safe-option
  signatures; separated singleton from repeated groups; renamed order-dependent cache-miss counts
  as encounter-time counts; and report both witness-cache and expanded-cache totals. Warning-strict
  `catch_up.SimulationBasinMain` build passes.
- Next finite diagnostic: rerun N=7 once with the corrected reporter to obtain non-singleton rates.
  Do not use that run to resume controller overfitting.

### Corrected N=7 selected-parent diagnostic — 2026-08-08 05:55 EDT

- Both roots remain true and all witness audits pass. The corrected labels explicitly distinguish
  the original witness cache from the lazily expanded cache.
- Player 2: 630 obligations / 525 groups, of which 440 are singletons and 85 are repeated. Every
  repeated group has a common coarse action and ledger class. Encounter-time misses split as 514
  winning and 1,110 losing; the expanded cache has 110,624 labels / 20,437 winning.
- Player 1: 2,223 obligations / 1,481 groups, of which 1,190 are singletons and 291 are repeated.
  Common coarse action classes occur in 280/291 repeated groups and common coarse ledger classes
  in 276/291; 15 combined conflicts remain. Encounter-time misses split as 2,233 winning and 4,513
  losing; the expanded cache has 138,053 labels / 26,968 winning.
- Sorting the safe-option signature merged groups that had differed only by enumeration order;
  this exposed five additional player-one conflicts. The informative repeated-group rates are
  therefore roughly 96.2% for actions and 94.8% for ledger classes, not the earlier aggregate
  above-99% headline. This reinforces the decision to freeze controller extraction.

### New-opening ledger and complete conditional draw reduction — 2026-08-08 06:05 EDT

- Found the natural boundary alignment: compare small opening `k` with large opening `N + k`, for
  `1 ≤ k ≤ 4`. The pending old support is exactly `{k}` and the consumed top support is exactly
  `{N + k}`.
- Defined `FourLiftLedger.newOpening N k` with positive top support `{N + k}`, empty positive
  pending support (so pending `k` has negative sign), and no residual. Proved
  `FourLiftLedger.consistent_new_opening` for `4 ≤ N`. Its value is
  `+(N + k) - k`, exactly the large-minus-small score balance.
- Proved `ExplicitFourLiftClosure.can_avoid_loss_after_new_opening`: global closure transfers any
  protected player's safety from small opening `k` to large opening `N + k`.
- Added `FourLiftNewOpeningTransfer`, `ExplicitFourLiftNewOpeningBasin`, and
  `ExplicitFourLiftNewOpeningBasins`, together with the basin-to-transfer theorem. These give the
  root-specific certificate route parallel to the old-opening API.
- Added `value_Icc_add_four_eq_draw_of_opening_transfers`: for `4 ≤ N`, player-one and player-two
  old-opening transfers, player-two new-opening transfer, and a draw at `N` imply a draw at `N+4`.
  Added the fully root-specific basin corollary.
- Strengthened `value_Icc_add_four_eq_draw_of_explicit_four_lift_closure`: it now needs only
  `4 ≤ N`, the two global closures, and the draw at `N`; the former independent four-new-opening
  safety premise has been eliminated.
- All statements are conditional: neither universal closure nor the required root-basin
  memberships have been proved. The achievement is a clean, self-contained reduction of the
  strategic research obligation, not a proof of the Catch-Up conjecture.
- `lake --wfail build catch_up.SimulationLedger` passes. Independent semantic review is in progress.

## Active unit: quantify the executable root obligations

- Add a diagnostic mode that tests exactly the roots quantified by the new conditional theorem:
  every old opening for both protected players, and the four paired new openings `k ↔ N + k`
  for player 2.
- Old roots use the empty ledger. New roots use the executable counterpart of
  `FourLiftLedger.newOpening`: top-positive bit `k-1`, no pending-positive bits, and no residual.
- Independently assert `residualLedgerValid` at every root before search. Report only root truth and
  cache counts; do not run the large witness/context reporter.
- First and only discovery run in this unit is N=7. A false root identifies the exact missing
  transfer obligation; all true roots would strengthen evidence for the root-basin formulation but
  remain untrusted executable evidence, not Lean proofs.

### Universal static closure rejected; root-basin API retained — 2026-08-08 06:12 EDT

- Independent review found a concrete statically `Consistent` but history-unreachable pair where an
  unavoidable opponent pick grows pending width from two to three. No `Advances` child exists.
  Swapping movers/signs gives the obstruction for either protected player.
- Consequently, the universal `ExplicitFourLiftClosure` over every statically related pair is
  uninhabited for the intended `N ≥ 4`; its draw corollary was logically sound but vacuous.
- Removed `ExplicitFourLiftClosure`, its global simulation packaging, its transfer lemmas, and the
  global-closure draw theorem. Do not restore a universal closure without adding a genuine
  reachability/provenance invariant.
- The root-specific `ExplicitFourLiftBasin` and old/new opening basin families are unaffected: their
  inductive constructors retain the selected history. The primary retained theorem is
  `value_Icc_add_four_eq_draw_of_opening_basins`.
- This supersedes the earlier checkpoint statements treating two global closures as plausible
  remaining obligations. It also calibrates the new-opening result: the four boundary roots have
  been absorbed into a common **root-basin** framework, not proved for free.
- Warning-strict `catch_up.SimulationLedger` build passes after removal.

### Complete N=7→11 executable root matrix — 2026-08-08 06:12 EDT

- Added `--async-residual-roots LIMIT N`, with generalized root lookup and an independent
  `residualLedgerValid` check before every search. Existing command modes retain opening-1 behavior.
- All theorem-required roots pass with discrepancy limit two:
  - player 2: all seven old openings are small-safe and basin-search true;
  - player 1: old openings 1–4 are small-safe and true; openings 5–7 are small-unsafe, so their
    transfer antecedents are false and no basin proof is required;
  - player 2: all four new roots `1↔8`, `2↔9`, `3↔10`, `4↔11` are small-safe, initial-ledger
    valid, and basin-search true.
- Thus every root quantified nonvacuously by the retained basin reduction passes at N=7. This is
  executable discovery evidence only; the recurrence-to-`ExplicitFourLiftBasin` reflection theorem
  is still absent.
- The positive complete matrix justifies one complementary N=8→12 run for the residue-zero chain.

### N=8→12 root matrix and exact width-two obstruction — 2026-08-08 06:22 EDT

- Every old-opening root passes for both players; all sixteen old roots are small-safe and
  basin-search true.
- New player-two roots `2↔10`, `3↔11`, and `4↔12` pass. The required root `1↔9` is false after
  334,519 residual labels / 48,776 winning, despite `smallSafe=true` and `ledgerValid=true`.
- Added a cached negative-trace reporter. One obstruction path takes large counters 1, 2, 3, 4
  while the small guide stutters. The pending old support evolves
  `{1} → ∅ → {2} → {2,3} → {2,3,4}`; balance remains exact throughout, and failure is
  precisely `old discrepancy exceeded 2` after the large player catches.
- Therefore the current width-two one-residual basin does not establish the complete residue-zero
  draw step. This is a genuine negative result for the present relation, not for the conditional
  theorem or for Catch-Up.
- One targeted follow-up is authorized: rerun only `1↔9` with discrepancy limit three. If true,
  width three is a concrete next relation candidate; if false, stop rather than continue widening.

### Width three absorbs the residue-zero boundary obstruction — 2026-08-08 06:23 EDT

- Added a single-new-root diagnostic and ran exactly
  `--async-residual-new-root 3 8 1`.
- The formerly false player-two root `1↔9` becomes true at discrepancy limit three, with 19,064
  searched labels / 2,875 winning. Thus three is the smallest tested pending-width bound that
  covers all nonvacuous theorem roots at both N=7→11 and N=8→12.
- Updated the semantic `FourLiftLedger.Supports` bound from pending cardinality two to three and
  clarified its docstring. Independent review confirmed that this preserves all basin soundness:
  visible pending counters retain pointwise coefficients `±1`, while the optional residual remains
  the sole resolved coefficient `±2`.
- Warning-strict `catch_up.SimulationLedger` build passes with the width-three relation.
- This still does not reflect the executable cache into Lean. The remaining credible target is to
  prove or independently certify the root-specific old/new basin families for width three. A
  universal static closure remains impossible: its overflow counterexample merely shifts from
  width `2→3` to `3→4`.

### Consolidated verification and next gate — 2026-08-08 06:24 EDT

- `lake --wfail build CatchUpResearch` passes all 8,091 jobs after the final width-three and
  root-basin changes.
- `git diff --check` is clean. No `sorry`, `admit`, or `axiom` occurs in the audited simulation or
  N15/N16 certificate modules.
- Branch remains `codex/catchup-experiment`. None of the current working-tree changes is staged or
  committed; no push or PR action was taken.
- The retained mathematical target is now precise and nonvacuous:
  `value_Icc_add_four_eq_draw_of_opening_basins` reduces the draw at `N+4` to the draw at `N` plus
  player-one/player-two old-opening basin families and the player-two new-opening basin family.
- The N=7→11 and N=8→12 exact runs give positive executable evidence for every nonvacuous root at
  semantic pending width three. They do **not** inhabit those Lean basin predicates.
- Next research gate: build an independent product-strategy certificate/reflection layer whose
  checked output constructs `ExplicitFourLiftOldOpeningBasins` and
  `ExplicitFourLiftNewOpeningBasins`, or extract a genuinely symbolic reachable-phase invariant
  strong enough to construct those inductive basin proofs. Do not return to universal static
  closure or add exact masks as controller cases.

### Active final theorem unit: weaken the player-one root obligation — 2026-08-08 06:27 EDT

- Three independent feasibility audits agree that a large-only certificate projection would erase
  the ghost/ledger evidence needed for `ExplicitFourLiftBasin`, while a sound product-certificate
  reflection layer is too large to implement and audit before the 07:15 consolidation cutoff.
- The retained draw reduction currently overstates the player-one obligation: player one needs one
  non-losing opening, whereas player two must avoid loss after every opening.
- Add a semantic empty-ledger consistency lemma for every unchanged old-opening root, then prove a
  sharper draw-step theorem requiring one explicit player-one old-opening basin, all player-two
  old-opening basins, and all player-two new-opening basins. Refactor the existing family-based
  theorem as a corollary if the sharper proof compiles warning-strictly.
- This is a hypothesis reduction in the nonvacuous root-basin theorem. It does not inhabit any
  basin or reflect executable evidence into Lean.

### Player-one root obligation weakened — 2026-08-08 06:35 EDT

- Proved `FourLiftLedger.consistent_old_opening`: every unchanged old-opening pair begins in the
  semantic relation with the empty ledger. This removes a repeated invariant proof from future
  root certificates.
- Proved
  `value_Icc_add_four_eq_draw_of_some_player_one_old_opening_basin_and_player_two_basins`. It needs one
  explicit player-one old-opening basin, both complete player-two basin families, and only the
  player-two half of the small-game draw criterion.
- Refactored `value_Icc_add_four_eq_draw_of_opening_basins` as a corollary. The old API remains
  available, but its proof now exposes that a full player-one basin family is stronger than needed.
- `lake --wfail build catch_up.SimulationLedger` passes.

### Active final bridge unit: local reachable closure implies basin membership — 2026-08-08 06:35 EDT

- Add a relation-level closure predicate parameterized by an arbitrary relation `R` on ghost/large
  pairs. A member must be a proved target, a safe terminal, an owner node with one advancing child
  in `R`, or an opponent node with an advancing child in `R` for every legal large move.
- Prove by well-founded induction on the large remaining-card count that a safe root in any such
  locally closed relation belongs to `ExplicitFourLiftBasin`.
- This is intended as the soundness core of a future finite product-DAG checker. It deliberately
  does not claim that the current executable cache supplies such an `R`.

### Local reachable closure theorem complete — 2026-08-08 06:37 EDT

- Defined `ExplicitFourLiftLocallyClosed` for an arbitrary selected relation on ghost/large pairs.
- Proved `ExplicitFourLiftLocallyClosed.to_basin` by well-founded induction on the large remaining
  counter count. Owner nodes use one selected advance; opponent nodes use dependent choice to select
  an advance for every legal move; child ghost safety follows from `safe_after_advance`.
- The theorem allows a finite certificate relation to construct basin membership without requiring
  universal closure over unreachable statically consistent pairs.
- Warning-strict `catch_up.SimulationLedger` build passes.

### Active finite-reflection unit: make history persistence executable — 2026-08-08 06:37 EDT

- Define a Boolean history-step checker by iterating over the finite old and top counter intervals.
- Prove checker truth equivalent to semantic `FourLiftLedger.HistoryStep`.
- This removes the unbounded-quantifier obstacle identified for a future product-DAG checker; it is
  not a complete product checker or an executable-cache reflection theorem.

### History persistence reflection complete — 2026-08-08 06:43 EDT

- Defined executable `FourLiftLedger.historyStepCheck` using bounded `List.range` traversals rather
  than non-executable `Finset.toList` conversion.
- Proved `FourLiftLedger.history_step_check_eq_true`, reflecting checker truth exactly to semantic
  `HistoryStep`. Warning-strict compilation passes.
- Added `FourLiftNewOpeningTransfer.can_avoid_loss_of_mem_new_interval` and reused it to remove the
  duplicated `x = N + k` arithmetic in both draw reductions.
- Independent logic, quantifier, and API reviews found no correctness, vacuity, or lint blocker.
  They confirm that local closure is a semantic checker core, not yet executable-cache reflection.

### Active final regression: basin constructors satisfy local closure — 2026-08-08 06:43 EDT

- Prove by constructor case analysis that `ExplicitFourLiftBasin` itself is
  `ExplicitFourLiftLocallyClosed`.
- This checks that the new local-closure interface exactly exposes the basin's four local cases.

### Final bridge/regression unit complete — 2026-08-08 06:44 EDT

- Proved `ExplicitFourLiftBasin.locally_closed` by direct case analysis on target, terminal, owner,
  and opponent constructors. Together with `ExplicitFourLiftLocallyClosed.to_basin`, this confirms
  that the selected-relation interface faithfully exposes the basin's local obligations.
- Independent review confirmed that `hmember` prevents an empty-relation vacuity and that induction
  is well founded even if the selected relation is not finite or acyclic: every recursive large
  edge strictly removes one counter.
- The remaining executable trust bridge is now sharply decomposed:
  1. encode product states containing small state, large state, and semantic ledger;
  2. retain and serialize selected product branches from the residual search;
  3. independently decode masks and check root/node containment and uniqueness;
  4. check large legality, exact large child, ghost stutter/pick, ledger support/value/history steps,
     owner selection, and complete opponent coverage;
  5. certify the `CanAvoidLoss` facts embedded in moving `AlignedSafeGhostStep`s;
  6. prove checker truth supplies a locally closed finite relation and root membership;
  7. invoke `ExplicitFourLiftLocallyClosed.to_basin` and then the sharpened draw reduction.
- The existing large-only `StrategyDAG` checker cannot replace this: it erases the small state and
  ledger, and product paths may revisit one large state under different ghost/ledger labels.

### Consolidated verification — 2026-08-08 06:44 EDT

- `lake --wfail build CatchUpResearch` passes all 8,091 jobs.
- `git diff --check` is clean. The audited simulation and N15/N16 certificate files contain no
  `sorry`, `admit`, or `axiom`.
- `SimulationLedger.lean` SHA-256:
  superseded by the final edge-reflection hash recorded below.
- N15 and N16 source hashes remain respectively
  `bb90ec85b7c9160ef53d89e39ba31f921f084e5b824451b7e5b9125d1138d010` and
  `0c2d2a40cc76a4e0c5558d74efb7402f676d51157d7271e097229b48a1a26304`.
- Branch remains `codex/catchup-experiment`; the index is empty. No commit, push, PR, or remote write
  was made.

### Active final executable edge-reflection unit — 2026-08-08 06:45 EDT

- Add an explicit optional-ghost-counter Boolean checker: `none` certifies stutter; `some y`
  independently checks alignment, nonterminality, legality, exact child equality, and protected-owner
  child safety using `CanAvoidLossClassifier.check`.
- Combine that check with `historyStepCheck`, child `Supports`, and `ValueStep` into a Boolean
  `advanceCheck`; prove checker truth implies semantic `FourLiftGhost.Advances`.
- This is the local edge-reflection component needed by a future product certificate. It does not
  check DAG containment, owner choice, opponent coverage, decoding, or root membership.
- Recovery/stop rule: run `lake --wfail build catch_up.SimulationLedger`; if the unit is not clean by
  07:05 EDT, remove only this last incomplete block and retain the verified 06:44 checkpoint.

### Executable edge reflection complete — 2026-08-08 06:48 EDT

- Added constructive `Decidable` instances for `FourLiftLedger.Supports` and `ValueStep`; the
  support instance splits the optional residual before synthesizing the finite decision procedure.
- Added `GamePosition.alignedSafeGhostStepCheck`. An explicit `none` checks exact stutter; `some y`
  checks mover alignment, nonterminality, membership of `y`, exact `afterPick` equality, and—when
  the actor is the protected player—exact one-sided safety through `CanAvoidLossClassifier.check`.
- Proved `aligned_safe_ghost_step_of_check_eq_true`.
- Added `FourLiftGhost.advanceCheck`, combining aligned ghost action, history persistence, child
  support, and value update. Proved `advances_of_advance_check_eq_true`.
- `lake --wfail build catch_up.SimulationLedger` passes (8,065 jobs). Fresh independent logic,
  executability, and API audits are in progress.
- This substantially narrows the future product checker: local edge semantics are now reflected.
  DAG decoding/containment, branch selection and exhaustive opponent coverage, root membership,
  witness serialization, and literal certificate verification remain unimplemented.

### Edge encoding completeness complete — 2026-08-08 06:51 EDT

- Proved `GamePosition.exists_aligned_safe_ghost_step_check_eq_true`: every semantic ghost step has
  an accepted `Option ℕ` encoding (`none` for stutter, `some y` for a pick).
- Proved `FourLiftGhost.exists_advance_check_eq_true_iff`:
  `(∃ smallCounter, advanceCheck ... smallCounter = true) ↔ Advances ...`.
- Thus the ghost-action/ledger-transition portion of the product-edge format is both sound and
  complete with respect to semantic `Advances`. Large-move legality/nonterminality, parent
  relation/safety, and owner/opponent branch coverage deliberately remain node-level obligations.
  Warning-strict module compilation and placeholder/whitespace scans pass.

### Independent edge-reflection audit — 2026-08-08 06:53 EDT

- Logic, executability, and API reviewers all pass the latest block. Direct `#eval` smoke tests of
  the exact safety classifier, history checker, ghost-action checker, and combined advance checker
  each returned `true` on the audit examples.
- Source contains no `classical`, `noncomputable`, `unsafe`, or `native_decide` in
  `SimulationLedger.lean`/`CanAvoidLossClassifier.lean`; the definitions themselves are constructive.
- `#print axioms` for the classifier equivalence and checker soundness theorems contains only
  standard `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
- Large literal certificate checks will probably require `native_decide`, which adds
  `Lean.ofReduceBool` and `Lean.trustCompiler`, as in the existing N11/N12/N15/N16 certificates.
- Performance warning: `CanAvoidLossClassifier.check` is unmemoized and may be the dominant cost
  when recomputed at many owner ghost edges; `historyStepCheck` also performs O(N) range scans.
  Benchmark before emitting a large product certificate.
- Architectural note: keep the eventual product-DAG types/checker/emitter in a new module importing
  `SimulationLedger`; do not continue growing the now roughly 900-line semantic module.
- Final `SimulationLedger.lean` size/hash at this checkpoint: 905 lines / 44,272 bytes,
  SHA-256 `ed9656fd9afcd9ba55e0174db507239442846bfea1b91a11813b072294e67f42`.

## Consolidated final-report draft — 2026-08-08 07:02 EDT

### Outcome

- The Catch-Up conjecture remains unresolved. No counterexample was found, and no unconditional
  parametric `N ↦ N + 4` theorem was proved.
- There is nevertheless substantial rigorous progress: four complete formal finite draw
  certificates, a symbolic four-counter classification, a nonvacuous conditional draw-step API,
  a persistent width-three semantic ledger/basin, a local-closure-to-basin theorem, and a sound and
  complete executable reflection of individual ghost/ledger advances.
- The original target has not been abandoned. Its credible form is now a **root-specific,
  history-carrying basin certificate**, not universal closure over every statically consistent pair.

### Formally established facts

- `CatchUp.value_eq_draw_iff_can_avoid_loss_after_opening` gives the exact game quantifiers:
  player 1 needs one safe opening; player 2 must be safe after every opening.
- Literal partial-strategy certificates prove full draws at `N = 11, 12, 15, 16`:
  - N11: 83-node p1 DAG / 124-node all-openings p2 DAG;
  - N12: 170 / 228;
  - N15: 403 / 532;
  - N16: 764 / 945.
  The independent checker verifies state bounds, exact legal transitions, one owner choice,
  exhaustive opponent coverage, child containment, uniqueness, progress, and proof-backed leaves.
- `TopFourClassification.value_top_four` gives the exact value of four consecutive counters in its
  full parametric deficit range; `top_subset_value?_sound` covers all 16 subsets.
- Parametric three-counter, one-old-pair, and four-counter-entry safety theorems justify the explicit
  endgame targets without trusting solver annotations.
- `SimulationLedger.lean` formally defines the width-three, one-residual relation; proves exact old
  and new opening consistency; defines `ExplicitFourLiftBasin`; and proves every basin member safe.
- `ExplicitFourLiftLocallyClosed.to_basin` proves any safe root in a selected locally closed
  relation belongs to the basin. `ExplicitFourLiftBasin.locally_closed` verifies that this interface
  exactly exposes the basin constructors.
- `FourLiftGhost.exists_advance_check_eq_true_iff` proves the explicit optional-counter Boolean edge
  format sound and complete for semantic `Advances`. Large legality, node invariants, and branch
  coverage remain deliberately separate node-level obligations.
- The sharpest conditional reduction is
  `value_Icc_add_four_eq_draw_of_some_player_one_old_opening_basin_and_player_two_basins`: for
  `4 ≤ N`, one p1 old-opening basin, every required p2 old/new-opening basin, and the p2 half of the
  small-game draw criterion imply a draw at `N+4`.
- `value_Icc_add_four_eq_draw_of_opening_basins` is the family-based corollary using a draw at `N`.
  No required basin family has yet been formally inhabited.

### Computational evidence, not formal proof

- The literature computation already reaches at least N=34 and found draws at every parity-eligible
  size through that point. N31/N32 were therefore not novel computational targets.
- The packed executable solver was independently scalar-checked at N=23,24,27,28 and reports every
  opening drawn. Its self-tests compare three formulations through N=10, random N=12 states, and
  the published N=3..20 table. These results are not connected to `CatchUp.value` by Lean proofs.
- The fixed one-residual/two-pending product search puts both protected opening-one roots in its
  basin at all four tested lifts 7→11, 8→12, 11→15, and 12→16.
- Complete theorem-root diagnostics give the sharper picture:
  - at 7→11, width two passes every nonvacuous required root;
  - at 8→12, width two passes all old roots and new roots 2↔10, 3↔11, 4↔12;
  - the remaining new root 1↔9 fails at width two but passes separately at width three with
    19,064 searched labels / 2,875 winning and a valid initial ledger.
- Therefore width three is the smallest tested semantic bound covering all nonvacuous required
  roots at the two base lifts. This combines width-two and targeted width-three runs; a single full
  N=8 width-three matrix was not run.

### Failed or narrowed approaches

- Even total weight, even with `2 * max ≤ total`, fails badly on arbitrary counter sets; interval
  structure is essential.
- Raw draw/cardinality lift families are false. At 15→19, 921 of 106,633 reachable cached draw
  states with at least six old counters cease to be draws; failures have six through nine old
  counters, and one draw becomes a loss.
- Fixed complete-turn sequences were initially pooled across residue classes. Splitting residues
  repairs many small replies, but the original validator omitted new high counters. Corrected
  all-reply shortest strategies are unstable and may use five picks.
- Exact old-move matching plus top stutter fails at 8→12, 11→15, and 12→16.
- One-pending asynchronous success relies on replacing pending identities; a no-swap version fails
  at the next sizes.
- Locally re-guessed signed debt is not persistent history. A persistent no-residual ledger needs
  width six at N=7 and seven at N=8, so it is not fixed width.
- Controller extraction remains noncompact: hundreds/thousands of exact phases and unresolved
  repeated-context conflicts. Exact masks/counter identities would overfit the data.
- Universal closure over all statically consistent ledger pairs is uninhabited: unreachable pairs
  can force pending-width overflow. It was removed. Widening the static bound only moves the
  pathology from 2→3 to 3→4.
- Width two has an exact N8 new-root obstruction: while the small guide stutters, large picks
  1,2,3,4 grow pending support `{1} → ∅ → {2} → {2,3} → {2,3,4}`. The score ledger remains exact;
  only the width bound fails.

### Trust boundaries

- The four literal draw theorems use finite `native_decide` checks and have axiom report
  `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`.
- The classifier equivalence, edge-reflection soundness, and local-closure-to-basin theorem do not
  use `native_decide`; their report is the standard
  `[propext, Classical.choice, Quot.sound]`.
- Solver values, solver-selected moves, and extraction order are untrusted. The existing residual
  executable emits diagnostics, not a proof-facing product DAG.

### Artifacts and reproduction

- Branch `codex/catchup-experiment`, HEAD
  `0b67426227811c55db98358c95e99ca5c4465e54`; index empty; 5 tracked modified and 17 untracked
  files; other worktrees untouched; no commit/push/PR/remote write.
- Fresh final build: `lake --wfail build CatchUpResearch` passes all 8,091 jobs.
- `git diff --check` is clean. No `sorry`, `admit`, or declared `axiom` occurs in the audited
  simulation/checker/certificate sources.
- Certificate SHA-256 values:
  - N11 `4fe0d76485aa022074386758ea0991e8c0cf3a1dd43331c16d394ebd2bb9a5da`;
  - N12 `8779dfb7010cbed7719ebbb3b383cf82e63833d46d545be830feed8739ba07d9`;
  - N15 `bb90ec85b7c9160ef53d89e39ba31f921f084e5b824451b7e5b9125d1138d010`;
  - N16 `0c2d2a40cc76a4e0c5558d74efb7402f676d51157d7271e097229b48a1a26304`.
- Final `SimulationLedger.lean` SHA-256:
  `ed9656fd9afcd9ba55e0174db507239442846bfea1b91a11813b072294e67f42`.
- Core reproduction commands:
  - `lake --wfail build CatchUpResearch`;
  - `lake env lean scripts/catch_up/N11Certificate.lean` (and N12/N15/N16 analogues);
  - `lake env lean --run scripts/catch_up/PartialCertificateMain.lean 15 8 --emit`;
  - `lake env lean --run scripts/catch_up/PartialCertificateMain.lean 16 8 --emit`;
  - `lake env lean --run scripts/catch_up/SimulationBasinMain.lean --async-residual-roots 2 7`;
  - `lake env lean --run scripts/catch_up/SimulationBasinMain.lean --async-residual-roots 2 8`;
  - `lake env lean --run scripts/catch_up/SimulationBasinMain.lean --async-residual-new-root 3 8 1`.

### Strongest remaining route

1. Create a new product-certificate module importing `SimulationLedger`; do not grow that semantic
   module further.
2. Encode each key as `(small State, large State, FourLiftLedger)` and each edge as
   `(large counter, optional ghost counter, exact child key)`.
3. Independently check bounded decoding, unique keys, root/child containment, parent `Related`,
   proof-backed target or safe terminal, exact large legality/child, one owner edge, and exhaustive
   opponent coverage equal to the decoded legal-counter list. Reuse `advanceCheck` for ghost/ledger
   transition semantics.
4. Prove checker truth defines an `ExplicitFourLiftLocallyClosed` relation. Root containment plus a
   certified safe ghost then gives basin membership via `.to_basin`.
5. Add an untrusted emitter retaining selected residual product branches; serialize and independently
   check only the required N7/N8 old/new roots first.
6. Package certified root memberships through the sharpened draw theorem.
7. Benchmark before large literal emission: the exact safety classifier is unmemoized and the
   history checker scans O(N) ranges at every edge.
8. Only after finite product certificates pass should the work return to extracting a symbolic
   parametric reachable-phase invariant.

## Final consolidation freeze — 2026-08-08 07:15 EDT

- The research scope was frozen at the scheduled consolidation time; no further conjectural search
  or implementation was started after this point.
- A fresh post-freeze `lake --wfail build CatchUpResearch` completed successfully with all 8,091
  jobs. This build includes the final edge-reflection and local-closure declarations.
- `git diff --check` remained clean, the Git index remained empty, and a fresh scan found no
  `sorry`, `admit`, or declared `axiom` in the audited simulation, checker, and N11/N12/N15/N16
  certificate sources.
- The final branch, file inventory, sizes, and SHA-256 values agree with the consolidated report
  immediately above. No file was staged or committed, and no branch, remote, issue, or pull request
  was changed.
