> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current results guide](../../results/README.md).

# Exact search audit and one root-derived experiment

C remains open. No N39/N40 result or counterexample certificate was found in the recovered evidence. This work changes only this search directory and performs mathematical diagnostics, with no machine work.

## Strongest available reuse and fidelity

- For practical exact interval/subset queries, reuse `deficit_two/upstream/catch_up_search.cpp.txt`: `PackedExactTable` supports N<=31; `WideExactTable` supports exactly N32. The archived file is byte-identical to the original 4b0d worktree source. Its pinned SHA256 is `b3cf5acf0ec7164e4dcdc85d820443d11af80a735fa7aa377e2796af25c120d2`.
- The packed engine computes all deficits simultaneously. `verifyScalar` independently reconstructs **every** stored ternary label from atomic scalar moves, not the packed reflection formulas. It shares counter/mask decoding and child labels, so this remains an executable cross-check, not a Lean certificate. The full all-label recurrence check is the parent audit gate.
- The same file has independent absolute-score/opening and completed-turn semantic oracles. Its existing self-test compares all three through internally consistent N10 states, plus complete ordered-turn generation through seven counters. That self-test was inspected, not rerun here.
- `seven_pairs/slots.hpp` is preferable for sparse supports: <=14 supplied distinct positive labels, each <=10000, with actual magnitudes retained. It uses a separate uncomputed marker and an exact memoized scalar recurrence. Existing comparison/replay logs cover141312 common queries and selected absolute-score checks; these old logs were not rerun here.
- All these solvers maximize **win/draw/loss**, not final score difference. They preserve the same player's perspective when x<d, and negate exactly when x>=d; equality ends the turn. The literal solver explicitly forces one opening pick. A normalized positive tied interval root also takes one pick, matching the opening rule.
- Domain caveats: packed `outcome(mask,d>N)` returns loss and is not an arbitrary-deficit oracle (e.g. {1,2},d3 actually draws). Root-reachable deficits are <=N. The absolute oracle packs65 bits into64 at N32, dropping mask bit31; arbitrary queries can collide, although score conservation prevents that collision inside a fixed internally consistent interval game. The turn-boundary key reserves six deficit bits. `ExactSlots` requires a valid mask. None of these caveats affects the present N24-domain queries.

## Actual frontier versus reports

The original C++ README records exact draws, every opening drawn, at N23,24,27,28,31,32. It records full scalar verification and timings: N31 about87.6s solve+268.3s verify, N32 about211.3s+659.8s. We have not replayed those frontier jobs. Its saved /tmp tables for N23,24,27,28 are absent now. N35/N36 are MCTS means only. N39/N40 exact leads in the prior recovered log are unfinished; no checked win or non-draw certificate is available.

The strongest recovered proof-producing checker is the pinned upstream `OpeningPackedIndexedCertificate` pipeline over indexed one-sided strategy DAGs. Its generic soundness proof connects legal edges, all opponent moves, safe terminals and strict progress to `CanAvoidLoss`, then root draw. Pinned `CatchUpCertifiedThrough28` composes finite cases; N27/N28 payload checks use `native_decide`. Those instances have a native-computation trust boundary and were not rebuilt here. Existing downstream symbolic theorem/axiom-audit results have a separate kernel-replay status. No C++ answer below is a formal proof premise.

Storage in the current implementation is10*2^N bytes for N<=31,18*2^32 bytes for N32 (72GiB), before overhead. Thus N24 uses160MiB for arrays; N28 uses2.5GiB; N31 uses20GiB. Naively extending64-bit words would need576GiB at N35,9TiB at N39,18TiB at N40; these are estimates for an **unimplemented** extension. The current exact program rejects N>32. The successful local N24 run used169459712 bytes peak RSS; compiler peak204914688 bytes was still below512MiB. Host total memory could not be queried within the sandbox.

## Completed bounded experiment

Use one table at N24 to query every lower-ray root
`L(N,b)=([1..N]\{1,b}, b-1)`, all2<=b<=N, for eligible N in
`3,4,7,8,11,12,15,16,19,20,23,24`.
These are genuinely root-derived: Player1 opens1, Player2 picksb, then Player1 faces deficitb-1. Smaller intervals are exact submask queries of the same table. All150 cases completed:145 draws and5 wins, no loss. This includes N16 and N20 directly; no larger table was allocated. Every legal first reply's exact move outcome was considered, preserving same-player continuations.

The adaptive uniform candidate was:
`{b-1,b+1,largest_remaining} ∩ remaining` contains a nonlosing reply.
It fails exactly at:

| (N,b) | Complete safe reply set | Proposed legal candidates | Ray value |
|---|---|---|---|
| (4,4) | {2} | {3} | win |
| (7,6) | {2,3,4} | {5,7} | win |

At (7,6), replies2,3,4 each win;5 and7 each lose. Thus the failure is not caused by confusing nonloss with strict win. Across all150 cases,
`max_(N,b) min_(safe x) |x-b| = 2`, attained at(4,2),(4,4),(7,6).
Every case has a safe reply within distance2 ofb; this is bounded evidence for a new uniform nearby-reply hypothesis, not an unbounded theorem. All full safe sets and candidate sets are in `adaptive_results.json` and the final log.

There are133 cases in which **every** available first pick is safe. In particular, this holds in all122 cases with tested N>=12 (N12,15,16,19,20,23,24). At N11 only5 of10 cases have every pick safe; their safe-count range is6..9 out of9 available picks. The earlier all-safe counts are2/2 at N3,0/3 at N4,2/6 at N7,2/7 at N8. These are exact safe-set counts, not assertions that arbitrary later play stays safe.

The same table also tests the exact-deficit reply x=b-1 for135 cases with N>=7,b>=3. It loses exactly at(7,4),(7,6),(8,3), because the tied residual is winning for the opponent. The stronger canonical residual opening rule (open4 ifb3, otherwise2) has7 failures: (7,3),(7,4),(7,6),(7,7),(8,3),(8,5),(8,7). For every tested eligible N>=11, all124 tied residuals are draws and all canonical children are draws; none is non-draw. No threshold theorem is inferred. The global smallest eligible exact-deficit failure is the trivial N4,b3 root trace1,3,2, leaving opponent counter4; it is only a control, not a formalization target.

Independent literal-score replay uses the existing `verify.absolute` evaluator, with actual scores1 andb after the opening prefix. It checks all first moves, complete safe sets, candidates and distances for39 adaptive cases through N12. It also replays all30 N7,8,11,12 exact-deficit/canonical cases and every residual opening; every comparison passed. No arbitrary sparse state is claimed root-reachable.

## Reproduction and evidence boundary

From repository root:

```
clang++ -std=c++20 -O3 -pthread research/catchup/campaign_2026_10_22/search/lower_ray_probe.cpp -o research/catchup/campaign_2026_10_22/search/lower_ray_probe
research/catchup/campaign_2026_10_22/search/lower_ray_probe > research/catchup/campaign_2026_10_22/search/adaptive_ray_probe.log
python3 research/catchup/campaign_2026_10_22/search/absolute_replay.py
```

Each child had a30s cap. Final compile took1.047s; final table solve0.424s and scalar check3.107s within a4.716s process; final literal replay0.221s. All experimental child times including exploratory reruns sum18.287s. `run.json` contains exact command arrays, command-JSON hashes, output hashes, exit codes and RSS scope. `manifest.json` pins final sources/binary/outputs. Final accepted output is `adaptive_ray_probe_final.log`; the original `lower_ray_probe.log` retains the initial135-case experiment. A superseded exploratory adaptive run included an irrelevant illegal canonical opening at N3; that output is not final evidence. The final program restricts canonical tests to their stated N>=7 domain.

The single highest-value result is the **all-b adaptive nearby-reply test**, not a larger interval value. It refutes the three-candidate rule on root-derived states while leaving the clean distance<=2 hypothesis alive across all150 cases. The distance statistic is diagnostic only; no new pattern-driven experiment is recommended before selecting a strategy mechanism. A structural argument must confront(7,6) and quantify allb; patching its preferred move or increasing N would not establish closure.

## Provenance correction after cross-repository audit

The pinned upstream `bb10b8246c8f7b99de084865826150459e5627f1:CATCHUP_FINAL_REPORT_20260812_0122_ET.md`, section "Lower-ray evidence and sharp boundary", already reports every exact-deficit tied residual through eligible N28, with exactly the same five small winning exceptions, and974 adjacent-response local challenges. The N24 lower-ray work above is a weaker reproduction and diagnostic solver replay, **not a novel mathematical result**. Its usefulness is source fidelity, complete safe-first-pick sets, and reproducible resource measurements. No further lower-ray or density-pattern experiment was started on that basis.

The next authorized question is the old `DenseHoleQualifies` hierarchy, including its saturated and prefix-blocked boundaries. Prior report duplication audit found exhaustive qualifying-state passes at (N,k)=(9,3),(12,4),(15,5),(16,5),(18,6),(21,7), wherek is the allowed hole count. These domains are reproductions. No complete all-N<=24 hierarchy gate or N24,k8 gate was found. See pinned `CATCHUP_CAMPAIGN_20260808_2206_ET.md:1767–1773`. Its lines1931–1935 already record the one-over-density even losses at N9,h4 and N12,h5. The new test will retain these distinctions.

## Completed dense-hole boundary audit

The separate `dense_boundary_probe.cpp` uses the unmodified archived N24 exact table. It tests the old predicate literally: S⊆[1,N], h=N−|S|,3h<=N,0<=d<=N,sum(S)>=d, and(d+sum(S)) even. **All ambient N0..24 are included**, with no interval-eligibility restriction. Saturated h=floor(N/3) and prefix-blocked states (no available x<d) are queried first at eachN, followed by the interior. Every qualifying subset/deficit is enumerated;117 exact(N,h) domains completed.

There is **no losing qualifying state** in27,572,106 cases:27,055,237 draws and516,869 wins. Wins do not refute the nonloss target. The boundary union contains17,457,201 cases, including16,365,432 saturated cases; the prefix-blocked subset contains2,768,955 cases (the subsets overlap). An independent combinatorial parity-count calculation exactly matches every domain count and every prefix count. The minimum possible sum of a qualifying support is at leastN, independently confirming that the catchability filter removes no extra d<=N case. These finite passes include old reproduction domains identified above; they do not prove the unbounded hierarchy.

At N24 alone all h0..8 pass, including9,193,635 saturated h8 states (8,998,364 draws,195,271 wins). The same query round then completely searches successive hole layers above the density threshold until the first layer containing losses, separately at eachN. Full layer counts, nearest-layer deficit ranges and all qualification counts are in `dense_results.json`. It checked no loss at any depth for N0..3. For N4..24, the nearest losing hole counts are respectively:

```
N: 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24
h: 2 2 3 3 3 4  4  4  5  5  6  7  6  7  8  8  8  9  9 10 10
```

The globally smallest outside-threshold loss is N4,h2,S={3,4},d3; both legal first moves lose. At N24, h9 also has zero losses (16,343,800 cases); h10 has exactly7 losses in24,515,304 cases, with deficits11..13, remaining sums223..227 and minimum remaining counter1 or2. A focused output-only export reproduced this already-tested layer to retain all7 states and all98 first-move outcomes. Every move loses in every state; hence every safe-first-pick set is empty. No new ambient size or mathematical domain was introduced by the export.

Independent literal-score replay confirmed all21 representative nearest-layer losses and every legal first move, including the first N24 witness. A further replay confirmed **all7 N24 losses and all98 legal first moves**, retaining full supports and move values in `dense_export_replay.json`. Literal replay uses actual scores(0,d), preserves the same player below the deficit, and switches on equality/overshoot. These outside-threshold states are not asserted reachable from interval roots and are not counterexamples to C or to DenseHoleQualifies.

**No nearest losing layer contains a deficit-zero loss.** This was checked by the complete per-layer deficit extrema: each minimum losing deficit is positive. Deeper layers after the first losing layer were not completely searched, so this audit makes no claim about all tied finite-set roots.

The dense table's419,430,400 labels were fully scalar-verified once. That job completed in7.103s wall time with202,981,376 bytes peak RSS; independent count/representative replay took0.866s, peak64,733,184 bytes. Export plus its compilation took2.527s; all-seven literal replay took2.522s, peak63,897,600 bytes. All dense experimental children including compilations sum14.113s; each child had a30s cap, and no cap or512MiB memory boundary was reached. No largerN was run. `dense_run.json` records commands, command hashes, output hashes and return codes; `dense_manifest.json` pins the final source and evidence files. Use the original full-check log `dense_boundary_probe.log` for the universal finite-domain conclusion; the export is only a diagnostic replay of the already-completed N24,h10 layer.

The old saturated/prefix-blocked closure remains a mathematical proof obligation. This audit identifies a finite safe boundary and nearby explicit losses; it supplies neither a uniform strategy mechanism nor an induction proof.

## Completed dominant exact-block predicate test

This new test is the precise structural corollary under formalization, not an interval-C defense or a move policy. For everyd=1..24 and every S⊆[1,d], let the **actual** hole count beh=d−|S|. It assumes2h<=d−1 and that every integer1<=t<h is a subset sum ofS. **No parity condition is applied.** All156(d,h) domains completed using one unmodified N24 table, whose419,430,400 labels passed full scalar verification once.

The test examined14,946,945 supports meeting the density bound. Exact subset-sum bits throughh were computed for every support; their complete-prefix criterion agreed with the independently implemented sorted-coin coverage criterion on every support. Of these supports,4,114,796 meet the representability predicate. Every one is nonlosing:949,602 draws,3,165,194 wins, zero losses.

For every qualifyingS, the explicit max-containing exactdblock was reconstructed and checked. WriteM=maxS,k=d−M. The density bound givesM>=|S|=d−h>=h+1, hence0<=k<=h<M. For k0 use{M}; for0<k<h reconstruct a subsetA summing tok and adjoinM; for k=h>0, allh holes are already aboveM, forcing S=[1,M] andk∈S, so use{k,M}. Counts are2,299,503 singleton-max blocks,1,815,161 reconstructed-subset blocks, and132 forced-tail blocks. EveryB satisfies B⊆S,sumB=d,maxS∈B; subset reconstruction uses descending updates to prevent repeated counters.

Every legal first move was evaluated with optimal unrestricted continuations:57,796,759 first moves, including55,497,256 below-deficit same-player continuations. Every qualifying case has at least one safe first move. **This does not say that playing the constructed block is safe.** The required control S={1,2,3},d3 has valuewin but first-move outcomes1:loss,2:win,3:loss; the constructed block is the losing first move{3}. Thus neither minimum/maximal-counter play nor direct block-play is inferred.

Independent Python enumeration used full exact subset-sum sets to re-enumerate all qualifying cases throughd10, including vacuous h0/h1 cases. All404 cases, every2,463 legal first pick, and all2,207 same-player continuations agree with the existing literal absolute-score recurrence. These404 cases include203 odd and201 even effective totals, confirming that parity was not silently assumed. The independently checked block supports, safe first moves and complete move outcomes are preserved in `dominant_block_replay.json`; `dominant_results.json` contains all156 domain counts and the full summary. An initial replay hit the installed Python's missing `int.bit_count` method; the compatibility correction and failed receipt are retained, and the final full replay passed.

The exact-table process took5.469s and202,948,608 bytes peak RSS; its scalar check took3.014s. Final independent replay took0.155s and16,220,160 bytes peak RSS. All child jobs including compilation and the recorded compatibility failure sum6.748s, with30s caps and no512MiB boundary reached. `dominant_run.json` records exact commands and hashes; `dominant_manifest.json` pins final sources, outputs and receipts. The earlier probes and their experimental domains were preserved. No largerN, machine work, or additional strategy-pattern search was run.

The finite test supports the proposed mathematical nonloss corollary and its block-construction hypotheses. The parent formal proof, rather than these external solver outcomes, is the intended unbounded guarantee.

## Completed maximal-block subsum-gap dichotomy test

The separate `subsum_gap_probe.cpp` checks all ambientN0..16, all S⊆[1,N] with actualholesh, and everyd satisfying2h+1<=d<=N. There is no parity guard. The one N16 exact table passed a complete scalar check of1,114,112 labels. All444(N,h,d) domains completed:201,213 states, independently counted as100,599 even and100,614 odd effective totals.

Exactly27 states lose. Every one satisfies the refined dichotomy:23 upper cases and4 lower cases, all27 odd. For each loss the test selects the **largest counterb occurring in any exactdblock**, reconstructs such a blockB with maxB=b, and verifiesb>=d−h and|B|<=h+1. It checks that S\B is a tied win, has exactly one winning openingw, thatw>b, and that the post-opening child is a loss. All215 original legal first picks are losses with correct perspective;89 are below-deficit continuations by the same player.

For the23 upper cases,w>d and the larger-deficit post-opening child loses. For the4 lower cases,w<d,t=d−w lies in1..h−1, **no subset of the originalS sums tot**, and the original same-player pickw continues to a loss. Their gaps are1,4,1,1. For example S={1,5,6,7,8,9},N11,d11,h5 has b6,B={5,6},w7,t4; the gap is not explained merely by absence of counter1. All27 complete witnesses, their blocks, residuals, parity and original move outcomes are retained in the log and `subsum_gap_results.json`.

A read-only additive audit confirms the selection argument: ifd is missing, it consumes one hole, while theh pairs{i,d−i},1<=i<=h, are disjoint underd>=2h+1. Some pair survives, implyingb>=d−h. In a lower case,w>b>=d−h>=h+1>t; any subset summing tot would excludew, and adjoiningw would contradict maximality ofb. This identifies the precise subset-sum obstruction; it does not prove interval C or a nonloss claim with arbitrary maxima.

Independent Python full subset-sum sets verify block-member maximality and every additive gap assertion for **all27 witnesses**. Literal-score replay verifies every witness throughN10 and the first maximum-ambient representative of each branch (upperN16, lowerN15):15 states, including every original first move, every residual opening (confirming uniqueness), the post-opening loss, and both absolute-score forms of each selected lower continuation. All passed. All444 candidate-domain counts independently match binomial coefficients. No unrecorded opponent policy is assumed.

The C++ process took0.339s and2,621,440 bytes peak RSS; independent replay took0.839s and119,242,752 bytes peak RSS. Compilation plus both jobs sum2.172s, with30s caps. `subsum_gap_run.json` contains exact commands/output hashes; `subsum_gap_manifest.json` pins final sources and evidence. Earlier probes were preserved. The prior cheap2617-state even-total test throughN12 remains bounded evidence, not a theorem; this task did not promote it or investigate a broader predicate.

## Completed high-deficit even-total cheap-kill test

The new `high_deficit_even_probe.cpp` tests the narrow hypothesis suggested after the loss-dichotomy checkpoint: S⊆[1,N], actual holes h=N−|S|, and 2h+1<=d<=N; classify both parities of d+sum(S), with **no subset-sum hypothesis**. The proposed nonloss conclusion applies only to the even class. This differs from the old ambient-density condition 3h<=N, and no uniform theorem is inferred from this finite pass.

All ambient N=0..24 and all 1,378 relevant (N,h,d) domains completed. The test classified 63,943,359 states:

| Effective-total parity | Loss | Draw | Win | Total |
|---|---:|---:|---:|---:|
| Even | 0 | 23,471,566 | 8,500,015 | 31,971,581 |
| Odd | 44 | 0 | 31,971,734 | 31,971,778 |

No even counterexample was found, so there is no first-even-loss witness to replay. The odd losses are not counterexamples to the proposed even-total statement. At N=24 alone the complete domain contains 32,449,872 states, of which 16,224,936 are even. No catchability condition was silently imposed: all supports in the stated domain were counted, and none was uncatchable.

The unmodified N=24 exact table received a fresh full scalar check of 419,430,400 labels. An independent combinatorial checker verifies every domain's binomial support count, every even/odd count using the parity of the deleted labels, and exact coverage of the full set of domain triples. It also matches all 444 N<=16 domain loss counts against the prior subsum-gap run. The complete per-domain outcome counts are saved in `high_deficit_even_results.json`.

The exact-table process took 4.071s and 202,932,224 bytes peak RSS; its scalar check took 3.025s. Compilation, the table process and the independent count checker sum 5.066s, with a 30s cap on every child and no memory boundary reached. Exact commands, hashes and exit codes are in `high_deficit_even_run.json`; `high_deficit_even_manifest.json` pins the final source and evidence. No larger N or additional pattern test was run.

The motivation remains conditional: a uniform proof would handle original interval openings x>=3, since those roots have h=1, d=x and effective total equal to the interval's total. Openings 1 and 2, including the first-pair obligation, remain outside that argument. The finite computation supplies no proof mechanism for the high-deficit hypothesis, and hole growth remains an unresolved issue.

## Arithmetic of all 44 odd losses

An output-only reproduction of the **same completed N<=24 domain** retained all 44 odd losing supports and all 495 original legal first-move outcomes. Every retained move loses. The export counts match every odd-loss count in the original 1,378-domain audit, and the complete set of 27 witnesses with N<=16 matches the prior subsum-gap witness set exactly. No larger N, new predicate, or large literal replay was used.

The observed margins m=d−2h range only from 1 to 2: 38 losses have m=1, and 6 have m=2. Exact subset-sum sets show that 33 of the 44 supports cover every target 1<=t<h; 17 of these are vacuous h<=1 cases and 16 have nonvacuous coverage. The other 11 supports have at least one genuine low subset-sum gap. The requested arithmetic patterns are defined only by the pair (margin, complete low-subsum coverage):

| Margin | Coverage | Count | First representative (N; S; d) |
|---:|---|---:|---|
| 1 | fails | 11 | 7; {2,3,5,6}; 7 (missing subsum 1) |
| 1 | passes | 27 | 3; {1,2,3}; 1 |
| 2 | passes | 6 | 7; {1,2,4,5,6,7}; 4 |

There is no margin-2 coverage failure in these 44 cases. First nonvacuous representatives for each pattern are also retained in the JSON. Eight losing supports satisfy max(S)<=d; all eight fail low-subsum coverage, consistent with the separate dominant-block corollary. These statistics are finite observations, not a new margin theorem or an explanation proving general exclusion of even losses.

The 44 losses occupy 42 distinct (N,h,d) domains; the two multiplicity-two domains are (19,9,19) and (23,11,23). `high_deficit_odd_results.json` lists **every** domain and every full support, deficit, margin, coverage gap set and first-move outcome, plus first representatives of all three patterns. The canonical witness-subset hash is:

```
4417d91fe0cbecc9ea75d8db06c43a157ad50891021a08ef285c7c2c94b4e73b
```

Its serialization is UTF-8 compact JSON of the lexicographically sorted (N,h,d,remaining-mask) tuples, with comma/colon separators and no trailing newline; the tuples are included in the JSON for reproduction. The arithmetic checker uses full subset-sum sets, independently of the solver's bit encoding. Export compilation, export and arithmetic checks took 1.927s; all jobs in the complete high-deficit round now sum 6.992s, each capped at 30s. The export peak was 202,915,840 bytes. All earlier probes and their logs remain preserved.

## Completed parity-flipping construction attempt

`construction_probe.cpp` takes each of the 44 saved odd losing seeds (S,d,N), with r=|S| and h=N−r, and evaluates two explicit constructions using the **unmodified** `seven_pairs/slots.hpp` solver:

- Shift/prefix: S'={1,2}∪(S+2), d'=d+2, N'=N+2. The new sum is sum(S)+2r+3, effective total changes by 2r+5, holes remain h, and margin d−2h increases by 2.
- Top padding: S'=S∪{N+1,N+2}, d'=d, N'=N+2. The new sum changes by 2N+3, effective parity flips, holes remain h, and margin is unchanged.

Both constructions produce even effective total and retain 2h+1<=d'<=N'. Shift/prefix reaches margin at least 3. **No translation or outcome-preservation rule is assumed.** Only the permitted r+2<=14 cases are solved: 28 eligible seeds give 56 exact constructed states; the other 16 seeds give 32 explicit skipped construction records at the frozen 14-label limit. Every seed, skip, transform equation, full new support and legal first-move outcome is retained in `construction_results.json`.

| Construction | Loss | Draw | Win |
|---|---:|---:|---:|
| Shift/prefix | 0 | 13 | 15 |
| Top padding | 0 | 28 | 0 |

Thus this natural attempt produces no counterexample to H or the stronger margin threshold. It establishes no general outcome-preservation or nonloss rule.

There are four new ambient-N=25 cases, from the two N=23 seeds with 12 labels. They use only 14 supplied labels; **no N=25 interval table is built**. Shift/prefix of seed 41 wins; its top padding and both constructions of seed 42 draw. Independent literal-score replay verifies all four cases and all 56 legal first picks, including 52 same-player continuations. Every transform and skip is independently checked against the saved original seeds and the exact parity/hole/margin equations.

The C++ process took 0.359s and 2,424,832 bytes peak RSS; independent literal replay took 1.687s and 65,306,624 bytes peak RSS. Compilation and both jobs sum 2.578s, each capped at 30s. `construction_seed_manifest.json` pins the seed extraction; `construction_run.json` records commands and output hashes; `construction_manifest.json` pins the frozen slot solver, sources and completed evidence. These are sparse auxiliary states, not original interval counterexamples. All earlier probes and logs are preserved.
