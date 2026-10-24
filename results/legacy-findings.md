# August–September findings

The conjecture remains open. This ledger connects the earlier campaigns to the current collection. Evidence labels record the archival integration's assurance: a report of a historical successful check is not a fresh replay. All 43 entries preserve scope, dependencies, limitations and provenance in [the machine-readable ledger](legacy-findings.json). A later [verified fifth-endpoint port](fifth-endpoint.md) separately updates the present status of CU-L037; it does not promote the rest of the archived module or campaign.

The [campaign index](../archive/campaigns/README.md) lists all source versions, notebooks, reviews, retained observations and missing artifacts. See [current routes](research-routes.md) before treating a historical next step as current.

The [endpoint ports](lower-ray-endpoints.md) separately update the current status
of CU-L021 and CU-L032. The [finite-controller replay bundle](../computation/experiments/earlier-campaign/two-buffer/)
rechecks the retained CU-L026 policy computationally. Its archived Lean protocol
does not receive a fresh build claim from that replay; the original ledger's
historical evidence remains intact.

## Reading the evidence

- **Current Lean library:** the named source is already part of the pinned build and prior axiom audits; this import leaves it unchanged.
- **Archived Lean source:** the proof text is available for inspection but was not built or audited in this import.
- **Historical native computation:** the concrete result relies on the previously disclosed compiler/native-evaluation boundary.
- **Historical exact/heuristic computation:** a retained run record, with no new outcome assurance from this archival task.
- **Report-only or informal:** a claim/argument remains useful, but the reported scratch artifact may be missing.

## Claims and their boundaries

### CU-L001 — Semantic audit and normalized recurrence

The audited game forces one opening pick, continues later turns only while behind, switches at equality, and awards the remainder when catching is impossible. The deficit evaluator agrees with the score-based reference.

Evidence: current Lean library; historical semantic audit. Scope: finite natural-number supports; normalization assumes the mover is tied or behind (me≤opponent); intended interval play uses positive counters.

The separately implemented C++ solver still needs its own checks; recurrence agreement does not certify arbitrary code.

Sources: [catchup_final_report_20260808_2206_et--7d784e0a.md](../archive/campaigns/reports/catchup_final_report_20260808_2206_et--7d784e0a.md), [Reference.lean](../CatchUp/Reference.lean), [Executable.lean](../CatchUp/Executable.lean).

### CU-L002 — Historical certification through 28

The August campaign reports value(Icc 1 N)=draw for every N≤28 with even triangular total.

Evidence: historical Lean native computation; source inventoried, large payloads not exported. Scope: initial intervals N≤28.

Concrete checks rely on Lean.ofReduceBool and Lean.trustCompiler. This is not a freshly replayed kernel-only range result in this collection.

Sources: [catchup_final_report_20260808_2206_et--7d784e0a.md](../archive/campaigns/reports/catchup_final_report_20260808_2206_et--7d784e0a.md), [CatchUpCertifiedThrough28.lean.txt](../archive/catch_up/CatchUpCertifiedThrough28.lean.txt).

### CU-L003 — Dense three-hole family through 25

The report certifies DenseThreeHoleNonloss N for 9≤N≤25: catchable support in Icc 1 N with at most three holes, deficit≤N and even effective total is nonlosing.

Evidence: historical Lean native computation. Scope: bounded ambient N, quantified irregular supports.

These are finite families. Their certificates do not establish an unbounded density invariant; large native payloads need a separate audit.

Sources: [catchup_final_report_20260808_2206_et--7d784e0a.md](../archive/campaigns/reports/catchup_final_report_20260808_2206_et--7d784e0a.md), [DenseThreeHoleCertifiedRange.lean.txt](../archive/catch_up/DenseThreeHoleCertifiedRange.lean.txt).

### CU-L004 — One drawn opening and two protected certificates

At N=27,28 the campaign uses opening one and separately certifies nonloss for each protected player at that same root. The draw-opening criterion then gives the initial draw.

Evidence: historical native certificates; current kernel proof of the draw-opening criterion. Scope: initial intervals N=27,28.

The historical certificates prove one drawn opening, not every opening drawing. The generic criterion and finite evaluations have different trust footprints.

Sources: [catchup_final_report_20260808_2206_et--7d784e0a.md](../archive/campaigns/reports/catchup_final_report_20260808_2206_et--7d784e0a.md), [OpeningPackedIndexedCertificate.lean.txt](../archive/catch_up/OpeningPackedIndexedCertificate.lean.txt), [DrawOpening.lean](../CatchUp/DrawOpening.lean).

### CU-L005 — Indexed and packed strategy certificates

The indexed checker verifies exact child states, owner choices, all opponent edges and coverage. The packed decoder checks tags, digits, lengths and trailing fields before those obligations.

Evidence: archived Lean sources; generic soundness reported historically. Scope: specified finite certificate formats.

These archived formats are not the C++ binary table format. No archived indexed checker was newly built in this import.

Sources: [catchup_final_report_20260808_2206_et--7d784e0a.md](../archive/campaigns/reports/catchup_final_report_20260808_2206_et--7d784e0a.md), [LinearIndexedCertificate.lean.txt](../archive/catch_up/LinearIndexedCertificate.lean.txt), [PackedLinearIndexedCertificate.lean.txt](../archive/catch_up/PackedLinearIndexedCertificate.lean.txt).

### CU-L006 — Independent N27/N28 audits

The August report describes complete Bellman checks, scalar samples, strategy-field replay, negative controls and W/D/L counts for N27/N28. Table-label counts differ from initial-game counts; not all supporting programs or tables are available.

Evidence: historical exact computations; independent audit tools and binary tables partly unrecovered. Scope: fixed tables and certificates N=27,28.

The audits were not rerun. Missing temporary programs, tables and receipts cannot be replaced by the narrative alone.

Sources: [catchup_final_report_20260808_2206_et--7d784e0a.md](../archive/campaigns/reports/catchup_final_report_20260808_2206_et--7d784e0a.md).

### CU-L007 — Counterexample lower bound and two-family normal form

Reported scratch result: a parity-admissible counterexample must have N≥31 and yield a loss in A(N,b)=((Icc 1 N)\{1,b},b−1), 2≤b≤N−2, or B(N,x)=((Icc 3 N)\{x},x−1), 3≤x≤N−2. Both retain the top two counters.

Evidence: report-only Lean check; proof artifact unrecovered. Scope: hypothetical admissible initial counterexamples.

The N≥31 clause inherits native finite certificates. The scratch proof was not integrated and is absent at its recorded location. Preserve the claim without current formal assurance.

Sources: [catchup_final_report_20260812_0122_et--b286d3c5.md](../archive/campaigns/reports/catchup_final_report_20260812_0122_et--b286d3c5.md).

### CU-L008 — Four remaining August obligations

The reported normal form closes if A(N,2) and B(N,3) are nonlosing, value(TA(N,b))≠win for TA(N,b)=Icc 2 N\{b−1,b}, 3≤b≤N−2, and value(TB(N,x))≠win for TB(N,x)=Icc 3 N\{x−1,x}, 4≤x≤N−2, for every N≥31 with even triangular total. Here value(TA) and value(TB) are tied initial-game values, not positive-deficit values.

Evidence: conditional research interface from a report; parent scratch missing. Scope: admissible initial intervals via residual states.

None of the four unbounded families was closed by that campaign. Deleted exact-deficit counters make b=2 and x=3 exceptional. Later local theorems do not silently close all four.

Sources: [catchup_final_report_20260812_0122_et--b286d3c5.md](../archive/campaigns/reports/catchup_final_report_20260812_0122_et--b286d3c5.md).

### CU-L009 — One common opening suffices for a four-lift

Reported scratch transfer: transferring both fixed-player nonloss guarantees at one common old opening that draws in the smaller game suffices for a root draw at N+4.

Evidence: report-only Lean check; three transfer artifacts unrecovered. Scope: conditional N→N+4 transfer.

The transfer hypotheses still need a uniform strategy. Neither every-opening transfer nor new-opening transfer is necessary for this sufficient interface.

Sources: [catchup_final_report_20260812_0122_et--b286d3c5.md](../archive/campaigns/reports/catchup_final_report_20260812_0122_et--b286d3c5.md).

### CU-L010 — Two nonlosing openings and its wording ambiguity

The August report states that two distinct legal openings with post-opening value ≠win force the root to draw; it attributes this to winning-opening uniqueness and the draw-opening criterion.

Evidence: informal consequence with reported scratch check; artifact unrecovered. Scope: arbitrary nonempty supports, conditional on two specified openings.

The later sentence saying “the statement is false for arbitrary even-total sets” is ambiguous: it must refer to existence of such openings, not this conditional implication. No unqualified existence theorem is adopted.

Sources: [catchup_final_report_20260812_0122_et--b286d3c5.md](../archive/campaigns/reports/catchup_final_report_20260812_0122_et--b286d3c5.md), [WinningOpening.lean](../CatchUp/WinningOpening.lean), [DrawOpening.lean](../CatchUp/DrawOpening.lean).

### CU-L011 — Tied maximum-companion claim

The August scratch report claims a maximum vertex with an outgoing tied-root reply edge has another distinct outgoing edge; an edge a→b means distinct a,b∈S with (afterOpening S a).moveOutcome b=win. It reports a 94,957-root audit of eligible even interval-minus-at-most-five-hole supports through N=23.

Evidence: report-only structural check and historical bounded observations; scratch missing. Scope: tied-root reply graph.

The report does not expose the scratch theorem's full quantified signature, so its exact additional hypotheses are unrecovered. Do not adopt an unrestricted theorem or apply it to the shifted deficit-one graph: September supplies a counterexample to that migration.

Sources: [catchup_final_report_20260812_0122_et--b286d3c5.md](../archive/campaigns/reports/catchup_final_report_20260812_0122_et--b286d3c5.md).

### CU-L012 — Lower-ray tied-residual observations

For every tested N≤28 with even triangular total and 3≤b≤N, the tied game on R_N(b)=Icc 1 N\{1,b−1,b} drew except winning cases (4,3),(4,4),(7,4),(7,6),(8,3). No tested residual lost. An adjacent-response policy passed 974 local challenges at N=15,16,19,20.

Evidence: historical exact computation; standalone reproducer unrecovered. Scope: specified finite interval residuals.

Repeated policy closure fails as holes grow. These observations give neither a parametric theorem nor a complete adversarial policy.

Sources: [catchup_final_report_20260812_0122_et--b286d3c5.md](../archive/campaigns/reports/catchup_final_report_20260812_0122_et--b286d3c5.md).

### CU-L013 — Least-safe picks and increasing turns

Certificate mining reports 737,794 independently enumerated continuing least-safe decisions through N=15 with no violation of increasing order; the proposed mechanism is commutation of below-deficit picks and minimality.

Evidence: historical observation; a related increasing-turn result is now in the verified library. Scope: least-safe policy under the stated semantics.

The August proof was interrupted. Current Increasing.lean is the formal authority for its exact later statements and qualifications.

Sources: [catchup_final_report_20260812_0122_et--b286d3c5.md](../archive/campaigns/reports/catchup_final_report_20260812_0122_et--b286d3c5.md), [Increasing.lean](../CatchUp/Increasing.lean).

### CU-L014 — Seven-hole shifted-tail package

The historical report records 61,746,189 antecedent-satisfying tests at M=25..28 for this package. Put h=|[m+1,M]\R|+max(m−1,0), with R⊆[m+1,M] and d+sum R even. Continuation nonloss assumes 1≤m≤M, h≤7 and 1≤d≤min(M−m,sum R). Catch nonwin assumes d≤m and either (1≤m≤M,h≤6) or (3≤m≤M,h≤7), with no catchability requirement. The package fails at smaller M=16..19.

Evidence: historical exhaustive exact computation. Scope: shifted tails with the precise H7/q1, H6/q1, H7/q3 hypotheses.

The clauses and hole-budget definitions are in the archived source; no all-M theorem follows. Independent audit programs are missing at their recorded locations.

Sources: [catchup_final_report_20260808_2206_et--7d784e0a.md](../archive/campaigns/reports/catchup_final_report_20260808_2206_et--7d784e0a.md), [SmallGapShiftedTailPackage.lean.txt](../archive/catch_up/SmallGapShiftedTailPackage.lean.txt).

### CU-L015 — Sharp catch-rank reduction

For natural M,m,d and nonempty catchable R⊆[m+1,M], assume |[m+1,M]\R|+max(m−1,0)≤7, d≤m, d+sum R even, and value(R,d)=win. The archived theorem gives d=0 or an actual winning move x∈R with x≤16, x−d∈[m+1,M]\R, or a tied winning residual R\{x,x−d} of even total with a unique winning opening y>x−d.

Evidence: archived Lean source; historical check only in this import. Scope: conditional shifted upper-tail theorem; zero deficit is an explicit alternative; all values use the current mover's perspective.

All exceptional branches remain obligations. The low-deficit child can still have linearly growing support; it is not a fixed finite leaf.

Sources: [catchup_final_report_20260808_2206_et--7d784e0a.md](../archive/campaigns/reports/catchup_final_report_20260808_2206_et--7d784e0a.md), [ShiftedUpperTailCatchRankReduction.lean.txt](../archive/catch_up/ShiftedUpperTailCatchRankReduction.lean.txt).

### CU-L016 — Strong four-counter state lift fails

Adding {N+1,…,N+4} need not preserve a drawn state: the historical solver records N=11 state ({1,2,8},11) and N=12 state ({6,12},6) becoming wins after lifting.

Evidence: historical exact computations; solver source available. Scope: specified normalized states, not initial interval roots; no new reachability assertion.

These refute the unrestricted statewise lift only. A strategy-specific conditional transfer remains open.

Sources: [catchup_progress--11413716.md](../archive/campaigns/reports/catchup_progress--11413716.md), [catch_up_compare--cb309c49.lean.txt](../archive/campaigns/versions/catch_up_compare--cb309c49.lean.txt).

### CU-L017 — Cardinality cutoff fails at six through nine old counters

At 15→19, only 105,712 of 106,633 cached drawn states with at least six old counters remained draws: 921 failures were recorded, including states with six through nine old counters.

Evidence: historical exact enumeration. Scope: solver-reached cache for the stated size pair.

This refutes the tested cutoff of six and smaller cutoffs. The historical claim that it rules out every fixed cardinality cutoff is stronger than these finite data justify.

Sources: [catchup_progress--11413716.md](../archive/campaigns/reports/catchup_progress--11413716.md).

### CU-L018 — Early simulation phases and ledger obligations

Old-matched/new-stuttering and persistent same-owner ledgers fail selected small lifts; wider local-debt product searches find successful roots. The width-three one-residual ledger supplies sound conditional simulations and exact edge checks.

Evidence: historical product-search evidence plus current generic simulation proof. Scope: specified simulation relations.

Successful searched product witnesses were not uniformly reflected into the required basin-membership theorem. Local phase counts and samples do not prove a bounded uniform controller.

Sources: [catchup_progress--11413716.md](../archive/campaigns/reports/catchup_progress--11413716.md), [catchup_final_report_20260808_2206_et--7d784e0a.md](../archive/campaigns/reports/catchup_final_report_20260808_2206_et--7d784e0a.md), [SimulationLedger.lean.txt](../archive/catch_up/SimulationLedger.lean.txt), [SimulationSoundness.lean](../CatchUp/Earlier/SimulationSoundness.lean).

### CU-L019 — Even totals and balanced allocations are insufficient

Historical exhaustive subsets of 1..12 with even total and twice the maximum≤total yielded 390 nondraws among 1,954 eligible sets; {3,4,5} is a winning support of total 12. Other reports use the winning block {4,5,6,7,8}.

Evidence: historical exact observations; five-counter trap source archived. Scope: irregular supports, not Icc 1 N.

An equal partition or one drawn play does not give two adversarial nonloss guarantees. The finite scan is not freshly replayed.

Sources: [catchup_progress--11413716.md](../archive/campaigns/reports/catchup_progress--11413716.md), [catchup_final_report_20260808_2206_et--7d784e0a.md](../archive/campaigns/reports/catchup_final_report_20260808_2206_et--7d784e0a.md), [FiveConsecutiveTrap.lean.txt](../archive/catch_up/FiveConsecutiveTrap.lean.txt).

### CU-L020 — Exact sum, potential, and hole-count routes need closure

The reports retain counterexamples to fixed matching, static quota partitions, fixed low replies, and scalar outcome classifications. Continuing picks increase holes; true effective-total descent alone does not preserve the necessary support family.

Evidence: historical failures and archived structural sources. Scope: specified proof mechanisms.

Do not treat the broad historical list as a theorem excluding every refinement. Exact witnesses and scope are in the chronological notebook entries.

Sources: [catchup_final_report_20260808_2206_et--7d784e0a.md](../archive/campaigns/reports/catchup_final_report_20260808_2206_et--7d784e0a.md), [catchup_progress--11413716.md](../archive/campaigns/reports/catchup_progress--11413716.md), [EffectiveTotalDescent.lean.txt](../archive/catch_up/EffectiveTotalDescent.lean.txt), [MaximumCounterPotential.lean.txt](../archive/catch_up/MaximumCounterPotential.lean.txt).

### CU-L021 — Antepenultimate endpoint transfer

For N≥7, a draw after opening one at size N−4 implies nonloss of Q_N(N−2), where Q_N(b)=(Icc 1 N\{1,b},b−1).

Evidence: archived Lean source; historical standard-axiom scoped check. Scope: conditional symbolic endpoint.

A draw at the smaller root alone does not identify opening one as drawn. This is one endpoint, with no parity hypothesis.

Sources: [catchup_endpoint_report_20260923_1727_et--ef5aeca3.md](../archive/campaigns/reports/catchup_endpoint_report_20260923_1727_et--ef5aeca3.md), [LowerRayAntepenultimateDescent.lean.txt](../archive/catch_up/LowerRayAntepenultimateDescent.lean.txt).

### CU-L022 — Adjacent-hole copying fails at the first move

At N=11,b=4,y=8, U=({2,5,6,9,10,11},1) draws and V=({2,5,6,7,10,11},1) wins. The map fixing common counters and sending 7→9 sends every nonlosing V move to a losing U move.

Evidence: archived Lean certificate source; historical kernel check. Scope: an admissible auxiliary pair, not a counterexample to no-jump.

The only simultaneous first choices preserving U nonloss and V win are U2,V5, yielding unmatched sets {5,9} and {2,7}. This does not preclude every asynchronous/loss-conditioned repair.

Sources: [catchup_local_exchange_report_20260923_1820_et--3f5dc5a0.md](../archive/campaigns/reports/catchup_local_exchange_report_20260923_1820_et--3f5dc5a0.md), [AdjacentHoleExchangeObstruction.lean.txt](../archive/catch_up/AdjacentHoleExchangeObstruction.lean.txt).

### CU-L023 — Parity and adjacent-pair deletions do not forbid jumps

At deficit one {6,11,14,15,18,23} loses while {4,11,14,15,18,23} wins, despite alternating parity and representation by disjoint adjacent-pair erasures. A distant reply 11 draws after opening 5 in the parent.

Evidence: archived Lean certificate source; historical kernel check. Scope: sparse multiple-pair deletion family.

It refutes the arbitrary-pair extension and the converse neighbor implication, not the original exactly-one-pair no-jump target.

Sources: [catchup_local_exchange_report_20260923_1820_et--3f5dc5a0.md](../archive/campaigns/reports/catchup_local_exchange_report_20260923_1820_et--3f5dc5a0.md), [AdjacentHoleExchangeObstruction.lean.txt](../archive/catch_up/AdjacentHoleExchangeObstruction.lean.txt).

### CU-L024 — Parametric terminal score-debt repair

For natural k, a=k+4,b=2k+5,c=2k+6, protect fixed p1. Actual ({a,b,c},a+1,p2) has a policy taking a maximum on p1 turns against every p2 pick, completing to p1 margin 0 or 2. The chosen shadow trace [c,a] from ({a,c},a,p2) completes to p1 margin 2; actual margin≥shadow margin−2.

Evidence: current Lean library for the repair; historical replay for 404 leaves. Scope: three-counter terminal gadget.

This covers the mandatory actual second-pick 5 branch, not all adjacent-hole roots. Intermediate ledger debt can exceed two.

Sources: [catchup_score_debt_report_20260928_0006_et--bff784af.md](../archive/campaigns/reports/catchup_score_debt_report_20260928_0006_et--bff784af.md), [ScoreDebtTerminalRepair.lean.txt](../archive/ported-inputs/ScoreDebtTerminalRepair.lean.txt), [CompletedMargin.lean](../CatchUp/Earlier/CompletedMargin.lean), [ScoreDebtTerminalRepair.lean](../CatchUp/Earlier/ScoreDebtTerminalRepair.lean).

### CU-L025 — Two stricter debt policies fail

Common copying at the repair entry can give completed margins actual=2, shadow=10. The root rule “take 2, then always maximum” has a legal terminal actual margin −2.

Evidence: archived Lean certificate source; historical kernel check. Scope: specified mandatory root policies.

A failed inequality for one policy does not rule out a richer two-buffer controller; the later finite controller succeeds.

Sources: [catchup_score_debt_report_20260928_0006_et--bff784af.md](../archive/campaigns/reports/catchup_score_debt_report_20260928_0006_et--bff784af.md), [ScoreDebtRepairCertificates.lean.txt](../archive/catch_up/ScoreDebtRepairCertificates.lean.txt).

### CU-L026 — Full mandatory causal two-buffer controller

For protected p1, U=({2,5,6,9,10,11},1,p1) and V=({2,5,6,7,10,11},1,p1), the saved 87-node policy covers every actual opponent move and every strict-win-preserving shadow protected reply, ending with actual margin≥shadow margin−2.

Evidence: archived Lean protocol/certificate and JSON policy; historical kernel check. Scope: one finite paired instance.

Raw remaining-field differences are bounded by two after each pick. Eagerly erasing an early-terminal remainder changes the convention and invalidates this policy. Not a parametric translator.

Sources: [catchup_two_buffer_report_20260928_0834_et--c1fbe535.md](../archive/campaigns/reports/catchup_two_buffer_report_20260928_0834_et--c1fbe535.md), [TwoBufferProtocol.lean.txt](../archive/catch_up/TwoBufferProtocol.lean.txt), [TwoBufferMandatory.lean.txt](../archive/catch_up/TwoBufferMandatory.lean.txt), [two_buffer_policy_20260928--f1d4f917.json](../archive/campaigns/versions/two_buffer_policy_20260928--f1d4f917.json).

### CU-L027 — Two-pick preparation and copied-pair repair

For k≥0 the actual ({k+3,k+4,2k+5,2k+6},2k+6,p1) can take k+3 then 2k+5, reaching ({k+4,2k+6},k+2,p2). The shadow bridge reaches the same pair at deficit k+4. Both opponent choices give a safe two-point terminal margin relation.

Evidence: archived symbolic Lean source; historical check. Scope: parametric local transition/trace family.

Conditional uniqueness of a strict winning shadow reply is not its existence. The transition family does not handle arbitrary initial entries or all branches.

Sources: [catchup_two_buffer_report_20260928_0834_et--c1fbe535.md](../archive/campaigns/reports/catchup_two_buffer_report_20260928_0834_et--c1fbe535.md), [TwoPickDebtRepair.lean.txt](../archive/catch_up/TwoPickDebtRepair.lean.txt).

### CU-L028 — Geometry-free first-pair strategy steal fails

S={3,7,9,14,17,20,29,34} loses at deficit 1 although S\{3} wins at deficit 2, min S=3 and effective total=134. Every first-pick child wins under the actual loss.

Evidence: archived Lean obstruction; historical kernel check. Scope: sparse supports with three held in reserve.

Discarding interval geometry is invalid even with all winning-child obligations. Copying also fails on a size-eight legal prefix [5,7,8,4,6] at a tie, but that prefix is not claimed to follow a supplied winning shadow strategy from its root.

Sources: [catchup_first_pair_report_20260928_0918_et--56c38447.md](../archive/campaigns/reports/catchup_first_pair_report_20260928_0918_et--56c38447.md), [FirstPairDescentObstruction.lean.txt](../archive/catch_up/FirstPairDescentObstruction.lean.txt).

### CU-L029 — Shifted-reply cycles and migration failure

At S={3,4,9,16,17,18,26,28,31,37}, deficit one loses and the shifted reply graph has 3→4→3. At S={3,4,5,6,9,19,24,26,29,38}, it has 3↔5 but the proposed slide through 4 fails: the 5→4 move draws and the 4→5 move loses. On Icc 3 7, vertex 7 has only reply edge to 3. Shifted edges are legal winning replies after a first pick from (S,1), not replies from a tied initial root.

Evidence: archived Lean source; historical kernel checks. Scope: shifted graph on alternative first choices.

These graph walks are not plays; actual picks always remove counters. Full-interval acyclicity under a hypothetical root loss remains open. Tied-root maximum-companion reasoning cannot migrate unchanged.

Sources: [catchup_shifted_cycle_report_20260928_1021_et--bb668e38.md](../archive/campaigns/reports/catchup_shifted_cycle_report_20260928_1021_et--bb668e38.md), [ShiftedReplyCycle.lean.txt](../archive/catch_up/ShiftedReplyCycle.lean.txt).

### CU-L030 — Loss forces a closed shifted-reply walk

A hypothetical loss at P_N=(Icc 3 N,1), N≥7, forces a legal winning reply at every first-choice vertex and hence a nonempty closed directed walk.

Evidence: archived Lean source; historical symbolic check. Scope: conditional full-interval first-pair graph.

Closed walk existence is formalized; extracting a simple directed cycle is explained informally. It supplies no contradiction by itself.

Sources: [catchup_shifted_cycle_report_20260928_1021_et--bb668e38.md](../archive/campaigns/reports/catchup_shifted_cycle_report_20260928_1021_et--bb668e38.md), [ShiftedReplyCycle.lean.txt](../archive/catch_up/ShiftedReplyCycle.lean.txt).

### CU-L031 — Prepaid reserve preservation and initialization barrier

For distinct positive counters at an opponent-turn boundary, partition the remaining support into fixed disjoint unequal pairs P and an unpaired pool B. Let D be the sum of pair gaps, W=sum B and L≥0 the protected player's lead. Conditions D+W≤L and L+D+W≤x for every x∈P support the mate-reply argument. The weaker BudgetEnvelope on S=[3,N]\{a}, lead a−1, for N≥7 and 3≤a≤N holds iff N=7 and a=3; it asks for B⊆S and natural D with |S\B|≤2D and those two inequalities.

Evidence: paper-level reviewed preservation; archived Lean initialization classification. Scope: specified reserve invariant and initial entries.

Preservation is informal; only the initialization classification was formalized. It excludes immediate initialization of this envelope, not delayed entry or other invariants.

Sources: [catchup_turn_invariant_report_20260928_1108_et--5e291d7e.md](../archive/campaigns/reports/catchup_turn_invariant_report_20260928_1108_et--5e291d7e.md), [ARGUMENT--f4b9f23e.md](../archive/campaigns/notebooks/turn-invariant-20260928/ARGUMENT--f4b9f23e.md), [TurnReserveInitialization.lean.txt](../archive/catch_up/TurnReserveInitialization.lean.txt).

### CU-L032 — Fourth-from-top endpoint

Q_N(N−3) is nonlosing for every N≥15 without parity or smaller-instance assumptions; kernel checks at admissible N=11,12 extend the admissible endpoint statement to N≥11.

Evidence: archived Lean source; historical standard-axiom check. Scope: one unbounded lower-ray endpoint.

Finite exact-sum trees cover the three top witnesses. At m=10 one branch requires legal completed turn [2,6,15]; repeating counter 6 in a block would be invalid.

Sources: [catchup_upper_exchange_report_20260929_0034_et--2a2d854a.md](../archive/campaigns/reports/catchup_upper_exchange_report_20260929_0034_et--2a2d854a.md), [LowerRayFourthEndpoint.lean.txt](../archive/catch_up/LowerRayFourthEndpoint.lean.txt).

### CU-L033 — Common-support uniqueness shortcut has wrong deficit

Deleting two disjoint exact blocks of sum d can yield w as a winning catch on a common support at deficit d. It does not yield a winning opening at deficit zero. At ({6,7,8},3), all three catching moves win.

Evidence: reviewed paper-level diagnosis in historical report. Scope: positive-deficit common support.

Tied-root winning-opening uniqueness cannot compare these catches. The example does not carry the full dense ancestry and is not a counterexample to the original dense target.

Sources: [catchup_upper_exchange_report_20260929_0034_et--2a2d854a.md](../archive/campaigns/reports/catchup_upper_exchange_report_20260929_0034_et--2a2d854a.md).

### CU-L034 — Dominant adjacent pair changes terminal utility

An unformalized candidate for finite distinct natural counters T with every t∈T at least 2, M=sum T, natural deficit d, and a>M+d replaces {a,a+1} in T∪{a,a+1} by empty-small-support utility win/draw/loss at deficits 0/1/≥2. The modified recurrence uses ordinary small-pick maximization without pruning when T alone cannot catch. The proposed argument excludes premature use of the pair while T is nonempty.

Evidence: informal candidate and one reported bounded diagnostic. Scope: dominant-pair family under precise separation.

No formal equivalence or uniform odd-pair strategy was proved. The modified utility is not neutrality; original early-terminal pruning cannot be used on T alone.

Sources: [catchup_upper_exchange_report_20260929_0034_et--2a2d854a.md](../archive/campaigns/reports/catchup_upper_exchange_report_20260929_0034_et--2a2d854a.md), [SIDE_IDEA--a1c48e7e.md](../archive/campaigns/notebooks/upper-exchange-20260929/SIDE_IDEA--a1c48e7e.md).

### CU-L035 — Exponential explicit-certificate lower bound

For N≥16 and either protected player, every existing full atomic initial strategy DAG with terminal safe leaves has at least 2^floor((N−2)/12) listed nodes. Counting upper-half target deletions handles merger of different histories.

Evidence: current Lean library; historical proof/review and measurements newly archived. Scope: specified full DAG language, conditional on certificate existence.

Not a lower bound on arbitrary Lean proofs, symbolic strategies, or compressed certificates. The earlier sqrt(N) argument is retained as an earlier version of the mechanism.

Sources: [catchup_certificate_complexity_report_20260929_0126_et--d3ddad31.md](../archive/campaigns/reports/catchup_certificate_complexity_report_20260929_0126_et--d3ddad31.md), [HIGH_COUNTER_ARGUMENT--cedd8bbc.md](../archive/campaigns/notebooks/certificate_complexity_20260929/HIGH_COUNTER_ARGUMENT--cedd8bbc.md), [CertificateComplexityHighCounters.lean](../CatchUp/Earlier/CertificateComplexityHighCounters.lean), [CertificateComplexityGame.lean](../CatchUp/Earlier/CertificateComplexityGame.lean).

### CU-L036 — Structural certificate compression and calibration

A sound maximum-equals-deficit target permits compressed leaves; fixtures at N=3,4,7 compare the languages. A paired toy game has exponentially many synchronization subsets yet a short mate-strategy induction.

Evidence: current Lean library; historical calibration argument. Scope: specific target rule and distinct toy game.

The toy is not a pairing proof for Catch-Up. Modest fixture savings do not establish polynomial-size Catch-Up certificates.

Sources: [catchup_certificate_complexity_report_20260929_0126_et--d3ddad31.md](../archive/campaigns/reports/catchup_certificate_complexity_report_20260929_0126_et--d3ddad31.md), [ARGUMENT--abc8fd94.md](../archive/campaigns/notebooks/certificate_complexity_20260929/ARGUMENT--abc8fd94.md), [CertificateComplexityCompression.lean](../CatchUp/Earlier/CertificateComplexityCompression.lean), [CertificateComplexityFixtures.lean](../CatchUp/Earlier/CertificateComplexityFixtures.lean).

### CU-L037 — Fifth endpoint and four-tail forcing forest

For N≥23, Q_N(N−4) is nonlosing without parity or smaller-instance hypotheses. Its four upper-opening exclusions for F(m,4)=[2,m]∪[m+3,m+6] hold for m≥17, using a 35-node exact-sum forest with 14 dominating leaves.

Evidence: archived Lean source; historical standard-axiom check. Scope: one endpoint; fixed tail length four with unbounded counter sizes.

At m=16, small 11 collides with large m−5=11 in this certificate. The collision invalidates that certificate, not the game-value claim below its bound. No closure for arbitrary tail length was proved.

Sources: [catchup_uniform_descent_report_20260929_0843_et--39544321.md](../archive/campaigns/reports/catchup_uniform_descent_report_20260929_0843_et--39544321.md), [LowerRayFifthEndpoint.lean.txt](../archive/catch_up/LowerRayFifthEndpoint.lean.txt), [quad_trees--aaa1c215.json](../archive/campaigns/notebooks/uniform-descent-20260929/quad_trees--aaa1c215.json).

### CU-L038 — Uniform upper-only exact-sum descent fails

For m≥6,k≥2 on F(m,k)=[2,m]∪[m+3,m+k+2], an upper-only exact block after opening m+4 must be {m,4}. The structurally permitted next witness m+3 then needs a new complement of four, which is unavailable.

Evidence: current Lean obstruction; historical supporting argument. Scope: exact-sum certificate class with all structurally permitted witnesses.

This does not assert that m+3 actually loses. Excluding it by a new semantic lemma would add information outside the refuted certificate class.

Sources: [catchup_uniform_descent_report_20260929_0843_et--39544321.md](../archive/campaigns/reports/catchup_uniform_descent_report_20260929_0843_et--39544321.md), [INDEPENDENT_IDEA--4569e7ba.md](../archive/campaigns/notebooks/uniform-descent-20260929/INDEPENDENT_IDEA--4569e7ba.md), [UniformExactSumDescentObstruction.lean](../CatchUp/Earlier/UniformExactSumDescentObstruction.lean).

### CU-L039 — Complement packing and lower-intruder resource cost

For integer q≥3, at most floor((q−1)/2) pairwise disjoint subsets of integers≥2 each sum to q; singleton {q} plus complementary pairs attain the bound. For k≥2 and m≥2k+2, this excludes the consecutive-lower-maximum forcing scheme on F(m,k): it requires k disjoint complements of q=k+2 but only floor((k+1)/2)<k exist. A known lower-intruder repair consumes {2,4,5}, widens the gap, and exits the original family.

Evidence: informal exact arithmetic argument retained in notebook. Scope: specified forcing normal form and positive distinct integers.

The packing argument is informal, not Lean-certified here. The forcing-scheme obstruction assumes no lower witness and no upper counter in an exact block, and must handle every structurally permitted witness. It does not rule out semantic branch exclusions or other proof languages. A decreasing counter count alone supplies neither future complements nor terminal closure.

Sources: [catchup_uniform_descent_report_20260929_0843_et--39544321.md](../archive/campaigns/reports/catchup_uniform_descent_report_20260929_0843_et--39544321.md), [INDEPENDENT_IDEA--4569e7ba.md](../archive/campaigns/notebooks/uniform-descent-20260929/INDEPENDENT_IDEA--4569e7ba.md).

### CU-L040 — Geometric three-pair repair

For a≥3,b≥a+2,c≥b+2,b≥2a−1, ({a,a+1,b,b+1,c,c+1},1) draws. Without the last separation condition the three-pair state is proved nonwinning. An orphan {a,b,b+1} at deficit a+1 draws for a≥2,b≥a+2.

Evidence: current Lean library; historical research context. Scope: exactly three pairs, unbounded sizes and gaps.

The number of pairs is fixed. Among the first-pair interval states this only covers the already-known P8; arbitrary odd-pair safety remains open under the relevant distinct hypotheses.

Sources: [catchup_uniform_descent_report_20260929_0843_et--39544321.md](../archive/campaigns/reports/catchup_uniform_descent_report_20260929_0843_et--39544321.md), [AdjacentPairGeometryRepair.lean](../CatchUp/AdjacentPairGeometryRepair.lean).

### CU-L041 — Historical independent exact runs through 32

The local packed solver report records exact root and all-opening draws for N=23,24,27,28,31,32, with independent scalar table verification. Its N32 run reports 141,733,920,768 labels and 72 GiB peak allocation.

Evidence: historical exact computation, source exported previously; large tables unrecovered. Scope: six initial intervals and their openings.

Detailed run records are newly preserved separately from this source pointer. These reproduce earlier work reported by von Stengel and do not extend the known frontier.

Sources: [packed-exact-run-2026-08-07.md](../archive/campaigns/packed-exact-run-2026-08-07.md), [README.md](../computation/solvers/packed/README.md).

### CU-L042 — Monte Carlo reconnaissance at 35 and 36

Three seeds at two million simulations each for N=35 and N=36 gave empirical means near zero and changing favored openings in the historical report.

Evidence: historical heuristic output. Scope: six bounded Monte Carlo runs.

No exact game value, certificate, or stable counterexample signal follows. No rerun is made in this import.

Sources: [packed-exact-run-2026-08-07.md](../archive/campaigns/packed-exact-run-2026-08-07.md), [README.md](../computation/solvers/packed/README.md).

### CU-L043 — External N≤38 evidence and attribution

A user-supplied August 8 handoff reports von Stengel computed through N=34 in 2019 and N=38 in May 2024. For the later reported sizes N≥21, draw-capable cases have every opening drawing, and odd-total cases have a unique winning opening among 1,2,3.

Evidence: external personal communication as reported in a supplied handoff. Scope: historically reported finite cases.

The repository publicly cites the 2019 institutional N≤34 report. The N≤38 report is private-communication evidence, not a public solver certificate. Do not attribute the work to Rao; the supplied correspondence explicitly disclaims his involvement.

Sources: [catchup_final_report_20260808_2206_et--7d784e0a.md](../archive/campaigns/reports/catchup_final_report_20260808_2206_et--7d784e0a.md), [handoff-2026-08-08.md](../archive/campaigns/handoffs/handoff-2026-08-08.md).

## Corrections preserved alongside the record

CU-L010 disambiguates the August two-opening sentence: the conditional criterion and the existence of qualifying openings are different assertions. CU-L017 narrows an overstatement about cardinality cutoffs: failures at six through nine old counters do not exclude every larger fixed cutoff. CU-L033 identifies the deficit mismatch in a uniqueness argument. CU-L041 and CU-L043 correct the obsolete novelty/attribution claims. None of these editorial corrections changes a verified Lean theorem.
