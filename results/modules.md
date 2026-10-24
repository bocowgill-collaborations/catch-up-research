# Lean module guide

All 100 mathematics modules are included in the default build. Start with the [results overview](README.md); this guide covers the library by topic. A file can contain both a positive theorem and a certified failed generalization. Full hypotheses and theorem names are in [catalog.json](catalog.json) and the linked source. The [earlier-work guide](../docs/earlier-work.md) explains recovered certificate, parity and proof-size results.

## Rules, evaluation and search

| Module | What it establishes |
| --- | --- |
| [CatchUp.Reference](../CatchUp/Reference.lean) | Absolute-score rules, normalized positions, fixed-player safety semantics, and the correspondence between them. The unfinished upstream conjecture is omitted. |
| [CatchUp.Classifier](../CatchUp/Classifier.lean) | Executable fixed-player nonloss classifier, proved sound and complete against CanAvoidLoss. |
| [CatchUp.Executable](../CatchUp/Executable.lean) | Exact ternary evaluation, common-score translation, initial-root correspondence and the empty game. |
| [CatchUp.ReachableBounds](../CatchUp/ReachableBounds.lean) | A reachable interval state keeps a subset of the original counters and deficit at most N. |
| [CatchUp.ZeroDeficit](../CatchUp/ZeroDeficit.lean) | Connects normalized tied-score positions to the initial game value. |
| [CatchUp.Search](../CatchUp/Search.lean) | A counterexample search halts if and only if the universal conjecture is false; no claim that the search actually halts. |

## Opening structure and reductions

| Module | What it establishes |
| --- | --- |
| [CatchUp.WinningOpening](../CatchUp/WinningOpening.lean) | At most one opening can force a win on any finite support. This mathematical fact was reported by von Stengel in 2019; this file supplies the formal proof. |
| [CatchUp.DrawOpening](../CatchUp/DrawOpening.lean) | A nonempty root draws exactly when some opening leaves a drawn child; includes the two-opening exchange identity. |
| [CatchUp.PairDeletion](../CatchUp/PairDeletion.lean) | A sufficient lower-pair-deletion safety family implies the interval draw claim. Establishing that family remains a separate obligation. |
| [CatchUp.LowerRayAntepenultimateDescent](../CatchUp/LowerRayAntepenultimateDescent.lean) | For N≥7, a draw after opening one at N−4 prevents loss at Q_N(N−2). The specified opening hypothesis matters. |
| [CatchUp.ExactSumResiduals](../CatchUp/ExactSumResiduals.lean) | An exact-deficit block proves nonloss after checking every potentially forced larger residual opening. |
| [CatchUp.LowerRayFifthEndpoint](../CatchUp/LowerRayFifthEndpoint.lean) | For N≥23, deleting 1 and N−4 leaves a nonlosing position at deficit N−5; no parity or smaller-instance assumption. See the [proof guide](fifth-endpoint.md). |
| [CatchUp.Increasing](../CatchUp/Increasing.lean) | Restricts the protected player to increasing safe picks while retaining every opponent choice; proves exact first-pair reductions and turn-length bounds. |

## Paired positions and adaptive defenses

| Module | What it establishes |
| --- | --- |
| [CatchUp.PairClassification](../CatchUp/PairClassification.lean) | Exact two-counter classification used in the top-four endgame analysis. |
| [CatchUp.DeficitTwo](../CatchUp/DeficitTwo.lean) | Separated four-pair positions of minimum at least four are nonwinning at deficit two; reduces the first-pair safety problem to interval nonwinning. |
| [CatchUp.ThreePairClose](../CatchUp/ThreePairClose.lean) | Symbolic three-pair endgames at close deficits, with unbounded natural parameters. |
| [CatchUp.AdjacentPairGeometryRepair](../CatchUp/AdjacentPairGeometryRepair.lean) | Two adjacent pairs draw at a tied root; three-pair results require the stated separation and minimum hypotheses. Classifies both orphan-deficit signs. |
| [CatchUp.TiedFour](../CatchUp/TiedFour.lean) | Tied four-pair and deficit-one five-pair nonwinning results under explicit separation assumptions. |
| [CatchUp.CanonicalSmall](../CatchUp/CanonicalSmall.lean) | Canonical two- and three-pair endgames used by larger defenses; every parameter restriction is stated in the source. |
| [CatchUp.CanonicalFour](../CatchUp/CanonicalFour.lean) | Classifies canonical four-pair deficit-four positions, including the exceptional winning geometry (6,10,20,40). |
| [CatchUp.FivePairLeaves](../CatchUp/FivePairLeaves.lean) | Shared kernel-replayed leaves and legality lemmas for one-pair deletions from [4,15]. |
| [CatchUp.FivePair](../CatchUp/FivePair.lean) | All one-pair reserves from [4,15] are defended at deficits one and three, yielding [4,15] nonwinning at deficit two and [3,15] nonloss at deficit one. |
| [CatchUp.FiveThree](../CatchUp/FiveThree.lean) | Refutes an unrestricted five-pair deficit-three principle, while proving safe upper-move reductions. |
| [CatchUp.CanonicalFiveLeaves](../CatchUp/CanonicalFiveLeaves.lean) | Shared finite leaves supporting the canonical five-pair restrictions. |
| [CatchUp.CanonicalFive](../CatchUp/CanonicalFive.lean) | Necessary anchor conditions for a winning canonical five-pair deficit-three position; does not assert every such position is nonwinning. |
| [CatchUp.AnchorFourEndgames](../CatchUp/AnchorFourEndgames.lean) | Small endgames needed by defenses retaining the pair {4,5}. |
| [CatchUp.AnchorFour](../CatchUp/AnchorFour.lean) | Four-pair and orphan defenses with the anchor {4,5}, subject to the stated excluded counters/geometries. |
| [CatchUp.AnchorFive](../CatchUp/AnchorFive.lean) | Five-pair restrictions and lower-orphan defenses when eight is absent; not an arbitrary-pair induction. |
| [CatchUp.ReserveTriangle](../CatchUp/ReserveTriangle.lean) | A multi-turn defense beginning with pick five, covering all nine replies at the diagnosed obstruction and symbolic related families. |
| [CatchUp.FourOrphan](../CatchUp/FourOrphan.lean) | A certified failure of a proposed four-pair orphan invariant, plus a proved large-parameter defensive repair. |
| [CatchUp.NearRepair](../CatchUp/NearRepair.lean) | Adaptive repairs in the remaining finite parameter range, composed with the large-parameter theorem to retain all opponent turns. |

## Whole turns and proof-depth barriers

| Module | What it establishes |
| --- | --- |
| [CatchUp.CompletedTurn](../CatchUp/CompletedTurn.lean) | Legal completed-turn predicates and endpoint semantics; a chosen subset must meet the first-catch condition. |
| [CatchUp.WholeTurn](../CatchUp/WholeTurn.lean) | Score-sum draw leaves, balanced-turn defenses and certified failures of proposed one-turn repairs. |
| [CatchUp.TurnDepth](../CatchUp/TurnDepth.lean) | Conservation and lower bounds on reaching terminal or score-sum leaves through completed turns. These are not formal proof-size lower bounds. |
| [CatchUp.IntervalReserveDepth](../CatchUp/IntervalReserveDepth.lean) | Depth barriers at the actual interval reserve endpoints; rules out a one-turn balanced repair in the stated range, not all strategies. |

## Subset sums and dense supports

| Module | What it establishes |
| --- | --- |
| [CatchUp.ExactSumLossObstruction](../CatchUp/ExactSumLossObstruction.lean) | An exact-deficit block in a hypothetical losing position forces a winning residual opening above the block maximum. |
| [CatchUp.LowerRayFourthEndpoint](../CatchUp/LowerRayFourthEndpoint.lean) | Q_N(N−3) is nonlosing for every N≥15 and every even-triangular N≥11. Uses symbolic exact-sum branches and four small kernel checks. |
| [CatchUp.IncompleteSubsumMass](../CatchUp/IncompleteSubsumMass.lean) | For r distinct positive counters with an unattainable target within their total, proves r(r+1)+2r <= 2*sum+2. Pure arithmetic, not a game-value theorem. |
| [CatchUp.DenseBlockMass](../CatchUp/DenseBlockMass.lean) | Bounds exact-block size and the ambient interval when the residual is small; no strategic preservation is claimed. |
| [CatchUp.DenseGapMass](../CatchUp/DenseGapMass.lean) | A uniform exact-block bound for the small residual configurations handled here. |
| [CatchUp.DenseGapMassGeneral](../CatchUp/DenseGapMassGeneral.lean) | Extends the true subset-sum-gap mass bound to arbitrary residual sizes. |
| [CatchUp.DenseLossGeneral](../CatchUp/DenseLossGeneral.lean) | Dense-loss dichotomy and exact-deficit nonloss boundary cases; the density and deficit hypotheses remain explicit. |
| [CatchUp.DenseLossSubsumGap](../CatchUp/DenseLossSubsumGap.lean) | Maximal exact blocks expose an upper branch or a genuine subset-sum-gap lower branch; preservation is not automatic. |
| [CatchUp.DenseTerminalReduction](../CatchUp/DenseTerminalReduction.lean) | A specific terminal subset-sum-gap branch forces N <= 9; does not close all dense cases. |
| [CatchUp.DenseTerminalNonloss](../CatchUp/DenseTerminalNonloss.lean) | Closes the bounded terminal gap branch using eight kernel-checked small successors. |
| [CatchUp.DenseTwoResidual](../CatchUp/DenseTwoResidual.lean) | Excludes the specified nonterminal lower branch with at most two residual counters. |
| [CatchUp.DenseThreeResidual](../CatchUp/DenseThreeResidual.lean) | Closes the specified lower branch with three residual counters by classification and safe exact-block entry. |
| [CatchUp.DenseLossFrontier](../CatchUp/DenseLossFrontier.lean) | Packages a necessary frontier for a hypothetical dense loss: an upper branch or a nonterminal lower obstruction with at least four residual counters. |

## Interval cores and near-maximum defenses

| Module | What it establishes |
| --- | --- |
| [CatchUp.TwoHoleTopBoundary](../CatchUp/TwoHoleTopBoundary.lean) | Conditional reduction for a two-hole top boundary to an exceptional support and a smaller winning interval opening. |
| [CatchUp.ThreeHoleTopBoundary](../CatchUp/ThreeHoleTopBoundary.lean) | Analogous conditional three-hole reduction with counter one retained; no general closure theorem. |
| [CatchUp.PairEntranceShadow](../CatchUp/PairEntranceShadow.lean) | Matches all completed opponent turns avoiding a reserve. Equality is an exceptional case, explicitly accounted for. |
| [CatchUp.DeficitCrossing](../CatchUp/DeficitCrossing.lean) | Crossing and legal midpoint-turn lemmas relating different deficits on the same support. |
| [CatchUp.DeficitCrossingEntry](../CatchUp/DeficitCrossingEntry.lean) | Specialized entry/crossing implications used by the actual upper interval branches. |
| [CatchUp.RootUpperReentry](../CatchUp/RootUpperReentry.lean) | Excludes a losing seven-shadow in the actual parent-loss branch, retaining the reserve-taking reply. |
| [CatchUp.RootUpperEightFrontier](../CatchUp/RootUpperEightFrontier.lean) | The actual eight-opening route forces a two-anchor double-loss obstruction; does not exclude that obstruction. |
| [CatchUp.RootUpperEightCriterion](../CatchUp/RootUpperEightCriterion.lean) | An exact conditional equivalence between the reserve endpoint and the deficit-one two-anchor core, retaining the original losing shadow. |
| [CatchUp.ConsecutiveGuardDescent](../CatchUp/ConsecutiveGuardDescent.lean) | On {3,4} union [9,N] at deficit one, a winning q >= 14 needs q+4 <= N. The residual witness cannot simply be reused on the old support. |
| [CatchUp.ConsecutiveGuardBoundary](../CatchUp/ConsecutiveGuardBoundary.lean) | Strengthens that exclusion to q+6 <= N: the top six large picks are nonwinning. |
| [CatchUp.NearMaximumDefense](../CatchUp/NearMaximumDefense.lean) | A complementary-pair defense rules out loss at deficit b under a near-maximum bound and explicit minimum/pair hypotheses. |
| [CatchUp.ComplementaryPairDefense](../CatchUp/ComplementaryPairDefense.lean) | Generalizes the complementary pair to {p,b-p}; the lower bound need not itself be present. |
| [CatchUp.AlternativeSumDefense](../CatchUp/AlternativeSumDefense.lean) | Generalizes the complementary pair to any separate exact-sum block B of total b. Bounded-range nonloss and a residual-opening bound are proved. |

## Certified obstructions to proposed generalizations

| Module | What it establishes |
| --- | --- |
| [CatchUp.AdviceFeatureCollision](../CatchUp/AdviceFeatureCollision.lean) | Same pair count, total, extrema, deficit, parity and selector interval can conceal opposite outcomes. Static arithmetic summaries do not determine value. |
| [CatchUp.AlternatingTailObstruction](../CatchUp/AlternatingTailObstruction.lean) | A certified sparse obstruction to a proposed alternating-tail principle; not an initial-interval counterexample. |
| [CatchUp.DenseBlockEntryObstruction](../CatchUp/DenseBlockEntryObstruction.lean) | A dense drawn continuing state has no safe first pick inside its maximal exact block; its unique safe pick lies elsewhere. |
| [CatchUp.EqualityReserveObstruction](../CatchUp/EqualityReserveObstruction.lean) | Every first repair turn containing the reserve loses under the equality hypotheses. Nonloss is characterized by a reserve-avoiding turn instead. |
| [CatchUp.FullGapDensityFamily](../CatchUp/FullGapDensityFamily.lean) | An unbounded sparse family refutes density-free gap preservation; does not refute the version retaining density. |
| [CatchUp.FullGapDensityObstruction](../CatchUp/FullGapDensityObstruction.lean) | A concrete failure of removing density from a strategic gap-closing implication. |
| [CatchUp.GapSuccessorObstruction](../CatchUp/GapSuccessorObstruction.lean) | A dense even ancestor can have a losing proposed gap successor while the ancestor itself wins; refutes that preservation implication. |
| [CatchUp.IntervalSuccessorReplyObstruction](../CatchUp/IntervalSuccessorReplyObstruction.lean) | At an actual drawn interval endpoint, the immediate-successor reply can lose; all first choices at the endpoint are certified. |
| [CatchUp.NearDeficitGuardObstruction](../CatchUp/NearDeficitGuardObstruction.lean) | A counter one below the deficit need not protect against loss; inserting two can reverse value and invalidate a copied winning move. |
| [CatchUp.OddPairRootObstruction](../CatchUp/OddPairRootObstruction.lean) | An even-total root made of six odd-start adjacent pairs is winning. This support is not an initial interval. |
| [CatchUp.SevenPairTest](../CatchUp/SevenPairTest.lean) | Adding two pairs breaks a previously successful recursive defense; includes exact counterplay and a symbolic bad-mate family. |
| [CatchUp.TwoAnchorDoubleLossObstruction](../CatchUp/TwoAnchorDoubleLossObstruction.lean) | Sparse supports can lose at both small deficits despite two anchors. The required losing high-shadow hypothesis is absent in this example. |
| [CatchUp.UnitGuardObstruction](../CatchUp/UnitGuardObstruction.lean) | A twelve-counter support of minimum two loses at deficit one; all twelve first picks are covered. |

## Recovered earlier certificates and structural results

| Module | What it establishes |
| --- | --- |
| [CatchUp.Earlier.Parity](../CatchUp/Earlier/Parity.lean) | Odd effective total rules out a draw at normalized positions and initial roots, with the invariant transferred through picks. |
| [CatchUp.Earlier.ThreeCounterSafety](../CatchUp/Earlier/ThreeCounterSafety.lean) | An unbounded parametric three-counter nonloss theorem, under explicit order and deficit-region hypotheses. |
| [CatchUp.Earlier.CompletedTurnReflection](../CatchUp/Earlier/CompletedTurnReflection.lean) | Characterizes when a chosen completed turn is legal at the deficit reflected through its total; handles the zero/singleton boundary. |
| [CatchUp.Earlier.CertificateTests](../CatchUp/Earlier/CertificateTests.lean) | Transparent kernel-checked terminal, owner and opponent certificates, plus executable malformed-certificate and extraction regressions. |
| [CatchUp.Earlier.CertificateSoundness](../CatchUp/Earlier/CertificateSoundness.lean) | Accepted full strategy DAGs imply fixed-player CanAvoidLoss under the reference semantics. |
| [CatchUp.Earlier.CertificateChecker](../CatchUp/Earlier/CertificateChecker.lean) | Independent local/global checker for exact state labels, legal transitions, terminal safety, all opponent moves and strict progress. Soundness is proved in CertificateSoundness. |
| [CatchUp.Earlier.StrategyContract](../CatchUp/Earlier/StrategyContract.lean) | Data format for solved graphs and fixed-player strategy DAGs, with the strategy owner and player to act explicit. |
| [CatchUp.Earlier.StrategyExtraction](../CatchUp/Earlier/StrategyExtraction.lean) | Untrusted extraction keeps one owner witness and every opponent reply; its output must pass the independent checker. |
| [CatchUp.Earlier.ExactSolver](../CatchUp/Earlier/ExactSolver.lean) | Earlier memoized Lean solver and reference-comparison code. Compiling this executable does not certify its exported outcomes. |
| [CatchUp.Earlier.CertificateComplexityHighCounters](../CatchUp/Earlier/CertificateComplexityHighCounters.lean) | Every valid full initial certificate at N>=16 has at least 2^floor((N-2)/12) listed nodes. Applies to this terminal-leaf certificate language, not all proof systems. |
| [CatchUp.Earlier.CertificateComplexityGame](../CatchUp/Earlier/CertificateComplexityGame.lean) | Game-aware deletion/covering lemmas for full certificates, with actual turn identities and bounded deletion cost. |
| [CatchUp.Earlier.CertificateComplexity](../CatchUp/Earlier/CertificateComplexity.lean) | Defines full-certificate existence, attained minimum node count, deletion-closure counting and target-cover bounds. |
| [CatchUp.Earlier.CertificateComplexityCompression](../CatchUp/Earlier/CertificateComplexityCompression.lean) | A proved maximum-equals-deficit target enables sound partial certificates. Structural leaves change the certificate language. |
| [CatchUp.Earlier.DeficitWinningBound](../CatchUp/Earlier/DeficitWinningBound.lean) | An available exact deficit forces a residual winning-opening restriction; an available maximum equal to the deficit guarantees nonloss. |
| [CatchUp.Earlier.LowerRaySuccessor](../CatchUp/Earlier/LowerRaySuccessor.lean) | Successor-child relations for the lower pair-deletion ray; isolates the remaining nonwinning obligations. |
| [CatchUp.Earlier.PartialCertificateSoundness](../CatchUp/Earlier/PartialCertificateSoundness.lean) | Accepted partial strategy DAGs imply nonloss when the recognized target leaves have an independently proved safety theorem. |
| [CatchUp.Earlier.PartialCertificateChecker](../CatchUp/Earlier/PartialCertificateChecker.lean) | Extends the full checker with explicit target leaves. It does not assume that an arbitrary target is safe. |
| [CatchUp.Earlier.CertificateComplexityFixtures](../CatchUp/Earlier/CertificateComplexityFixtures.lean) | Literal full and compressed certificates for both players at N=3,4,7, with kernel-checked node counts. No certificate-size minimality is asserted. |
| [CatchUp.Earlier.UniformExactSumDescentObstruction](../CatchUp/Earlier/UniformExactSumDescentObstruction.lean) | An explicit obstruction to two successive upper-only exact-block descent steps; rejects that uniform route, not C. |
| [CatchUp.Earlier.AdditiveTripleReduction](../CatchUp/Earlier/AdditiveTripleReduction.lean) | Reduces pair-deletion safety to additive-triple residual obligations, with the doubling case handled separately. |
| [CatchUp.Earlier.LowerRayExactDeficit](../CatchUp/Earlier/LowerRayExactDeficit.lean) | Exact-deficit endpoint identities and draw-opening reductions for the lower ray. |
| [CatchUp.Earlier.ReplyDigraphReduction](../CatchUp/Earlier/ReplyDigraphReduction.lean) | Represents first-two-pick outcomes as a ranked reply graph and proves conditional draw reductions. A ranking still needs to be supplied. |
| [CatchUp.Earlier.TopFourClassification](../CatchUp/Earlier/TopFourClassification.lean) | Symbolic classification for subsets of the four added counters within the stated start/deficit bounds, reusing the current pair API and retaining an import-compatible renamed duplicate lemma. |
| [CatchUp.Earlier.ScoreDebtTerminalRepair](../CatchUp/Earlier/ScoreDebtTerminalRepair.lean) | A causal terminal repayment gadget for an unbounded three-counter family; explicit hypotheses retain actual versus shadow roles. |
| [CatchUp.Earlier.CompletedMargin](../CatchUp/Earlier/CompletedMargin.lean) | Tracks signed completed margins and effective parity along legal traces, preserving the winner when the terminal trailing player receives leftovers. |
| [CatchUp.Earlier.SimulationSoundness](../CatchUp/Earlier/SimulationSoundness.lean) | Solver-independent transfer theorems for exact and ghost strategy simulations. A relation must satisfy the stated adversarial simulation obligations. |
