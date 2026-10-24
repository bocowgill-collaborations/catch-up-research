# Recovered earlier work

The [August–September campaign archive](../archive/campaigns/) now supplies the previously missing reports, supporting reviews, probes, observations and earlier source versions. The [finding ledger](../results/legacy-findings.md) records exact claims and their present assurance. This archival expansion is separate from the 26 compiled ports described below.

The initial public package contained the current 70-module mathematics snapshot. A further branch audit found 144 historical Catch-Up module paths in the earlier local research repository. The collection now recovers **26 additional modules** into the default Lean build and preserves **56 other small source files** in a clearly separate [historical archive](../archive/).

The recovered files are under [CatchUp/Earlier](../CatchUp/Earlier/). They use the same pinned Lean 4.27.0 and Mathlib revision as the main mathematics library. The port changes module references, removes repository-specific indexing attributes, and renames one duplicated pair theorem; mathematical statements and proof bodies are retained. The original source inputs are also retained as data and the collection checker reconstructs each mechanical adaptation. Original hashes, paths, the source commit and transformations are recorded in [earlier-sources.json](../verification/earlier-sources.json). The original 70 proof files are unchanged.

## Results worth knowing about

| Result | Why it matters | Source |
| --- | --- | --- |
| Parity under play | Odd deficit-plus-remaining total rules out a draw, with the invariant transferred through picks and to initial roots. | [Parity](../CatchUp/Earlier/Parity.lean) |
| Completed-turn reflection | Characterizes whether a turn can also be played at the deficit reflected through the chosen total; treats the singleton boundary explicitly. | [CompletedTurnReflection](../CatchUp/Earlier/CompletedTurnReflection.lean) |
| Three-counter safety | A symbolic family handles all ordered natural parameters satisfying the stated region inequalities. | [ThreeCounterSafety](../CatchUp/Earlier/ThreeCounterSafety.lean) |
| Certificate soundness | The independent full checker implies CanAvoidLoss. Partial certificates also have a soundness theorem when their targets are proved safe. | [CertificateSoundness](../CatchUp/Earlier/CertificateSoundness.lean), [PartialCertificateSoundness](../CatchUp/Earlier/PartialCertificateSoundness.lean) |
| Full-certificate size bound | Every valid full initial certificate at N≥16 needs at least `2^floor((N-2)/12)` listed nodes. The certificate language and existence hypothesis are essential. | [CertificateComplexityHighCounters](../CatchUp/Earlier/CertificateComplexityHighCounters.lean), [proof-size guide](proof-size.md) |
| A structural compression rule | An available maximum equal to the protected acting player's deficit is a sound target leaf. Literal examples compare full and compressed node counts at N=3,4,7. | [CertificateComplexityCompression](../CatchUp/Earlier/CertificateComplexityCompression.lean), [Fixtures](../CatchUp/Earlier/CertificateComplexityFixtures.lean) |
| Earlier opening reductions | Lower-ray, ranked-reply and additive-triple reductions isolate sufficient conditions. They leave explicit strategic hypotheses. | [LowerRaySuccessor](../CatchUp/Earlier/LowerRaySuccessor.lean), [ReplyDigraphReduction](../CatchUp/Earlier/ReplyDigraphReduction.lean), [AdditiveTripleReduction](../CatchUp/Earlier/AdditiveTripleReduction.lean) |
| Simulation and debt repairs | General simulation soundness and a causal terminal repayment family formalize part of the older transfer effort. They do not instantiate a uniform N→N+4 theorem. | [SimulationSoundness](../CatchUp/Earlier/SimulationSoundness.lean), [ScoreDebtTerminalRepair](../CatchUp/Earlier/ScoreDebtTerminalRepair.lean) |

## Historical sources and evidence boundaries

The [archive inventory](../archive/inventory.json) records all 144 inspected module paths, including files already represented by the current API, recovered ports, source-only attempts and omitted large/generated or native-only artifacts. The raw `.lean.txt` files are reading material, not part of the verified build. Their original imports may need adaptation and their dependencies are not promised as a standalone build.

Older sources with names suggesting certification through N=28 include `native_decide`-based finite checks. Those are not accepted here as kernel-replayed finite outcomes. The large generated payloads are not silently imported into the proof library; they need a separate replay/trust audit. Small transparent full and compressed certificates in the recovered fixtures are checked in the kernel.

Four-counter transfer ledgers, new-opening repair phases, shifted-reply cycles and dense-hole reductions remain useful historical ideas to inspect in the archive. An abstract simulation theorem only transfers safety after its relation and every adversarial step obligation have been supplied. No such historical file is being presented as a solution to C.
