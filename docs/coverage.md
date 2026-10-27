# Collection coverage and remaining gaps

Audit date: 23 October 2026; updated 27 October for the atlas and controller ports. This page
records what was inspected, not that all Catch-Up research has been found.

The [first-pair atlas](../results/first-pair-atlas.md) now ports four archived
modules with 67 public theorem declarations. Its
[verification record](../verification/atlas-ports.md) preserves the original
archives and distinguishes proof checking from historical evidence. There are
now 110 maintained mathematics modules, including the five
[formal controller and repair ports](../results/two-buffer-controller.md) with
34 public theorem declarations. The [research handoff](research-handoff.md)
records current proof gaps and the next dependency-ordered verification batches.

A later local-cache search recovered one conditional maximum-companion
implementation, [CU-R001](../results/reply-maximum-companion.md), related to
CU-L011. All ten original compiled declarations were freshly kernel-replayed;
readable source with two public theorems was reconstructed and signature-compared.
Together with the separately ported endpoints, that recovery brought the catalog to 101 modules.
The differently named August scratch
source, other missing proof/audit artifacts and large tables remain unrecovered.
See the [recovery record](../verification/reply-maximum-companion.md) for search
scope and limitations; the original missing-reference ledger remains historical.

The [August–September expansion](../archive/campaigns/) compares 290 path/blob versions across 55 relevant commits and 15 local refs, including the original game file before its move from GameTheory to Paper. It adds 183 historical records/source versions, three supplied research handoffs and one detailed packed-solver run record. A [43-entry finding ledger](../results/legacy-findings.md) and 263 notebook locators expose the claims, failures and gaps. Twenty-five temporary artifact references were absent at their recorded locations: 23 from the final reports and the N23/N24 tables from the August 7 run record; reported hashes are retained where available. No Lean source, toolchain, or large numerical result was changed or newly verified by this expansion. The [PR review](../verification/pr1-review.md) records hypothesis clarifications, source reconstruction and bounded witness replays.

| Area | Coverage in this collection | Remaining gap |
| --- | --- | --- |
| Local mathematics | The original 70 modules, 26 earlier recovered modules, four endpoint/interface modules, CU-R001, four atlas modules and five controller/repair modules give 110 in the [module guide](../results/modules.md). Fourteen historical branches were inventoried, covering 144 module paths. | All 56 original [archive](../archive/) snapshots remain outside the build, including inputs of twelve same-named maintained ports. Generated/native-only range claims and other unported declarations need separate audits. |
| Rules and examples | [Worked introduction](game.md), [glossary](glossary.md), [arithmetic explanations](mathematics.md), reference correspondence and small independent checks. | Informal arithmetic explanations on the new guide page are not additional Lean declarations. |
| Structural and arithmetic results | Opening uniqueness, draw-opening and pair-deletion reductions, pair/orphan defenses, dense-loss/subset-sum results, boundary exclusions and depth barriers are indexed. | The uniform strategic closure needed for C remains open. |
| Failed approaches and experiments | Expanded [failure guide](../results/failed-ideas.md), [experimental findings](../results/experimental-findings.md), 90 indexed [historical research notes](../archive/research-notes/), 31 retained [observation files](../computation/observations/) and checked obstruction modules. | Historical numerical outputs are not newly replayed or proof certificates. Old next steps, novelty phrases and checking paths are not adopted as current claims. |
| Open routes | A [current route guide](../results/research-routes.md) relates pair deletion, dense subset-sum methods, exact interval cores, proof compression and machine integration, retaining their strategic hypotheses. | No uniform adversarial closure or initial-interval counterexample has been proved. |
| Original and external work | Original paper/code, FormalConjectures statement/discussions, the 2019 institutional report through N=34, and two public solver projects. | The 2019 source/certificates were not located; external large runs have not been independently replayed or Lean-certified here. |
| Machines | Complete verified 388,819,712-state baseline, plus the smaller candidate's checked allocation, initialization and component contracts; all required source/data dependencies are included. Historical design and proof-compression reports are in the notebook. | Candidate inherited-core preservation and full halting equivalence remain open. Earlier experiment code outside the preserved dependency closure is not part of the verified build. |
| Reproduction | Two pinned Lean packages, source hashes, retained successful receipts, a small bounded Python explorer, the recovered [packed C++ solver](../computation/solvers/packed/), [pair/orphan bundles](../computation/experiments/), [mutation/SMT/shrinking bundles](../computation/experiments/campaign/) and the [87-node two-buffer policy replay](../computation/experiments/earlier-campaign/two-buffer/) with frozen inputs. | Separate interval/reflection/density replay routes and the full near-repair forest extractor remain outside these bundles. Large exact tables were not located or rerun. Faster proof checking and large-instance certificate compression remain separate work. |

The initial public snapshot's [hosted verification run](https://github.com/bocowgill-collaborations/catch-up-research/actions/runs/39984904177) completed successfully for both pinned packages. This records that particular run, not a guarantee about future commits. The original 70 proof-source hashes are unchanged. Recovered-source hashes and the new replay checks are recorded separately in the [collection receipt](../verification/collection.json).

Please suggest missing sources through an issue or contribution. An especially useful addition would be von Stengel's original implementation or a reproducible archive behind the 2019 N=34 report. Do not infer a mathematical result from an uncompleted run or from the “closed” status of a GitHub issue.

The research-note expansion inventories 94 local report paths across the mathematical and interpreter work. Selected reports and data have original/exported hashes in [research-collection.json](../verification/research-collection.json). It preserves existing findings rather than launching new searches. Historical notebook commands still refer to their original layout; use the new [portable reproduction commands](../computation/experiments/) for the selected executable bundles. Their source hashes, adaptations and remaining gaps are in [solver-sources.json](../verification/solver-sources.json). Only small calibration cases were run for this addition. The verified source library remains unchanged.

The [campaign manifest](../verification/campaign-sources.json) separately inventories source/data paths in the earlier search directory, both SMT directories and the adaptive-mutation directory. It includes frozen unprocessed suffixes, every selected input list, exact SMT reconstruction recipes and literal audit dependencies. Larger generated SMT text is represented by fingerprints and a checked generator rather than duplicated large files. The [campaign guide](../computation/experiments/campaign/) explains historical coverage and incompleteness.
