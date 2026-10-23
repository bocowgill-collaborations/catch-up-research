# Collection coverage and remaining gaps

Audit date: 23 October 2026. This page records what was inspected; it does not assert that all research on Catch-Up has been found.

| Area | Coverage in this collection | Remaining gap |
| --- | --- | --- |
| Local mathematics | The original 70 modules are preserved, and 26 earlier modules are recovered into the pinned build. All 96 have topic summaries in the [module guide](../results/modules.md). Fourteen historical branches were inventoried, covering 144 module paths. | The [archive](../archive/) retains 56 more small source files outside the verified build. Generated/native-only historical range claims require a separate trust audit. |
| Rules and examples | [Worked introduction](game.md), [glossary](glossary.md), [arithmetic explanations](mathematics.md), reference correspondence and small independent checks. | Informal arithmetic explanations on the new guide page are not additional Lean declarations. |
| Structural and arithmetic results | Opening uniqueness, draw-opening and pair-deletion reductions, pair/orphan defenses, dense-loss/subset-sum results, boundary exclusions and depth barriers are indexed. | The uniform strategic closure needed for C remains open. |
| Failed approaches | [Failure guide](../results/failed-ideas.md), checked obstruction modules and three retained serialized search witnesses. | Old heuristic runs and superseded scratchwork are not promoted into results. |
| Original and external work | Original paper/code, FormalConjectures statement/discussions, the 2019 institutional report through N=34, and two public solver projects. | The 2019 source/certificates were not located; external large runs have not been independently replayed or Lean-certified here. |
| Machines | Complete verified 388,819,712-state baseline, plus the smaller candidate's checked allocation, initialization and component contracts; all required source/data dependencies are included. | Candidate inherited-core preservation and full halting equivalence remain open. Superseded experiments outside the preserved dependency closure are omitted. |
| Reproduction | Two pinned Lean packages, source hashes, retained successful receipts, a small bounded Python explorer and comparison checks. | Faster/smaller proof checking and large-instance certificate compression are separate work. |

The initial public snapshot's [hosted verification run](https://github.com/bocowgill-collaborations/catch-up-research/actions/runs/39984904177) completed successfully for both pinned packages. This records that particular run, not a guarantee about future commits. The original 70 proof-source hashes are unchanged. Recovered-source hashes and the new replay checks are recorded separately in the [collection receipt](../verification/collection.json).

Please suggest missing sources through an issue or contribution. An especially useful addition would be von Stengel's original implementation or a reproducible archive behind the 2019 N=34 report. Do not infer a mathematical result from an uncompleted run or from the “closed” status of a GitHub issue.
