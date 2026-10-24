# Sources, credits and AI assistance

Catch-Up was introduced by Isaksen, Ismail, Brams and Nealen (2015). See the [original code](https://github.com/aisaksen/catch-up). The literal formal target comes from [Google DeepMind's FormalConjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Paper/CatchUpConjecture.lean).

This repository collects research from Bo Cowgill's Catch-Up campaign and related local work. It is a downstream research collection, not an official Google DeepMind repository. Existing reference definitions, strategy semantics and earlier reductions are preserved rather than claimed as newly invented here.

The machine uses [Google DeepMind's Cryptids](https://github.com/google-deepmind/cryptids), the verified Chess interpreter/compiler development and Mathlib. Original source copyright notices are retained. The [source manifest](verification/source-manifest.json) identifies copied files, their origins and hashes; [pins](verification/pins.json) record the precise source snapshots. Some development snapshots were local: they are vendored here so public reproducibility does not rely on those commits being available upstream.

AI systems, including Codex and collaborating proof/search agents, assisted with experiments, Lean proofs, verification and documentation. Kernel checking establishes the included Lean claims subject to the documented standard axioms. It does not validate an unproved explanation or an unaudited external report. Earlier campaign review and fresh publication checks are distinguished in [verification](verification/).

Sources are distributed under the [Apache 2.0 license](LICENSE), retaining existing notices. Dependency licenses remain with their respective projects. No priority or exhaustive-coverage claim is made.

The August–September archival import used Codex to compare local Git versions, prepare public copies, organize a finding ledger and check provenance. Historical reviewer comments remain historical assessments. This import adds no new proof verification or large computation; its [manifest](verification/legacy-sources.json) distinguishes original bytes, public adaptations and missing artifacts. Raw private correspondence and third-party PDFs are not included.

The later [fifth-endpoint port](verification/fifth-endpoint.md) uses Codex to adapt
the archived symbolic proof and extract its reusable exact-sum interface. It is
a source-preserving verification contribution, not a claim of discovering the
endpoint anew. Only the named port receives its fresh build and axiom assurance.

Bernhard von Stengel's [2019 LSE abstract](https://www.lse.ac.uk/Mathematics/assets/documents/Events-Archive/CGO-PhD/PhD-Seminar-on-Combinatorics-2019-update.pdf#page=5) reports computations through N=34 and uniqueness of a winning opening. These predate the linked 2026 solver projects. The corresponding Lean uniqueness theorem is a formalization of an already reported fact, not a claim of discovering it here. See the [reading guide](docs/sources.md) for the distinction between historical reports, reproduced computations and kernel-checked claims.
