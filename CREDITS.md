# Sources, credits and AI assistance

Catch-Up was introduced by Isaksen, Ismail, Brams and Nealen (2015). See the [original code](https://github.com/aisaksen/catch-up). The literal formal target comes from [Google DeepMind's FormalConjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Paper/CatchUpConjecture.lean).

This repository collects research from Bo Cowgill's Catch-Up campaign and related local work. It is a downstream research collection, not an official Google DeepMind repository. Existing reference definitions, strategy semantics and earlier reductions are preserved rather than claimed as newly invented here.

The machine uses [Google DeepMind's Cryptids](https://github.com/google-deepmind/cryptids), the verified Chess interpreter/compiler development and Mathlib. Original source copyright notices are retained. The [source manifest](verification/source-manifest.json) identifies copied files, their origins and hashes; [pins](verification/pins.json) record the precise source snapshots. Some development snapshots were local: they are vendored here so public reproducibility does not rely on those commits being available upstream.

AI systems, including Codex and collaborating proof/search agents, assisted with experiments, Lean proofs, verification and documentation. Kernel checking establishes the included Lean claims subject to the documented standard axioms. It does not validate an unproved explanation or an unaudited external report. Earlier campaign review and fresh publication checks are distinguished in [verification](verification/).

Sources are distributed under the [Apache 2.0 license](LICENSE), retaining existing notices. Dependency licenses remain with their respective projects. No priority or exhaustive-coverage claim is made.
