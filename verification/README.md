# Verification and provenance

The [August–September source manifest](legacy-sources.json) and [finding ledger](../results/legacy-findings.md) describe an additional historical import outside both Lean builds. Run `python3 scripts/check_legacy_archive.py` to check hashes, coverage, finding references, notebook locators, data parseability and corruption/privacy controls. This check is included in `check_collection.py`. With the original local Git database available, `python3 scripts/check_legacy_archive.py --source-repository PATH` additionally rechecks every original blob and the complete inspected-tree inventory. It executes no historical probe or CHECK instruction.

The [import receipt](legacy-import.json) records the checks actually run, log fingerprints, unchanged proof-source scope, editorial discrepancies and deferred artifacts. Its source manifest and finding-ledger hashes are checked along with the retained logs.

There are two independent, pinned Lake packages. Their `CatchUp` namespaces intentionally contain the same game interface compiled with different Lean versions; build them separately. The cryptid package also has separate audit entry points for the baseline and the candidate components: those developments reused some declaration names and must not be imported into a single Lean environment.

| Package | Lean | Mathlib commit |
| --- | --- | --- |
| Repository root: mathematics | 4.27.0 | `a3a10db0e9d66acbebf76c5e6a135066525ac900` |
| `cryptid/`: full verified machine | 4.35.0-rc4 | `1f414401f69059aa7eead47b53ee40bd38455eeb` |

## Reproduce

With elan, Python 3, Git and network access available:

```sh
lake exe cache get
lake build
python3 scripts/check_axioms.py
python3 scripts/verify_export.py
python3 computation/check_semantics.py
python3 scripts/check_collection.py
lake env lean --run computation/CheckEarlier.lean
cd cryptid
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

The source snapshots and full manifests are included; no private repository is a dependency. The library includes large finite certificates, so a clean build can require substantial memory. The baseline machine is a generated finite transition function, not a 388-million-row text file.

`check_axioms.py` checks both the named headline endpoints in `AxiomAudit.lean` and all public Catch-Up theorems in the imported environment via `AuditAll.lean`. In the cryptid package it repeats these checks for `ComponentAxiomAudit.lean` and `ComponentAuditAll.lean` in a separate environment. The only allowed axioms are `propext`, `Classical.choice` and `Quot.sound`. The full audit includes compiler-generated theorem declarations; its count is not a count of new mathematical results. A deliberately bad `sorryAx` report must be rejected. Kernel checking is authoritative; an external solver and Python tests are not proof premises. The scripts impose explicit subprocess deadlines and fail on unfinished runs.

`check_sources.py` reuses the existing research fidelity check. It compares the actual game declarations with the frozen literal reference and checks a deliberate equality-rule mutation is rejected. `verify_export.py` also verifies copied source hashes and local documentation links. The frozen `.lean.txt` inputs in `upstream/` include the unfinished conjecture for source comparison only; they are never imported into either verified build.

## Evidence and scope

- [pins.json](pins.json) records source commits, reference blobs and toolchains.
- [source-manifest.json](source-manifest.json) records the unchanged exported proof sources and required machine-table data by SHA-256 and origin. A local development commit is not necessarily an upstream public commit; the files themselves are vendored here.
- [publication.json](publication.json) records checks actually run for this initial export. Fresh builds use the pinned external dependency caches but rebuild the local proof sources; they do not rebuild all of Mathlib.
- [benchmarks.json](benchmarks.json) retains selected earlier proof-checking and certificate-size measurements, with their scope. These are earlier runs, not fresh publication timings. Search cost and kernel checking cost are different.
- The GitHub workflow builds each package separately and retains its own receipts. A local successful run does not imply the hosted workflow has already completed.

An initial public release omits private campaign logs, account usage information, local paths, cache files and unfinished prototype code. It includes the verified mathematics, the complete verified machine, and the checked dependency closure of the smaller candidate’s local component contracts. The candidate’s missing global proof is documented explicitly. Further verified results can be added with matching provenance and checks.

## Collection expansion

The [collection audit](collection.json) records recovery of 26 earlier modules into the mathematics build, bringing the catalog to 96 modules. The original 70 sources are unchanged. [earlier-sources.json](earlier-sources.json) and original input files document the mechanical port; `check_collection.py` reconstructs those transformations and checks the full module catalog. The [historical archive](../archive/) is explicitly outside the verified build. Its source-only entries and native/generated metadata are not being presented as kernel-certified results.

The later [research-note manifest](research-collection.json) records 90 historical reports and 31 retained observation files, their original/exported hashes and the limited text adaptations. Its 94-path report inventory also identifies omitted superseded drafts and incomplete scratchwork. `check_research_archive.py`, also called by `check_collection.py`, checks coverage, hashes, parseability and a corruption control without executing a mathematical search. This validates the exported records; it does not prove their numerical outcomes. No Lean source or machine definition changed in this documentation/data expansion.
