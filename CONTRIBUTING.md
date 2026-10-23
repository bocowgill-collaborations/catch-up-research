# Contributing

Start with the [results guide](results/) and [open questions](results/open-questions.md). Small, reproducible contributions are welcome: a theorem, checked finite result, failed proof idea with a diagnostic example, or a clearer explanation.

For a mathematical claim, state the exact remaining counters, score deficit or initial interval, whose perspective is used, and every hypothesis. Cover all opponent replies. Distinguish a strategy, one play sequence, and the optimal game value. A draw requires two nonlosing guarantees.

Keep proved statements, experiments and conjectures separate. Preserve the pinned toolchains. Include commands, resource limits and completed cases for computations; a timeout is not a draw. External solver output needs a checked bridge before it becomes a formal theorem. Final Lean results must avoid proof placeholders, custom outcome axioms, native-only proof shortcuts and dependence on the unfinished upstream conjecture.

Credit sources and collaborators, identify AI assistance, and explain what was independently checked. Please open an issue to coordinate substantial changes to the definitions or compiler.

For a source or result entry, include its title/authors, stable URL or commit, date, exact claim, rules and evidence level. Check for earlier reports before claiming novelty. Add a new mathematics module to [the catalog](results/catalog.json) and [topic guide](results/modules.md), and run `python3 scripts/check_collection.py`. The [coverage audit](docs/coverage.md) identifies the largest current collection gaps.
