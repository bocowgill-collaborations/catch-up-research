> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Retired finite-reduction route

An initial `table_cells` proof used `decide +kernel +revert` across all
7,750 generated cells. The strict replay exhausted the existing 8,192-MiB
Lean allocator budget after 20.101 seconds and exited -6. The limit was not
increased. Local initialization rewriting also required isolating the fuel
argument to avoid changing dependent machine-state indices.

The final generated-table theorem uses generic finite-list lookup and only
splits the two scanned bits. It proves every row at once without evaluating
the whole transition generator exhaustively. The final Prototype replay
passes. This is a proof-compression change, not a change in machine behavior.

The exported numeric table is independently reconstructed and simulated in
Python. Its bytes are diagnostics, not kernel proof premises. We do not claim
a separate Lean certificate equating a numeral-only exported table with M.
The authoritative finite transition definition and generated-row equality
are compiled and axiom audited.
