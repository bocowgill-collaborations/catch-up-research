> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Shared head restoration at the two interpreter loads

The complete binary blank-tape machine has **388,819,712 states**, saving
**137,500** against the preserved 388,957,212-state two-site decoder machine.
Lean proves both statements:

```lean
ConjectureMachines.Halts CatchUp.Machine.RestoreShare.M ↔
  ¬ CatchUp.Search.Conjecture

ConjectureMachines.Halts CatchUp.Machine.RestoreShare.M ↔
  ConjectureMachines.Halts CatchUp.Machine.ReadShare.M
```

The target includes `N = 0` and retains the reference outcome semantics.
The universal Catch-Up conjecture remains unresolved. This is a verified
compiler optimization; it establishes no new game outcome or counterexample.
All preceding formal sources, compiled modules and retained evidence remain
available and are checked against their previous snapshots.

## What is shared

The two actual interpreter loads remain primitive PCs 285 and 302, reader
indices 54 and 63. Their scratch register is dead on entry because each load
overwrites it for every glyph and old store. As in the preceding construction,
the two callers put tags 0 and 1 in that existing five-valued register and use
one eleven-bit reader tree. No tape cell, tape header, alphabet symbol or
register value is added.

Previously, the tag dispatch selected one of two identical eleven-left-move
restoration chains, followed by its original load payload. The new graph first
restores the head using a common chain for each decoded glyph. Only then does
it inspect the tag and select either original bare payload. Moves preserve
the tag, and the original load overwrites it after dispatch. The construction
retains every old payload, including the unused original family, and charges
both tag loads and all 1,250 dispatch nodes.

`prepared_leaf` in `Proof.lean` reuses the existing `moveLayers` proof to establish
the shared restoration. `source_stepAux` in `Simulation.lean` proves exact final
configuration equality for every source label, old store and arbitrary binary
tape. Ordinary readers, both shared callers, plain instructions, moves and
writers are included. `step_eq` identifies the complete TM1 transition
functions, and the existing graph, binary lowering, initialization and
finite-index transport theorems preserve halting in both directions. The
unchanged literal Catch-Up program and verified source search supply the
end-to-end equivalence. No assumption about whether the conjecture is true
enters this proof.

## Full state accounting

Both former restoration families had 1,250 glyphs and eleven move nodes per
glyph. Sharing them removes exactly **13,750 graph nodes**. Each graph node
still pays for all five store descriptors and both physical binary phases:
`13,750 * 5 * 2 = 137,500` states saved. Return storage is therefore fully
charged even though no new store value is needed.

| Component | Complete count |
| --- | ---: |
| Existing base | 8,354 nodes |
| All original payloads | 2,167,500 nodes |
| Return dispatch | 1,250 nodes |
| Movement/restoration, `11 * (1733*1250 + 270 + 1188)` | 23,844,788 nodes |
| 1,733 reader trees | 10,642,353 nodes |
| Writer suffix graph | 2,210,760 nodes |
| Two caller tag loads | 2 nodes |
| **Total graph** | **38,875,007 nodes** |
| Post controls, including start and halted/default stores | 194,375,041 states |
| Binary body, including return controls | 388,750,082 states |
| Full blank-tape initializer | 69,630 states |
| **Complete machine** | **388,819,712 states** |

`node_count`, `post_count`, `body_states`, `generated_states` and `states_saved`
are kernel-checked counts. The initializer writes the same complete 34,815-bit
program/root/table stream as before. `initializes` proves its actual
69,630-step run from the all-zero two-way tape and state zero, with the head
restored at body entry. No program or continuation data are preloaded for
free. The transition function is total over the finite control and binary
symbols, with an optional instruction for halting; the entire enormous table
is specified by this generator rather than serialized. Counts include all
nominal states, including unreachable ones. No minimality claim is made.

## Reproduction and trust boundary

From the workspace root:

```sh
python3 -B research/catchup-reuse/restoration/verify_restore.py --full
```

The runner uses eight strict Lean commands: four new formal modules, the
axiom audit, the formal wrong-tag control, exhaustive reader diagnostics and
physical fixture export. It then independently reconstructs and replays the
physical fixtures in Python. Running without `--full` checks retained
receipts, hashes and independent replay. Output is restricted to this package.
`benchmark.checked.json` contains the executed receipts, source and artifact
hashes, resource measurements and complete state accounting.

This reuses the isolated package's Lean 4.35.0-rc4, compiler commit
`c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`, Mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`, and Chess source content at
`8fed07fa2981ecd96141303b0d8982116106f6eb`. The runner checks actual compiler
version, pinned Git blobs and source/cache hashes. The original package stays
on Lean 4.27.0 / Mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900`.
Existing backend/Mathlib compiled dependencies use ordinary Lean imports;
the full imported dependency closure is not freshly rebuilt. No dependency
upgrade is performed.

Twenty-four new requested axiom endpoints and 27 baseline endpoints are
checked. Only `propext`, `Classical.choice`, `Quot.sound`, or fewer are
allowed. There is no `sorryAx`, custom result axiom, native-decider premise,
unfinished conjecture dependency or external solver assumption. The count
and headline preservation statements are Lean proofs; native diagnostics
below are separate regression evidence.

## Physical diagnostics

The reader diagnostic exhausts all 2,048 eleven-bit words, all five old
stores, both real sites and two live neighboring-cell patterns: **40,960
cases**. This includes words outside the 1,250-symbol canonical encoder image.
Every case checks:

1. At physical step 11, both callers enter the same restoration node for the
   decoded glyph, with the return tag intact and head displacement 11.
2. At step 22, the head has returned to zero and reaches the dispatch node.
3. At step 24, the original expected source continuation and loaded store
   are reached; checked tape cells from -2 through 13 are unchanged.

The general Lean theorem handles arbitrary tape; these finite tests inspect
the physical implementation and are not proof premises.

Five actual initialized binary-program traces are independently replayed from
blank tape in Python. Their inputs are independently reconstructed using the
preserved constructor-table and stack codec. Each complete paid initializer
is checked at its handoff.

| Source fixture | Physical transitions | Observation |
| --- | ---: | --- |
| Zero | 19,944 | Halt |
| Successor on `[3]` | 38,370 | Halt |
| Zero branch on `[0,6]` | 188,850 | Halt |
| Positive branch on `[2,6]` | 228,984 | Halt |
| `fix succ` on `[]` | 200,000 | Explicit bound reached |

The loop observation is not a nonhalting proof. These trace lengths agree
with the preserved baseline. Across visited-state exports, 542,468 transition
cells are replayed, with overlaps retained; this is not a full-table dump.
Three corrupted controls are rejected: a changed
initializer write, a missing visited row, and a wrong caller-1 return tag in
a branch fixture that visits both callers. The auxiliary `tag_required`
theorem also proves that the two return tags yield different source
destinations for every tape/store. This is a compiler correctness obligation,
not a Catch-Up counterexample or a state lower bound.

## Cost, review and remaining work

The benchmark records every new supporting theorem, auxiliary checker and
compiled module, alongside the reused semantic/source modules, the six
preceding sharing modules and the 80-module backend source closure. It
distinguishes checking cost from interactive proof development and prior
dependency builds. A small final theorem invocation is not the whole proof.
No certificate-size or proof-size lower bound is asserted.

All eight strict Lean commands passed in **139.601 seconds** on macOS 26.6.2
arm64 with 16 logical CPUs. Maximum recorded individual-child high-water RSS
is **7,228,817,408 bytes**. The four new formal modules contain **21,679 source
bytes and 33 theorems**, with **955,248 compiled bytes**. The six auxiliary
Lean/Python sources add 19,175 bytes, including the separate wrong-tag
theorem. The fixture export occupies 12,014,826 bytes. Reused support remains
separately recorded rather than included in those new-source figures.

Each Lean child has a 120-second wall limit, an 8,192-MiB Lean allocator
budget and one-MiB output limit, except 16 MiB for fixture export. The allocator
budget is not an OS RSS cap. No unbounded game search is launched.
Fresh-context independent review accepted the result in `REVIEW.md`. It
freshly replayed all four new modules and 24 audits, checked snapshot pins,
and independently replayed the physical fixtures. It inspected the retained
native reader result rather than rerunning that enumeration. Lean's kernel
remains the formal verification authority within the stated import boundary.

The frozen benchmark SHA256 is
`04b6c22a2864337fa65b03db95bc5189301c08d713171844fb456f81dbc9aca4`.

The single next optimization is to identify another compatible group of
actual reader sites whose scratch stores are dead and whose restoration
chains agree, then apply this proved sharing contract with full dispatch and
return-storage accounting. This reduces the verified cryptid; deciding the
Catch-Up game remains a separate mathematical obligation.
