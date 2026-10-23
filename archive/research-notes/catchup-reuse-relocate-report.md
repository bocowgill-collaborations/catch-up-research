> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# All 92 actual switch copies: relocation complete

The completed local switch contract is now proved for every actual switch copy
in both `Lowering.machine` and its initialized, 211,100,482-state `Lowering.M`.
The proof starts at the actual projected instruction entry, executes the paid
right/left bridge, runs the copied switch, and resumes the exact program
continuation. Results, saved inputs and earlier caller frames are arbitrary.
No transition, allocation or initializer was changed.

The main statements are in `CatchUp/Machine/Lowering/Relocation.lean`:

- `all_switches`: candidate-body execution for any actual switch placement.
- `initialized_switches`: execution under the actual initialized machine's
  four-state numeric offset.
- `program_switch`: the same statement for any actual program instruction
  satisfying `program[pc]? = some (.bank .switch next)`. Callers do not need to
  supply a placement or a numerical relocation certificate.
- `initialization_preserved`: the existing four-step blank initializer is intact.

Writing `E` for the proved widening of `Cases.entry projection`, the initialized
contract is:

```lean
program[pc]? = some (.bank Bank.switch next) →
∃ steps, FlatInit.runFrom M steps
  (FlatInit.embed bits body
    ⟨E pc, natBanks result (frames ++ Switch.savedFrames data)⟩) =
  some (FlatInit.embed bits body
    ⟨E next, natBanks data (frames ++ [result.getLastI])⟩)
```

The actual theorem uses `entryState` in place of the abbreviation `E`. Natural
banks are bottom first: `getLastI` retains the top result word and returns zero
for an empty result. The previous entrance/restoration/extraction proof supplies
physical tail erasure and restoration of the exact saved-input format.

`switch_count` kernel-checks that there are exactly 92 switch placements.
`pc_unique` excludes duplicate instruction addresses. `switch_coverage` proves
that **every actual program switch instruction** supplies such a placement;
`switch_mem` also identifies these as exactly the switch members of the original
placement list. This is not a proof about 92 separately invented example machines.

## What makes relocation sound

1. Generic `place_lower`, `place_upper` and `place_find` establish interval
   ownership and actual first-match lookup. Each copy owns its complete body
   and its already-paid entry bridge. The checked allocation bounds exclude
   failed `pack` operations or accidental selection of an adjacent copy.
2. Generic segment/cell lemmas prove local target closure. The switch metadata
   check verifies every non-return target stays inside the local body. Successful
   execution can therefore be lifted without falling through a bounds check.
3. A positive-prefix-sum theorem proves strict hook-address growth after every
   bank instruction. This proves distinct hooks for **all 277 bank sites**, not
   just the switch copies. The only explicit site data is a 277-record list
   checked equal to the actual `sites` construction by the kernel. No complete
   numerical transition table or external address calculation is a proof premise.
4. `push_zero_entry` and `bank_entry` prove the intercepted hook is exactly the
   real projected interpreter entry. The generic hook and bridge transition
   theorems include both movement instructions and restore the original tape
   position for an arbitrary tape, including every caller frame.
5. `successful_step` and `successful_run` lift the raw local execution. The raw
   external state -1 maps to the real `Cases.entry projection next`, not to a
   stopping state. In particular, the local finite view's stopping index 15387
   is **not** confused with the full candidate's executable entry bridge at
   `base + 15387`. The proof uses the raw local contract for this reason.
6. Existing `FlatInit.step_embed` supplies the initialized-machine lift. The
   contract includes its four-state offset; the original four-step blank writer
   remains proved. The theorem does not assert that every switch is reachable
   from blank, or that its caller continuation halts.

The eight new modules are `RelocationGeometry`, `RelocationTargets`,
`RelocationEntry`, `RelocationData`, `RelocationHooks`, `RelocationSites`,
`RelocationRun` and `Relocation`. All **59 new theorem endpoints** are audited,
including the supporting geometry, metadata, index, prefix-sum and simulation
lemmas. Their source/compiled sizes and replay metrics are recorded below and in
`benchmark.checked.json`; previous support is retained in the earlier manifests.

## Build, diagnostics and trust boundary

Reproduce from the repository root:

```sh
python3 -B research/catchup-reuse/relocate/verify.py --full
```

The gate replays eight proof modules, the axiom audit and a native diagnostic
export. The ordinary theorem proofs use Lean's kernel. Every audited dependency
is a subset of `propext`, `Classical.choice`, `Quot.sound`; two new theorems are
axiom free. No `sorryAx`, custom axiom, unfinished conjecture dependency, external
solver assertion or native-only proof is accepted. Pinned imported ordinary
objects are reused; the entire imported library is not rebuilt.

The separate native diagnostic export probes **24,288 cells** across the body
and initialized machines, covering both symbols at selected internal controls,
every hook, every entry bridge and the actual external-return rows of all 92
copies. The Python checker compares them to the frozen local table and relocation
formula, checks continuation/address metadata, then runs **31,559 whole-tape
cases**, totaling **42,997,200 transitions**. Every copy receives the complete
343-case small grid; three larger cases add long tails, saved inputs and frames.
The maximum case is 432,452 transitions. Empty/default-zero results, nonempty
zero top words, discarded tails, empty inputs and nonempty caller frames occur
in every copy's grid. All **ten deliberate corruptions** are rejected.

These physical runs use the actual native cells when available and the proved
relocation formula with frozen rows elsewhere. They are not described as native
execution of the entire full machine at every step. They compare the complete
tape, final head origin and exact continuation, rather than just decoded logical
outputs. They are finite diagnostics; the universal guarantees are Lean theorems.
No intact-controller counterexample or new game outcome was found.

Each subprocess has a 120-second deadline. Lean uses `-M8192` and a 16 MiB output
limit; physical checks use 1 MiB output, 50 million steps per positive case and
100,000 per corrupted case. Exhaustion is an error. The allocator setting is not
an OS RSS cap. Interactive proof-generation and failed-attempt costs were not
instrumented separately. Recorded timings measure successful replay/checking.
The new hostile review is an implementing-agent self-audit, not independent review.

Pins are unchanged: Lean 4.35.0-rc4 commit
`c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`, Mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`, Cryptids blobs
`8fed07fa2981ecd96141303b0d8982116106f6eb`. The original Lean 4.27.0/Mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900` game package is preserved.
All **17 prior snapshots and 755 source/object/artifact records** remain intact.

The final replay used **nine ordinary proof/audit commands in 31.814 seconds**,
plus the separate native export in **97.702 seconds**. The instrumented physical
check took **21.541 seconds**. Peak child RSS was **6,891,044,864 bytes** on macOS
26.6.2 arm64, 16 logical CPUs. The eight new UTF-8 Lean sources total **38,894
bytes**; their compiled objects total **2,469,520 bytes**, excluding separately
recorded prior support. The diagnostic native export is 558,994 bytes. These
serialization sizes are upper bounds on this artifact, not proof-size minimality
claims. There are **45 new manifest records** and 755 preserved prior records.

Frozen benchmark SHA-256:
`50bc7712027ce4a21bfd8d5ffe3b386d2a5e8ffef36c3613279e8e8517dffa80`.
Native diagnostic export SHA-256:
`dd109585053d32145e4c0c39de26558433509c2047f3c49129b94450481ff1a6`.
The frozen prior local-table export remains
`056a67ec46fc1082715ed52d32d176f92d0d88131ac9a954885396555c5c2746`.

## Remaining before certifying the smaller cryptid

The current certified cryptid remains **388,819,712 states**, with its existing
`Halts(M) ↔ ¬C` theorem. The candidate remains **211,100,482 kernel-counted states**,
including its four initializer states. This milestone adds or removes zero states.
It closes switch relocation; it does not yet establish that candidate's full
blank-tape halting equivalence.

The remaining substantive obligations are:

1. Universal contracts for the actual save, finish and source-successor bodies,
   and their 185 remaining placements. The new geometry, hook and index lemmas
   apply to all bank sites and can be reused.
2. Preservation/integration of inherited interpreter operations under the real
   hook redirects, instead of assuming proofs about the unmodified interpreter
   automatically apply to the candidate.
3. Full simulation of the actual 204-node DAG, including partial computations,
   `cons`, composition, case and fixpoint, in both halting directions.
4. Compose that simulation with the already-verified source/search equivalence
   and paid blank initializer, then audit the final smaller-machine theorem.

The single highest-value next step is the **actual saveBody contract for arbitrary
input and caller frames**, followed by relocation into all 92 save copies using
the now-proved shared lemmas. C remains unresolved in this campaign. No claim of
least state count, shortest proof or a new counterexample is made.
