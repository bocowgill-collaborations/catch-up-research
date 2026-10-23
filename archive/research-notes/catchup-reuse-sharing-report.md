> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Decoder sharing at two actual interpreter sites

The subsequent shared-restoration construction (`../restoration/REPORT.md` in the historical layout)
preserves this machine and proves an equivalent **388,819,712-state** machine,
saving a further **137,500 states**. The measurements below describe this
preserved decoder-sharing baseline.

The complete binary machine now has **388,957,212 states**. Lean proves

```lean
ConjectureMachines.Halts CatchUp.Machine.ReadShare.M ↔
  ¬ CatchUp.Search.Conjecture
```

It saves **48,890 states**, about **0.0126%**, against the preserved
389,006,102-state interpreter-reuse baseline. This is an integrated compiler
change, with a total transition generator for the full machine. The previous
machine remains available. The Catch-Up conjecture, including its zero case,
remains unresolved; this work establishes no new game outcome.

## The two sites and the return-storage contract

The actual primitive PCs are **285** (reader index 54) and **302** (reader
index 63). Their original source rows load the current main-stack or
reverse-stack symbol into the `Option Γ'` scratch register, then continue at
PC 284 or301 respectively. `Sites.main_row` and `rev_row` prove the exact row
functions. The old scratch value is overwritten for every symbol and every
old store, so it is dead at both entries.

Each caller temporarily loads a tag into this same register: `none` for main,
`some consₗ` for reverse. One shared eleven-bit read tree preserves that tag.
At the leaf, a store-dependent branch selects the original restoration and
load payload. The load then replaces the tag with the same stack symbol as
the original execution, and the original source destination is selected.

This uses the existing five-valued store, whose full size remains counted.
There is no additional store value, tape header, tape cell, alphabet symbol
or assumed blank workspace. In particular, we do not apply the earlier toy
decoder's destructive adjacent-cell protocol to live interpreter tape.
The reusable part of that proof is the read/head-restoration argument,
generalized in `ReaderSemantics.lean` to arbitrary label and store types.

`Simulation.source_stepAux` proves exact equality of the final configuration
for **every source label, every store and arbitrary binary tape**. It includes
all ordinary readers, both tagged readers, moves, plain instructions and every
writer label. The tag is inspected before either payload overwrites it.
`step_eq` gives equality of the complete TM1 transition functions. Existing
lazy-graph, binary-lowering, initialization and finite-index transport proofs
then preserve halting in both directions. The same literal 204-row Catch-Up
program and proved source-search theorem supply the end-to-end result.

## Complete state accounting

One full eleven-bit reader tree contributes `3*(2^11-1) = 6,141` graph nodes.
We use 1,733 readers instead of 1,734, then add 1,250 return-dispatch branches
and two caller tag-load nodes. All old payload/restoration families stay paid.
The net reduction is 4,889 nodes. Every node still pays for all five store
descriptors and both binary physical phases: **4,889 × 5 × 2 = 48,890 states**.
Load/branch administration may fold into a Post instruction during execution;
its nominal descriptor states are nevertheless retained and counted.

| Component | Complete count |
| --- | ---: |
| Existing preparation/payload/restoration graph | 26,034,392 nodes |
| New return dispatch | 1,250 nodes |
| 1,733 reader trees | 10,642,353 nodes |
| Existing writer suffix graph | 2,210,760 nodes |
| Two tag loads | 2 nodes |
| **Total graph** | **38,888,757 nodes** |
| Post controls, including start and halted/default stores | 194,443,791 states |
| Binary body, including return controls | 388,887,582 states |
| Full blank-tape initializer | 69,630 states |
| **Complete machine** | **388,957,212 states** |

`node_count`, `post_count`, `body_states` and `generated_states` prove these
counts in Lean. The input is exactly the previous 34,815-bit program/root/table
stream. `initializes` proves the actual 69,630-step run from state zero on the
all-zero two-way tape, reaching body entry with the full input and restored
head. No program or return data are preloaded for free. Counts include all
enumerated states, including unused ones; no minimality claim is made.

## Checks and evidence

From the workspace root:

```sh
python3 -B research/catchup-reuse/sharing/verify_share.py --full
```

All ten strict Lean commands passed: the six new formal modules, endpoint
audit, formal wrong-tag control, exhaustive native reader tests and physical
fixture export. The final evidence replay reports `TWO_SITE_SHARING_PASS`.
There are 23 new audited endpoints, plus 27 preserved baseline endpoints. They
use only `propext`, `Classical.choice`, `Quot.sound`, or fewer. No desired-result
axiom, `sorryAx`, native-decider axiom or unfinished conjecture enters the
headline theorem.

`ReaderTests.lean` tests 40,960 physical cases: all 2,048 eleven-bit words, all
five old stores, both sites and two live neighboring-cell patterns. This
includes binary words outside the codec's canonical 1,250-symbol range. Every
case reaches the expected next source entry in 24 ordinary binary transitions,
with restored head and unchanged checked cells from −2 through 13. Expected
glyphs use the actual decoder, so this is exhaustive native regression over
these finite inputs. The arbitrary-tape Lean theorem supplies the general
preservation result.

Five actual initialized binary-program traces were exported and independently
replayed by Python. Their input bits also match the independently implemented
constructor-table and natural/stack codec from the preserved baseline checker.

| Source fixture | Physical transitions | Observation |
| --- | ---: | --- |
| Zero | 19,944 | Halt |
| Successor on `[3]` | 38,370 | Halt |
| Zero branch on `[0,6]` | 188,850 | Halt |
| Positive branch on `[2,6]` | 228,984 | Halt |
| `fix succ` on `[]` | 200,000 | Explicit bound reached |

The loop observation is not a nonhalting proof. All five trace lengths agree
with the previous machine. Across visited-state exports, 542,468 transition
cells were replayed, with overlaps retained. We did not enumerate the entire
machine. Each fixture starts blank and its complete paid prefix is checked.

Three physical controls are rejected: corrupting the initializer's first
write, deleting a visited row, and changing caller 1's encoded return store
from tag 1 to tag 0. The latter uses the branch fixture, which visits both
sites; the zero fixture visits only caller 0. Separately,
`NegativeShare.tag_required` kernel-proves that the two tag choices produce
different source destinations for **every** tape/store. It is an obstruction
to dropping this return information, not a lower bound on machine size or
a Catch-Up counterexample.

## Compatibility, resources and proof size

This uses exactly the baseline's isolated Lean 4.35.0-rc4, compiler commit
`c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`, Mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`, and Chess source content at
`8fed07fa2981ecd96141303b0d8982116106f6eb`. The runner checks the actual
compiler version, pinned source blobs and compiled artifacts. The original
Lean 4.27 package and all preserved baseline sources, scripts, compiled
modules and retained artifacts remain unchanged. Existing backend/Mathlib
compiled dependencies are reused through ordinary Lean imports; this is not
a fresh rebuild of the whole dependency closure.

`benchmark.checked.json ` records all receipts and hashes. The ten Lean
commands total 147.828 seconds on macOS 26.6.2 arm64 with 16 logical CPUs; maximum
recorded individual-child high-water RSS is 7,213,645,824 bytes. Per-child limits
are 120 seconds, Lean's 8,192-MiB allocator budget and one-MiB output, except
16 MiB for physical fixture export. The allocator budget is not an OS RSS cap.
Times exclude interactive development and prior dependency builds. No
unbounded game search or external solver was run.

The six new formal modules contain 25,610 source bytes and 46 theorems; their
compiled modules total 1,300,872 bytes. The formal wrong-tag control adds one
auxiliary theorem. All auxiliary Lean/checker sources, reused semantic/source modules (118,977 bytes) and the 80-module reused backend closure (5,795,840 source bytes) are
recorded separately. This counts the supporting mathematics rather than
calling the final iff invocation the whole proof. It establishes an artifact
size upper bound, with no shorter-proof or minimality claim.

Fresh-context independent review is recorded in `REVIEW.md`. It checks the
mathematics, finite assembly, pinned-cache boundary and evidence. Model review
adds criticism; Lean's kernel remains the formal verification authority.

The single next optimization is to share these same sites' identical
eleven-step head-restoration chains, placing the tag dispatch after the
common restoration. That targets a larger paid duplication while retaining
this proved two-site contract. Any replacement must again prove both halting
directions and count every payload, dispatch, store and initializer state.
