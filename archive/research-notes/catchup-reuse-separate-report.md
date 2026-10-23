> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Separate-stack binary prototype

The complete prototype is `CatchUp.Machine.Separate.M : Machine 464 2`:
**460 body states plus four initialization states**. Lean proves shared
parameterized push/pop correct for arbitrary stack lengths and contents,
one-bit call/return correctness, a family of unbounded-depth pending returns,
the actual initializer, and a 46-step blank-start demonstration. Every one of
its 928 transition cells is published and compared to the machine in Lean.

This is a component prototype, not a 464-state Catch-Up cryptid. The full
Catch-Up machine remains the preserved 388,819,712-state construction with
`Halts M ↔ ¬C`. No new game outcome or resolution of C follows here.

## Storage and sharing

The data stack grows left and the return stack grows right from the origin.
Words are bottom first. Bit `b` is stored as a pair `(1,b)`; a blank marker
position ends a stack. The origin and its two neighboring cells are zero.
Stack growth never shifts the opposite region. A zero data bit therefore
cannot be mistaken for the end marker. `wire_injective` and `banks_injective`
prove that blank extension identifies neither distinct words nor distinct
pairs of stacks, including words ending in zero.

Both regions use the same parameterized push/pop routines. A selector chooses
the outward/inward directions; the saved bit and auxiliary continuation stay
in finite control. Calls use the right-region push code to save the return
address, then enter the selected continuation. Returns use the same right-region
pop code to recover it. The two return destinations are one-bit addresses.
The left region is preserved throughout those operations.

The finite selector/value/continuation parameters are not free registers.
Every corresponding physical state is counted. This construction shares code
for repeated calls with the same parameters; different parameter values still
have distinct physical controls. It tests separate storage and the operation
contracts, without eliminating all continuation-induced control multiplication.

## What Lean proves

All statements below refer to ordinary binary write/move transitions on the
two-way tape. Inputs are canonical encodings of two finite stacks; malformed
tapes have no claimed abstract meaning.

| Result | Scope |
| --- | --- |
| `push_correct`, `push_full` | For either region, any word of length n, arbitrary other word, bit and continuation: append precisely that bit, preserve the opposite region, restore the head, finish in `4*n+8` steps. |
| `pop_correct`, `pop_full` | From word `w ++ [a]`, recover `a`, erase its pair, preserve the other region, restore the head, finish in `4*w.length+12` steps. |
| `pop_empty` | Empty pop preserves both regions and reaches explicit underflow in six steps. |
| `call_correct` | For any existing data/return words and either address/target bit: push the address and jump to the target entry. |
| `return_correct`, `return_from_entry` | For any return word `frames ++ [address]`: pop that address and reach its corresponding entry, with data unchanged. |
| `call_return_correct`, `call_return_full` | A call to the returning subroutine followed by its actual return restores both words and reaches the saved entry in `8*frames.length+20` steps. |
| `nested_returns`, `nested_returns_full` | For any existing words and any depth, unwind suffix `[0] ++ replicate depth 1` in LIFO order, reaching entry zero while preserving the existing words. |

The nesting theorem has no depth bound. Its suffix is specific because entry
one executes return and entry zero starts data pop. Automatic unwinding of an
arbitrary address string is not claimed. The general single-return theorem
does recover either top address for arbitrary preceding frames. This is a
two-stack, two-address prototype; four independently accessed banks and
arbitrary-width program addresses remain future obligations.

Proofs reuse Mathlib tape operations, the existing `FlatInit` initialization,
step-embedding and reachability theorems, and elementary list induction.
The new arbitrary-length scan/restoration proofs include exact physical step
counts, rather than inferring termination from bounded tests. Theorems lift
the operations into the initialized machine through exact step simulation.

## Full count and blank start

The finite control is explicitly numbered:

```text
23 phases × 2 region selectors × 2 saved bits × 5 continuations = 460
two zero writes followed by two return moves                 =   4
complete binary machine                                     = 464
```

All combinations are paid, including unused combinations and stopping
controls. `q_value` proves the arithmetic numbering. `state_count` gives the
complete count. The initializer contains no preloaded data or assumed program
tape. For this empty-region layout the separators are already blank; the
published version nevertheless pays for explicitly writing two of those zero
cells and returning. Those four states are conservative overhead, not a
minimal initialization claim.

`initializes` proves the actual four-step prefix. The demonstration then
pushes data bit one, calls a subroutine after saving return address zero,
returns, pops the data bit and stops with empty regions and restored head.
`body_run`, `full_run`, `terminal` and `M_halts` prove the 42-step body and
46-step complete run, followed by a missing transition.

`rows` enumerates all 464 rows, including 80 missing transition cells. The
native export is used to propose an ordinary literal Lean table in
`Published.lean`. `Published.literal_correct` compares all 928 cells in the
kernel and proves `Machine.ofRows literalRows = M`. The same exported cells
appear in `machine.txt`, with zero-based state numbers and `---` for halts.
The Python table data therefore do not become an unchecked proof premise.

## Executed checks and resources

From the workspace root:

```sh
python3 -B research/catchup-reuse/separate/verify.py --full
```

All eight strict Lean commands passed: five formal modules, export, literal
table verification and the axiom audit. All 56 new requested endpoints use
only `propext`, `Classical.choice`, `Quot.sound`, or fewer. There is no
`sorryAx`, custom result axiom, native decision premise or conjecture premise.
The count, arbitrary-length contracts and published table are kernel checked.

Independent Python tests passed **105,072 cases**, executing **8,403,624
physical transitions**. They test push/pop on both sides and every finite
bit/continuation parameter, words up to five bits with opposite words up to
three bits (pop inputs add their top bit), both call targets and addresses,
and pending-return depths zero through eight. Additional zero, one and
alternating 4,096-bit words test both sides. Complete state, head and sparse
tape equality are checked at each operation boundary. All four corruptions
are rejected: changed initializer write, faulty pop erasure, incorrect return
destination and missing row. The complete blank prefix/run is replayed too.
These finite tests are diagnostics; the Lean contracts provide the unbounded
length and depth guarantees.

The eight Lean commands total **25.692 seconds** on macOS 26.6.2 arm64 with
16 logical CPUs. Maximum recorded individual-child high-water RSS is
**4,885,151,744 bytes**. The separately bounded Python run takes 1.275 seconds.
Each child has a 120-second wall bound; Lean has an 8,192-MiB allocator budget
and 16-MiB output limit. The allocator budget is not an OS RSS cap. Timings
exclude interactive proof development and existing dependency builds.

Five formal modules contain **22,232 source bytes and 54 theorem declarations**;
their compiled objects occupy **4,124,784 bytes**. Auxiliary sources/table files
add **43,317 bytes**, including the **19,575-byte** literal-table Lean source
and **5,200-byte** plain transition table. The three auxiliary compiled objects
occupy **3,882,032 bytes**; two auxiliary theorems certify the literal table.
All helper, source, object, table and evidence hashes are in the benchmark.
These are artifact-size upper bounds, not proof-size or state lower bounds.

The isolated package stays on Lean 4.35.0-rc4 / compiler commit
`c29b6dda4f7c20e3eeaa717c4e565663c5cfa364` and Mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`. The original package stays on Lean
4.27.0. The prior full-machine baseline, sharing and restoration manifests,
source pins, cache hashes and 27 baseline axiom reports pass preservation
checks. Existing imported objects retain the ordinary Lean dependency-cache
trust boundary; the full backend/Mathlib closure is not freshly rebuilt.
The new prototype directly imports `FlatInit` and Mathlib, and does not need
the Catch-Up conjecture or interpreter semantics as premises.

The frozen benchmark SHA256 is
`87e2343e29f17ece4cb9c0f5e98792744368c3de982d6059702c45cd730c963b`.
Independent fresh-context review and its exact scope are in `REVIEW.md`.
The reviewer independently rebuilt all eight modules with byte-identical
objects, reproduced all 56 audits and the complete export, reran the supplied
physical tests in a temporary directory, and checked 12,150 further cases
with a separately written simulator. It accepted the result within the
stated component and dependency-cache scope.

## Highest-value next step

Implement self-delimiting natural-number words on these bit stacks and prove
word push/pop, including arbitrary-width saved return addresses. That connects
this storage prototype to the values and frames of the existing Catch-Up
evaluator. A general finite controller, needed arithmetic/copy operations and
the full search simulation still have to be built and counted before this
can replace the verified cryptid. No full-interpreter reduction factor has
been established by this prototype.
