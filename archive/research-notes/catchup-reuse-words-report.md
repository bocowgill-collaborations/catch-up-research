> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Self-delimiting natural words and return-address storage

The new binary component is `CatchUp.Machine.Words.M : Machine 3875 2`:
**3,851 body states plus 24 blank-tape initialization states**. Lean proves
word transfer for arbitrary natural values and arbitrary bank lengths,
unbounded natural return-address save/recovery, actual immediate call/return,
and a complete 226-step blank-start demonstration. The demonstration starts
with address 3 written by its own initializer; runtime addresses in the
operation theorems have no upper bound.

This advances the separate-stack implementation toward a smaller interpreter.
It supplies no new game-theoretic lemma or counterexample. The full Catch-Up
cryptid remains **388,819,712 states**, with its preserved theorem
`Halts M ↔ ¬C`. The universal conjecture C remains unresolved.

## Representation and exact contracts

`word n = [0] ++ replicate n 1 ++ [0]`. This is a **unary**, self-delimiting
code of length `n + 2`, including the word for zero. It is not a logarithmic
binary representation of a natural. Each encoded bit uses the existing
physical marker/data pair `[1,b]`. Data grow left and return frames grow
right from the common origin; both lists are bottom first. Canonical finite
banks and the zero exterior are part of the contracts.

The new controller repeatedly pops one physical bit from the source bank
and pushes it onto the other bank. It checks the opening zero and stops
after the closing zero. The word is palindromic, so reversal from successive
pops preserves its numerical meaning. This avoids a third reversal buffer.
The delimiter flag, source side, popped bit and all inherited continuation
controls are paid physical states.

| Theorem | Kernel-checked statement |
| --- | --- |
| `read_word`, `word_cancel`, `encode_injective` | Decoding with arbitrary suffixes, unambiguous word boundaries and injective natural-stack encoding. |
| `run_present` | Every successful finite run of the reused bit machine lifts into its new control context. Old stopping boundaries can be extended; no false old/new halting equivalence is used. |
| `word_transfer` | For either source side, all raw bit prefixes `u,v`, and every natural `n`, move `word n` from `u ++ word n` to `v ++ word n`, preserve the prefixes and restore the head. |
| `push_nat`, `pop_nat` | Transfer the top natural between data and frame banks, preserving all earlier naturals. Push consumes the data operand; it does not create an unbounded value from finite control. |
| `call_correct` | From data `data ++ [target,address]`, save `address` on the frame bank and leave `data ++ [target]` on data. |
| `return_correct` | Recover every natural saved address from `frames ++ [address]` as the next data/PC word, preserving earlier frames and data. |
| `call_return_correct` | Actual save, two physical handoff steps, then return restore both banks for arbitrary addresses and stack lengths. |
| `word_transfer_full`, `call_return_full` | The operation contracts also hold inside the complete initialized family. |
| `initializes`, `full_run`, `terminal`, `M_halts` | The initializer writes all data on blank tape and the demonstration then halts. |

`call_correct` is a dispatch-ready storage boundary. It **does not look up
an instruction or jump to the target program instruction**. The recovered
return address remains a natural word on tape. Neither a universal
interpreter nor arbitrary-program compilation is claimed. The immediate
return composition is actual machine execution, rather than a host script
that changes control between two separately tested operations.

The exact transfer cost is

```text
(n+2) * (4*(length u + length v + n+1) + 24)
```

For a call/return round trip, take twice this cost plus the two handoff
steps, with `u = encode data` and `v = encode frames`. All three quantities
are arbitrary. These induction proofs, rather than finite simulation,
establish termination and correctness at arbitrary lengths. Unary encoding
and repeated scans incur a quadratic cost even on initially empty banks.

## State and initialization accounting

```text
3 global controls                                                =     3
8 contexts × (460 reused bit controls + 20 bounce + 1 done)       = 3,848
Body                                                             = 3,851
Address-3 input: 12 writes + 12 head-return controls               =    24
Complete address-3 instance                                       = 3,875
```

Every allocated combination is counted, including unreachable states and
stopping controls. The family initializes `2*n + 6` bits using `4*n + 12`
states; `state_count` proves the complete count `4*n + 3863`. Both word
delimiters, markers, separators and the payload are included. No program
or nonzero tape data are preloaded for free. This is an exact construction
count, with no minimality claim.

The new formal source defines the entire deterministic finite binary table.
`table_cells` and `table_correct` connect its generated finite rows to M
for all states and both scanned bits. machine.txt (`machine.txt` in the historical layout) serializes
all 7,750 numeric cells: one zero-based state per line, scanned 0 then 1,
with `write L/R next` or `---` for a missing transition. An independent
checker reconstructs every numeric cell and verifies the serialization.
The numeric IO export itself has no separate numeral-only Lean equality
certificate and is not a proof premise.

An attempted exhaustive kernel reduction of all generated cells exhausted
the existing 8,192-MiB allocator budget after 20.101 seconds. The final
proof instead uses generic finite-list lookup and splits only the two
scanned bits. It compiles without increasing the limit. See
FAILURES.md (`FAILURES.md` in the historical layout). This replaces costly proof computation with a
short structural argument; it changes no transition.

## Reproduction and assurance

From the repository root:

```sh
python3 -B research/catchup-reuse/words/verify.py --full
```

The retained final run passed all eight strict Lean commands (six core
files, Export and Audit), warnings as errors and auto-implicit disabled.
All **48 new theorem declarations** were transitively axiom audited and
use only `propext`, `Classical.choice`, `Quot.sound`, or fewer. No new
source uses sorry, custom axioms, native-only decision, or the unfinished
Catch-Up theorem. All previous four machine manifests and their recorded
sources, objects and artifacts still match. Baseline checks retain 80
Cryptids source pins, 320 compiled dependency pins, 49 old/helper sources
and 27 baseline axiom reports.

The independent Python suite passed **33,787 operation cases** comprising
**57,601,202 successful physical transitions**. It covers both directions,
all bit prefixes up to length three, natural prefixes up to two words,
target preservation, addresses through 1024, and 1024-bit prefixes. It
also checks the blank prefix/run, underflow and malformed first delimiter.
All 7,750 exported cells agree with reconstruction: 7,382 present and 368
missing. Four corruptions are rejected: initializer write, premature word
completion, payload write, and missing table row. An initial payload
mutation used an unvisited control context; the required negative assertion
caught it, and the retained test corrupts the actual payload-write context.
These diagnostics do not replace the universal Lean theorems.

Eight Lean commands took **17.666 seconds** in the retained run; the Python
suite took **6.882 seconds**. Peak recorded individual-child high-water RSS
was **3,739,533,312 bytes** on macOS 26.6.2 arm64 with 16 logical CPUs.
Each child has a 120-second wall limit; Lean has an 8,192-MiB allocator
budget, which is not an OS RSS cap. Compilation/checking measurements
exclude exploratory proof development; the failed reduction is separately
recorded above. There was no unbounded search.

Six new formal sources total **22,716 bytes / 48 theorems**, with
**2,103,400 compiled bytes**. Two auxiliary objects add 86,896 bytes.
The benchmark records all supporting scripts, sources, tables, outputs,
receipts and dependency snapshots. These retained sizes are reproducible
upper-bound evidence, not proof-size lower bounds. Reused supporting
mathematics remains explicitly linked through the prior manifests.

Compatibility remains Lean **4.35.0-rc4**, compiler
`c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`, Mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`, and pinned Cryptids sources at
Chess commit `8fed07fa2981ecd96141303b0d8982116106f6eb`. The older package
stays Lean 4.27.0 / Mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900`.
Ordinary pinned imported `.olean` files retain the usual cache boundary;
this run replays all new modules rather than rebuilding the whole backend.

Frozen benchmark SHA256:
`c7b7945c72fdde166e7a158f2a1e28ed6347be90e796dafc6318731e56b19ca0`.
The independent review is recorded in REVIEW.md (`REVIEW.md` in the historical layout).

The highest-value next step is **verified instruction-table lookup and
dispatch from the recovered PC word**, followed by connecting this tape
representation to the already verified Catch-Up search. Until that link
exists, 3,875 is a component count and cannot replace the full cryptid count.
