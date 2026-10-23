> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Instruction lookup and dispatch from a recovered PC

The new binary component is `CatchUp.Machine.Dispatch.M : Machine 6760 2`:
**6,736 body states plus 24 blank-tape initialization states**. Lean proves
lookup and actual instruction-entry dispatch for every finite table over
the prototype's three instructions and every natural PC, including empty
tables and out-of-range addresses. It also proves the composition from
saved-address recovery through lookup, and unbounded-length chains of
selected return instructions.

The program table is **compiled into counted finite control**. This is a
baseline with size linear in program length, not a fixed-size interpreter
with its program on tape. All table controls are included. The three
instructions are `halt`, `push` and `ret`: `push` enters the existing word
save-and-immediate-return code; `ret` recovers a saved PC and dispatches it.
There is no general call(target, continuation) instruction, arithmetic ISA,
or compiler from the Catch-Up source in this component yet.

The full verified Catch-Up cryptid remains **388,819,712 states**, with its
preserved `Halts M ↔ ¬C` theorem. C remains unresolved. This work supplies
implementation/proof components for a smaller construction; it yields no
new game-theoretic result or counterexample.

## What the machine does

The tape retains the previous two outward-growing banks: data left and
return frames right, with physical marker/data pairs `[1,b]`. Naturals are
the inherited unary self-delimiting words `0 1^n 0`, of logical length
`n+2`. No unbounded address is stored in a free machine register.

Lookup starts with the recovered PC word on top of data. It consumes its
last delimiter, pops each payload one with the already proved bit routine,
then consumes its first delimiter. A counted finite counter saturates at
the program length L. Values at least L select a distinct error control
after consuming the entire PC, rather than wrapping to a valid index.
Every pop returns the head to the origin and preserves the frame bank.

The final zero selects the actual next control for `program[PC]?`. Halt
and error are separate controls with no transition. A push enters the
existing left-bank word-transfer routine, retaining its immediate-return
continuation. A return enters the right-bank word-transfer routine; after
recovery, two paid head moves lead back to PC lookup. These are physical
transitions, not host-level changes between separately tested routines.

## Uniform Lean results

The theorems quantify over arbitrary finite programs and canonical finite
bank encodings with blank exterior. Lookup permits arbitrary raw bit
prefixes, without requiring those prefixes to encode stacks of naturals.
Malformed arbitrary tapes have no claimed abstract program semantics.

| Result | Scope |
| --- | --- |
| `bit_run`, `word_run` | Successful finite runs of both reused machines lift into the new controller. Extended old stopping states are not treated as halting-equivalent. |
| `after_one`, `get_saturated`, `ones_loop` | The physical read loop counts all payload ones, with saturation preserving the correct optional instruction lookup. |
| `lookup_correct` | For every program, natural address, and raw prefixes u,v: consume exactly the PC, preserve u,v and the head, and reach the entry for `p[address]?`. |
| `lookup_valid`, `lookup_out_of_range` | Valid PCs select their stated instruction; every address at least the program length selects the terminal error control. |
| `return_dispatch` | Recover any natural saved PC, preserve earlier frames/data, execute the two-step handoff, consume the PC, and reach its instruction entry. |
| `push_return_dispatch` | Enter the inherited save/immediate-return routine, then perform real PC lookup; its complete composition and costs are included. |
| `unwind_returns` | For any finite pending address sequence whose entries select `ret`, execute the whole return chain. Preserve earlier data/frames; the final address may select any instruction or error. |
| `lookup_full`, `return_dispatch_full`, `unwind_returns_full` | These contracts also hold in the complete initialized machine family. |
| `initializes`, `full_run`, `M_run`, `M_halts` | Paid blank initialization and the concrete demonstration execute as specified. `full_run` reaches an entry for arbitrary programs; it does not assert arbitrary-program halting. |

For a PC n above data prefix u, lookup takes exactly

```text
(n+2) * (4*length(u) + 2*n + 16)
```

successful transitions. Its cost does not scan the preserved frame bank.
Return-and-dispatch adds the already proved natural-word transfer cost and
two head-handoff transitions. The save/immediate-return composition adds
twice the transfer cost and four handoff transitions before lookup.
All word values and bank lengths are unbounded in these theorems. Unary
storage and repeated scans remain an efficiency limitation.

## Exact state and initialization costs

```text
5 boot, handoff, halt and error controls                         =     5
Existing word-machine controls                                  = 3,851
(L+2) phases × (460 bit controls + 20 bounce controls)            = 480*(L+2)
Body                                                             = 4,816 + 480*L
Initializer for chosen saved PC n                                =    12 + 4*n
Full initialized family                                          = 4,828 + 480*L + 4*n
```

There is one delimiter-header phase and L+1 saturated counter phases.
Every inherited selector/bit/continuation combination, bounce control and
unused state is counted. Instructions are wired into the generated finite
transition function; no program tape or table lookup oracle is assumed.

The sample table is `[ret, push, ret, halt]`, with L=4 and saved address n=3.
Its initializer writes all 12 physical tape bits, including markers,
delimiters and separators, using 12 write and 12 return states. The body
recovers 3 from the right bank, dispatches the fourth instruction (zero-based
PC 3), and halts with both banks empty and head home:

```text
24 initialization + 2 boot + 200 return + 2 handoff + 110 lookup = 338 steps
6,736 body + 24 initialization                                = 6,760 states
```

`state_count`, the type of M, and `M_count` kernel-check this accounting.
The fixed initialized demonstration has one chosen input. Its operational
contracts separately allow arbitrary PC values in nonblank configurations;
the initializer does not provide an external input interface.

## Numeric table and independent diagnostics

`rows`, `table_cells` and `table_correct` prove the generated finite table
equals M for all states and both scanned bits. machine.txt (`machine.txt` in the historical layout)
publishes all **13,520 numeric cells**, one zero-based state per line,
scanned zero then one, with `write L/R next` or `---` for a missing
transition. The numeric IO export is a diagnostic artifact; there is no
separate numeral-only Lean equality certificate and no native computation
in proof premises.

Independent reconstruction matches all 13,520 cells: 12,910 present and
610 absent. Native fixtures also match **5,466 program-dependent dispatch
sites**, covering every one of the 364 tables over the three opcodes with
length zero through five, both scanned bits and addresses through L+2.
Those fixtures exercise program-content and saturation boundaries; the
unbounded quantifiers follow from the Lean theorem.

The bounded physical suite passes **22,211 cases** and **58,460,342 physical
transitions**. It checks lookup with raw prefixes, recovered-PC returns,
save/immediate-return, dispatch followed by each nonterminal instruction,
return chains through depth 128, addresses through 1024, 1024-bit prefixes,
128-word frame prefixes, the blank run and an illegal first delimiter.
It compares the entire tape, head and control at each contract boundary.
Five corrupted versions are rejected: initializer write, wrong selected
instruction, counter wraparound, premature return termination and missing
table row. No game experiment or strategy-counterexample claim is made.

## Reproduction, resources and proof size

From the repository root:

```sh
python3 -B research/catchup-reuse/dispatch/verify.py --full
```

All six strict Lean commands passed (four core modules, Export and Audit),
with warnings as errors and auto-implicit disabled. All **47 new formal
theorem declarations** pass transitive axiom audit with only `propext`,
`Classical.choice`, `Quot.sound`, or fewer. No new source uses sorry,
custom axioms, native decision or the unfinished Catch-Up theorem.

Final Lean replay took **13.588 seconds**; bounded physical replay took
**6.781 seconds**. Peak recorded individual-child high-water RSS was
**3,751,215,104 bytes** on macOS 26.6.2 arm64 with 16 logical CPUs. Each
child has a 120-second wall bound; Lean has an 8,192-MiB allocator budget,
which is not an OS RSS cap. Checking times exclude interactive proof and
code development. No unbounded search or external solver run was used.

An auxiliary export expression with implicit dependent types hit its
4,000,000-heartbeat elaboration limit after 107.647 seconds. A separately
typed `exportSite` helper and the core's existing definitional-equality
setting fixed it under the same limits; the final exporter takes 2.232
seconds. Broad simplification in an early proof was likewise replaced by
specific rewrites. Neither issue refuted a mathematical claim or changed
the machine construction.

Four core sources total **24,618 bytes / 47 theorems**, with **1,958,912
compiled bytes**. Two auxiliary objects add **211,040 bytes**. Supporting
sources/scripts and the plain table total 113,964 bytes, including the
90,624-byte table; the JSON export and fixtures add 454,212 bytes. The
benchmark records all new supporting objects and outputs separately and
links all five prior manifests. These are retained artifact sizes and
local checking costs, without minimality or proof-size lower-bound claims.

The isolated package remains Lean **4.35.0-rc4**, compiler
`c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`, and Mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`. Reused Cryptids source blobs
remain pinned to `8fed07fa2981ecd96141303b0d8982116106f6eb`. All 80 source
pins, 320 dependency-object pins, 22 directly imported Mathlib sources,
49 old/helper sources and 27 baseline axiom reports pass. The other
checkout's HEAD may advance unrelated work; relevant source/object bytes
and the pinned commit's blobs are checked. The original package remains
Lean 4.27.0 / Mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900`.
Ordinary pinned imports retain the usual `.olean` cache trust boundary;
this is not a full dependency rebuild.

Frozen benchmark SHA256:
`d3a27ae62a8be180e9748e920d89b25f582d9725643fa4604c115ac21dec98f6`.
See REVIEW.md (`REVIEW.md` in the historical layout) for independent fresh-context criticism and replay.

The next concrete step is a **general call(target, continuation) instruction**:
save the continuation, dispatch the target, and later return through this
proved resolver. That must replace the inherited immediate-return path
before claiming a general calling convention or full Catch-Up interpreter.
