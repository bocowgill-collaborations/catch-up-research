> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# General dynamic call and return

Implemented `CatchUp.Machine.Call.M : Machine 6796 2`, with **6,736 body
states plus 60 blank-tape initialization states**. Its demonstration runs
two real nested calls and both returns, then halts after **1,478 successful
transitions** with both banks empty. The callee is selected and executed;
the old forced immediate-return handoff has been replaced.

Lean proves call, return and callee composition uniformly for every finite
program over `halt`, `call`, `ret`, every natural target and continuation,
and arbitrary earlier data/frame stacks. The program is compiled into
counted finite control. This is a general calling convention for that
prototype instruction set, not a complete Catch-Up source interpreter.
The full **388,819,712-state** Catch-Up cryptid and its `Halts M ↔ ¬C`
theorem remain unchanged. C remains unresolved.

## Calling convention and formal contracts

Both stacks retain the earlier canonical marker/data encoding: data grows
left and saved frames right. Naturals are self-delimiting unary words
`0 1^n 0`, with logical length n+2. Stack lists are bottom first. A call
starts with data `data ++ [target, continuation]`; continuation is on top.

| Theorem | Exact effect |
| --- | --- |
| `call_correct` | Consume both operands, leave earlier data unchanged, append the entire continuation to frames, consume the target through lookup, and enter `p[target]?`. |
| `return_correct` | Remove the top saved continuation, consume it through lookup, preserve all current callee-produced data and earlier frames, and enter `p[continuation]?`. |
| `call_callee_return` | Compose call with any **actual finite callee run** to the return entry that preserves the saved frame; then return to the continuation with the callee's result stack. This does not assume arbitrary callees terminate or preserve frames. |
| `call_return` | If the selected target instruction is `ret`, execute call, target selection, and the real return. |
| `call_invalid`, `return_invalid` | All addresses at least the program length select the distinct terminal error control; no address wraps into the program. An invalid call target leaves its saved continuation on frames; an invalid return continuation has been popped. |
| `nested_calls` | Execute an outer call to a call instruction, an inner call to a return instruction, then the inner and outer returns. The inner continuation selects `ret`; the outer continuation is unrestricted. All earlier stacks and four addresses are arbitrary. |
| `call_full`, `return_full`, `nested_full` | These operational contracts also hold in the complete initialized family, for arbitrary runtime operands and existing frames. |

`lookup_correct` still consumes the whole PC, handles empty programs and
all out-of-range naturals, and preserves arbitrary raw bit prefixes. The
operation contracts assume canonical finite banks and blank exterior;
arbitrary malformed tapes have no claimed abstract calling semantics.
The initializer creates arbitrary initial data with **empty frames**.
That blank-start statement is separate from the operational contracts
with arbitrary existing frames.

The exact costs reuse the previous functions. Write `E(data)` for the
concatenated natural words and

```text
transfer(u,v,n) = (n+2) * (4*(length(u)+length(v)+n+1) + 24)
lookup(u,n)     = (n+2) * (4*length(u) + 2*n + 16)
call(data,frames,t,c)
  = transfer(E(data++[t]), E(frames), c) + 2 + lookup(E(data),t)
return(data,frames,c)
  = transfer(E(frames), E(data), c) + 2 + lookup(E(data),c)
```

The two added transitions in each operation are actual head movements.
All word lengths and frame depths are unbounded in the theorems. Unary
storage and repeated scans remain an efficiency limitation; logarithmic
integer width is not claimed.

## Safe reuse of the existing proofs

The generic construction retargets two rows of its lowered-program
dispatcher, on both scanned symbols. Word control 2 now moves left to
lookup after saving the continuation, and global boot control 1 enters
call. The earlier dispatcher and word machine are preserved in their own
namespaces, with their source/object/artifact hashes unchanged.

Reusing an arbitrary old run across a changed instruction would be unsound.
The new `Boundary` proof establishes a concrete control invariant: old
right-source contexts (numeric states at least 1927) are closed under
successful transitions. From old word control 2, execution enters this
region and cannot reach the left-transfer endpoint at state 1926.
Consequently, an old successful transfer ending there did not previously
execute control 2. `word_run_before` safely reuses the complete old push
proof up to that endpoint. `word_run_right` separately reuses return runs
inside the closed right-source region. The changed handoffs are proved
directly. No global halting equivalence between the different old and new
calling behaviors is assumed.

The existing bit-pop proof, saturating-counter algebra, lookup cost,
natural codec and frame encoding are reused. The new instruction type is
lowered to the old three-value control encoding; the new machine supplies
the corrected call behavior. This changes semantics deliberately without
allocating any additional body controls.

## All initialization and state costs

For program length L and initial encoded data length D:

```text
5 existing global controls                                      =     5
3,851 existing word controls                                    = 3,851
(L+2) lookup phases × (460 bit +20 bounce controls)               = 480*(L+2)
Body                                                             = 4,816 +480*L
Initializer bits (including emitted separators and all markers)  =     2 +2*D
Initializer states (write then restore head)                     =     4 +4*D
Complete initialized machine                                    = 4,820 +480*L +4*D
```

All unused parameter combinations and terminal controls remain counted.
The program is paid for in finite control; there is no free program tape,
unbounded register or external lookup operation.

The initializer reuses `FlatInit` through a proved reflection of the tape
and transition directions: initialize a reflected body, then reflect the
whole machine. The writer therefore emits data leftward and returns home;
the body executes the ordinary unreflected call machine. `reflect_step`,
`reflect_run`, `initializes` and `step_embed` connect this to actual binary
transitions. No initial operands, markers or nonzero frames are assumed.
No new head-positioning routine or hidden bootstrap state is needed.

The demonstration has program `[call, ret, ret, halt]`, L=4, and initial
data `[1,2,0,3]`, D=14. Outer call `(0,3)` invokes the call instruction at
0. That callee executes inner call `(1,2)`. Instruction 1 returns to 2,
which returns to 3, which halts.

```text
30 emitted bits; 60 initializer states
6736 body +60 initialization                           = 6796 states
60 initialization +2 boot +470 outer call
  +328 inner call +306 inner return +312 outer return  = 1478 steps
```

`M_count`, M's type, `M_run`, `M_terminal` and `M_halts` are kernel-checked.
The physical simulator also checks the final absolute head position zero.
The complete family count is proved by `state_count`; it is not an estimate
or a minimized count.

## Numeric checks and trust boundary

`table_cells` and `table_correct` prove that all generated finite rows
reconstruct M. machine.txt (`machine.txt` in the historical layout) publishes every one of its
**13,592 numeric cells**, one zero-based state per line, scanned zero then
one, using `write L/R next` or `---` for a missing transition. All cells
match an independently reconstructed table: 12,982 present and 610 absent.
The native export bytes have no separate numeral-only Lean certificate
and are not proof premises.

Native fixtures check **6,922 sites across all 364 three-opcode programs
of lengths zero through five**, including dispatch boundaries and both
retargeted rows. The bounded physical suite passes **24,698 cases** and
**61,824,036 successful routine transitions**, including arbitrary target/
continuation combinations in the tested ranges, halt and invalid targets,
round trips, nested callees, 128-word prefixes, 1024-bit prefixes and
addresses through 1024. Whole tapes, heads and controls are compared.
Empty-bank and malformed-header diagnostics also pass.

All **seven** corruptions are rejected: initializer write, restoration of
the old immediate return, wrong target, premature return termination,
saved payload damage, counter wraparound and missing row. Finite tests
support the implementation; universal lengths/addresses come from Lean.
No game counterexample or failed strategic invariant was discovered.

## Reproduction, resources and proof size

From the repository root:

```sh
python3 -B research/catchup-reuse/call/verify.py --full
```

All ten strict Lean commands passed: eight core modules, Export and Audit,
warnings as errors and auto-implicit disabled. All **67 new theorem
declarations** pass transitive axiom audit using only `propext`,
`Classical.choice`, `Quot.sound`, or fewer. No new source uses sorry,
custom axioms, native-only decision or the unfinished Catch-Up theorem.
All six earlier manifests and their recorded sources, objects and
artifacts still match, with the baseline pin/audit checks intact.

Final Lean replay took **20.102 seconds**; bounded physical replay took
**7.290 seconds**. Peak recorded individual-child high-water RSS was
**3,754,819,584 bytes** on macOS 26.6.2 arm64 with 16 logical CPUs. Each
child has a 120-second wall bound; Lean has an 8,192-MiB allocator budget,
not an OS RSS cap. These checking times exclude interactive proof/code
development. No unbounded experiment or external solver was used.

Eight new formal sources total **36,640 bytes /67 theorems**, with
**2,386,968 compiled bytes**. Two auxiliary objects add **240,952 bytes**.
Supporting sources/scripts/table total 116,042 bytes, including the
91,092-byte plain table; the JSON export/fixtures add 651,713 bytes.
The benchmark records the new supporting mathematics, all output bytes
and receipts, and links all six previous manifests. These are retained
upper-bound artifacts, without state or proof-size minimality claims.

The isolated package remains Lean **4.35.0-rc4**, compiler
`c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`, Mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`, and pinned Cryptids source
blobs at `8fed07fa2981ecd96141303b0d8982116106f6eb`. All 80 source pins,
320 compiled dependency pins, 22 directly imported Mathlib sources, 49
preserved old/helper sources and 27 baseline axiom reports pass. The
original package stays Lean 4.27.0 / Mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900`. Ordinary pinned imported
objects retain the usual `.olean` cache boundary; this is not a full
Mathlib/backend rebuild or a cross-version theorem.

Frozen benchmark SHA256:
`b09acc6dc57e41b972e58973cc990bbff7e1bf9890f0dc73ac26229f53a9b149`.
See REVIEW.md (`REVIEW.md` in the historical layout) for the independent review and replay.

The next useful step is a **data-changing callee**, beginning with successor
on a natural data word and return through this convention. Its source-level
effect and frame preservation should be proved before extending the ISA
toward the full verified Catch-Up search. The present component alone
does not establish a smaller complete cryptid.
