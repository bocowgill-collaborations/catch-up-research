> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Successor as a data-changing callee

Implemented and proved a binary successor callee using the existing separate
bit stacks, natural-word codec, lookup and general calling convention. Its
complete blank-tape demonstration is `CatchUp.Machine.Succ.M : Machine 7206 2`:
**7,162 body states plus 44 initialization states**. It initializes operand 3,
target 0 and continuation 1; calls the successor instruction; returns to halt;
and stops after **682 successful transitions**, with data `[4]`, empty frames
and the head at its original origin.

This is a component for the proposed smaller interpreter. The complete Catch-Up
cryptid remains **388,819,712 states**, with its preserved `Halts M ↔ ¬C` theorem.
C remains unresolved. This result supplies no new game outcome and does not yet
replace the complete search machine.

## Uniform operational theorems

The instruction set is `halt`, `call`, `ret`, `succ`. A program is compiled into
counted finite control. Data grows left and frames right; lists are bottom
first. Both banks use the preserved marker/data layout, with natural words
`word(n) = 0 1^n 0`, of logical width n+2.

| Theorem | Exact conclusion |
| --- | --- |
| `lookup_correct` | Consume the complete natural PC, select the actual four-opcode instruction or the terminal error state, and preserve arbitrary raw bit prefixes on both banks. All addresses, including those beyond program length, are covered. |
| `call_correct`, `return_correct` | Preserve the existing calling convention: consume target/continuation operands, save the complete continuation, enter the selected instruction; return pops the saved continuation and preserves arbitrary callee-produced data and earlier frames. |
| `successor_bits` | Change `u ++ word(n)` to `u ++ word(n+1)` on the left, preserve the arbitrary raw prefix u and arbitrary right-bank bit string v, restore the head, and enter the actual return routine. |
| `successor_nat` | Change `data ++ [n]` to `data ++ [n+1]` with every earlier data word and every saved frame preserved. |
| `call_successor_return` | If the target instruction is `succ`, consume the two call operands, increment n, execute return and dispatch the saved continuation. No assumption on the continuation's opcode is needed. |
| `nested_successor` | An outer call to `call` executes an inner call to `succ`, increments data, returns to a `ret` instruction and then returns through the outer continuation. All earlier data/frames, program lengths and five natural operands/addresses are arbitrary. |
| `successor_full`, `call_successor_full` | The operational contracts also hold inside the fully initialized machine family, with arbitrary runtime stack prefixes and frames. |
| `blank_run`, `blank_terminal`, `blank_halts` | For every natural n, the demonstration family initializes `[n,0,1]` from an all-zero tape, executes call/successor/return, reaches halt with `[n+1]`, and halts. |
| `state_count`, `family_count`, `M_count` | Exact paid control counts, including initialization; the demonstration family has 7,194+4n states and M has 7,206. |

No upper bound on n, addresses, program length or stack depth occurs in these
contracts. Zero is included. The operational contracts assume canonical finite
banks and blank exterior. They do not assign abstract natural-number semantics
to arbitrary malformed tapes. `malformed_closing_bit` proves that a closing
one selects the distinct error control after the pop; the finite suite also
checks empty-stack underflow.

## Mechanism, reuse and counted costs

Successor uses three existing bit operations: pop the final delimiter zero,
push one, then push a new closing zero. For
`w = u ++ [0] ++ replicate n 1`, these take

```text
pop zero and restore/dispatch head      4*length(w) +14
push one and restore/dispatch head      4*length(w) +10
push zero and restore/dispatch head     4*(length(w)+1) +10
Total = succCost(u,n) = 12*(length(u)+n+1) +38
```

The final control is the ordinary return routine, rather than a symbolic
return operation. `call_callee_return` composes actual finite machine runs;
`call_successor_return` supplies the proved successor run as that premise.
The updated data length is used in the subsequent return cost. Nested calls
retain both real saved continuations throughout the inner computation.

The previous Call/Words/Dispatch/Separate machines and proofs are preserved.
The extension copies their paid controls and introduces three contexts of
460 bit controls plus two bridge controls each. The old word and global
transitions retain their semantics. Only completed-PC lookup bounces route
the newly selected opcode to the new entry; all other successful bit
transitions are copied. A lowering sends `succ` to old `halt` only for the
reused allocation/body definition. The actual four-opcode lookup is separately
proved and selects successor. It does not use the lowered halt as its answer.

The fragile old-word reuse retains the already proved closed right-context
invariant from Call. A run ending before the old return boundary cannot have
executed that boundary, while return runs stay within the right-source region.
Thus the push and return proofs are lifted on exactly the valid scopes.
No claim that arbitrary old and extended machine runs coincide is needed.

For program length L and initial encoded data length D:

```text
Existing paid call/word/lookup body       4,816 +480*L
New successor contexts                  3*(460+2) =1,386
Complete body                            6,202 +480*L
Initializer bits                         2 +2*D
Initializer states and steps             4 +4*D
Complete initialized machine             6,206 +480*L +4*D
```

Every unused parameter combination and terminal state remains counted. Program
information is in paid finite control; no free program tape, unbounded return
register or uncounted dispatch operation is assumed. The initializer reuses the
proved reflected FlatInit writer: it creates all left-bank words and markers
from a blank binary tape, returns home, and enters the unreflected body. Initial
frames are empty; arbitrary existing frames belong to the separate runtime
contracts.

For M: L=2 (`[succ,halt]`), initial data `[3,0,1]`, D=10, so 22 bits require
44 initializer states. Call takes 254 steps, successor 86, return 296:

```text
7,162 body +44 initialization =7,206 states
44 initialization +2 boot +254 call +86 successor +296 return =682 steps
```

Unary naturals and repeated whole-bank scans remain important efficiency
limitations. This is an explicit baseline upper bound, with no claim of
constant program-independent control, logarithmic word width or minimality.

## Checked evidence and trust boundary

From the repository root:

```sh
python3 -B research/catchup-reuse/succ/verify.py --full
```

The final replay passed **nine strict Lean commands**: seven core modules,
Export and Audit, with warnings as errors and auto-implicit disabled. All
**72 new theorem declarations** pass transitive axiom audit, using only
`propext`, `Classical.choice`, `Quot.sound`, or fewer. No new verified source
uses sorry, custom axioms, native-only proof computation or the unfinished
Catch-Up conjecture.

`table_cells` and `table_correct` prove the generated finite rows reconstruct M.
machine.txt (`machine.txt` in the historical layout) publishes all 14,412 numeric cells, one zero-based
state per line, scanned zero then one: `write L/R next`, or `---` for a missing
transition. Every cell matches separate reconstruction; 13,762 are present
and 650 absent. Native export bytes have no separate numeral-only kernel
certificate and are not proof premises.

The exact bounded physical suite passes **18,809 cases** and **38,286,790
successful routine transitions**. It compares final whole tapes, controls and
head positions, exercises every opcode and invalid dispatch, and checks actual
nested changed-data calls and returns. There are 7,201 raw successor cases,
8,116 complete successor call/returns, 1,024 other calls, 1,353 returns,
393 lookup cases and 722 variable-program cases. Large cases include natural
operands and addresses through 1,024, 1,024 raw prefix bits and 128 earlier
natural words/frames. Native fixtures compare **42,774 sites across all 1,365
four-opcode programs of lengths zero through five**, including new bridges.
The variable-program executions use reconstructed tables whose changed sites
are checked against those fixtures; universal execution contracts are the Lean
theorems.

All **nine** deliberate corruptions are rejected: initialization write,
skipped increment, wrong payload, wrong closing delimiter, wrong head return,
successor routed to halt, premature return termination, malformed delimiter
accepted, and missing table row. Two malformed/empty-bank diagnostics pass.
A timeout is never treated as a mathematical outcome. These finite checks are
evidence about the exact encoded component, not a proof by testing.

All seven preceding manifests and their recorded sources, objects, helpers
and artifacts remain unchanged. Pinned dependency/source checks and the 27
baseline axiom reports pass. The isolated package remains Lean 4.35.0-rc4,
compiler `c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`, Mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`, with Cryptids dependency blobs at
`8fed07fa2981ecd96141303b0d8982116106f6eb`. The original Catch-Up package
remains Lean 4.27.0 / Mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900`.
Ordinary pinned imported objects retain their usual cache trust boundary;
this replay is not a complete Mathlib/backend rebuild or cross-version proof.

The fresh independent review additionally replayed the seven core modules,
Export and Audit into isolated output paths. Its separate numeric model
reconstructed the foundational bit/word/call layers and the new extension,
matched every sample cell and all 42,774 fixture sites, and passed **6,488
additional cases /58,155,956 successful transitions**, including operand 4,096,
1,077-bit raw prefixes, 128 earlier data words, 64 earlier frames and actual
changed-data nested returns. This is independent model criticism and diagnostic
evidence alongside Lean verification, rather than human approval or a full
Catch-Up source simulation. Exact review scope is in REVIEW.md. The independent scripts, receipts and logs
are retained in review-evidence (`review-evidence/README.md` in the historical layout); the identical Export.log
is shared with the producer artifacts.

## Checking cost and proof size

Final Lean checking: **19.485 seconds**; bounded physical checking:
**4.778 seconds**. Peak recorded individual-child high-water RSS:
**3,786,555,392 bytes**, on macOS 26.6.2 arm64, 16 logical CPUs. Each child
has a 120-second wall bound. Lean's 8,192-MiB allocator budget is not an OS RSS
cap. Lean output is bounded to 16 MiB, physical output to 1 MiB. Interactive
proof-generation/development time is separate and not included in replay times.

The seven new formal sources contain **41,074 bytes /72 theorems**, with
**3,001,096 compiled bytes**. Two auxiliary compiled objects add 265,880 bytes.
The recorded helpers and plain table total 123,500 bytes; output artifacts
and receipts total 3,192,921 bytes. The benchmark records all this supporting
mathematics and links the seven older manifests, rather than treating a short
invocation as the entire proof. These are exhibited upper bounds, not proof-size
or machine-size lower bounds.

Frozen benchmark SHA256:
`e7f49bd1448cc29ea19ccd7dde7daee1a225135eaa897d7ad45da6df4b106dbe`.
Independent review is recorded in REVIEW.md (`REVIEW.md` in the historical layout).

No game counterexample or strategic invariant was tested in this component
session. The highest-value next step is **conditional predecessor/zero test**
with a proved data/frame contract and actual branch dispatch. Together with
successor and dynamic calls, it supplies the next arithmetic/control primitive
needed to connect this smaller architecture to the verified Catch-Up search.
