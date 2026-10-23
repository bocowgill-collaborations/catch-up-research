> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Literal push and generated dynamic calls

Implemented `push(value, continuation)` in the binary interpreter prototype.
It creates the complete natural word during execution, preserves earlier data
and frames, restores the head, and enters the specified continuation. Lean
proves this for every natural value and arbitrary finite programs and stacks.

The complete blank-tape demonstration is
`CatchUp.Machine.Literal.M : Machine 38658 2`: **38,634 body states plus 24
initialization states**. Initialization writes only working operand 3. Execution
then creates target 3 and continuation 4 as real data words, calls successor,
returns and halts with data `[4]`, empty frames and head 0 after **2,076 successful
transitions**. Neither call operand is supplied on the initial tape.

This is a smaller-interpreter component. The complete Catch-Up cryptid remains
**388,819,712 states**, with its preserved `Halts M ↔ ¬C` theorem; C remains
unresolved. The new instruction set is not yet connected to the complete
verified search source.

## Formal contracts and frame preservation

The source has seven opcode forms: halt, call, ret, succ, pred(z,s), test(z,s),
push(n,next). Lists are bottom first, data grows left and frames right. Naturals
retain the unary framing `word(n)=0 1^n 0`, of logical width n+2, with binary
marker/data pairs on the physical tape.

| Theorem | Kernel-checked effect |
| --- | --- |
| `literal_push_bits` | Append `word(n)` to an arbitrary left raw-bit prefix u, preserve the arbitrary right bank v, restore home and enter the actual continuation. |
| `literal_push_nat` | Append a new natural n after arbitrary earlier data words and preserve every earlier saved frame. Zero and empty data are covered. |
| `literal_invalid_continuation` | Complete the word and reach the distinct terminal error control if the continuation is outside the program, with data and frames otherwise correct. |
| `pushes_dynamic_call` | Execute two literal instructions to create the complete target and continuation words, then execute the real dynamic call. Both operands are consumed, the continuation is saved and target lookup is actually performed. |
| `call_literal_return` | A dynamically selected callee can execute literal push and return the new word through its saved continuation; all earlier words/frames survive. |
| `nested_literal` | Execute outer call, inner literal-producing call, its return to ret, and outer return; preserve arbitrary earlier frames and the new result word. |
| `pushes_call_successor_return` | Generate both call operands, call successor on the working word and return its incremented value. |
| `repeated_push` | One fixed self-looping push instruction can execute any finite number k of times, appending k words with unchanged frames. Its machine/program does not depend on k. |
| `literal_push_full`, `call_literal_full` | The operational contracts remain valid inside the complete initialized binary machine family. |
| `blank_run`, `blank_terminal`, `blank_halts` | For every n, the demonstration starts blank with initialized data `[n]`, generates its call operands, and halts with `[n+1]` and empty frames. |
| `blank_repeated` | For every literal n and repetition count k, the same self-loop program starts with empty data from blank and reaches exactly k created words. This is a finite-prefix theorem, not a separately asserted non-halting theorem. |
| `state_count`, `family_count`, `M_count` | Exact allocated state counts, including every initializer and pool context. |

The dynamic-call contracts allow arbitrary natural target and continuation
values. Generic call reaches the selected entry, without assuming arbitrary
callees terminate. Return-composition theorems state their actual callee or
selected-return premises explicitly. Earlier arithmetic, invalid-address,
lookup and frame contracts are adapted and rechecked in the richer opcode
namespace; their original verified files remain unchanged.

Operational tape hypotheses are canonical finite banks with blank exterior.
The raw push theorem preserves both arbitrary finite bit prefixes. No abstract
natural semantics is claimed for every malformed tape.

## Compiled pool and uniform proof

Each literal contributes the following fragment to one finite compiled pool:

```text
(0, advance), n copies of (1, advance), (0, continuation-address)
```

Fragments are concatenated in instruction order. A literal's entry is the pool
offset of the fragments at earlier instruction sites. Non-literal instructions
contribute no pool cells. The final delimiter carries the compiled continuation;
other cells advance to the next pool cell. There is no free program tape or
unbounded return register.

Every pool cell receives one paid context of 460 old bit controls and 2
head-restoration bridges. Its bit is emitted through the existing proved push
routine, including the full scan and return to home. The closing bridge enters
the actual program continuation; invalid labels select error. Empty pools have
no literal contexts, and out-of-range pool starts select error.

`pool_at` proves the offset/fragment decomposition from the actual instruction
lookup. `emit_prefix` proves traversal for an arbitrary bit prefix by induction.
`push_fragment` handles the final zero and actual continuation. These proofs are
uniform; they do not enumerate n or trust an external trace. The successful
primitive instructions lift through the inherited relabeling proof, while the
extended stopping boundaries are proved separately.

For raw earlier data u and m appended bits:

```text
bitCost(u,m)     = m*(4*length(u)+2*m+8)
literalCost(u,n) = (n+2)*(4*length(u)+2*n+12)
```

Each bit's cost is `4*currentLength+10`: the existing push plus its two real
head-restoration transitions. Repeating one literal k times costs
`bitCost(u,k*(n+2))`, proved by induction with the changing data length.
The repetition count creates no additional controls or preloaded words.

## All state and initialization costs

Let L be program length, P the sum of n+2 over all literal instructions, and D
the encoded length of initial data:

```text
Preserved arithmetic/call/lookup body     10,360 +4,638*L
New startup (enter instruction 0)              2
Literal pool contexts                        462*P
Complete body                           10,362 +4,638*L +462*P
Initializer bits                        2 +2*D
Initializer states and steps            4 +4*D
Complete initialized machine            10,366 +4,638*L +462*P +4*D
```

All unused earlier controls, including the old call boot and per-site
conditional contexts, remain counted. There is no dummy literal context.
Literal magnitudes are paid for through their emitted-bit contexts; static
continuation labels are compiled into finite transition destinations.
Dynamic call operands are actual generated words, handled by the verified
runtime call/lookup/return routines.

The two new startup states enter instruction 0. The reflected FlatInit writer
creates all initial data and markers from the binary zero tape and returns
home before startup. Initial frames are empty; general runtime contracts
separately permit arbitrary existing frames.

For the demonstration:

```text
0: push(3,1)
1: push(4,2)
2: call
3: succ
4: halt
initial data=[n], frames=[]
```

L=5, P=5+6=11 and D=n+2. The complete family therefore has **38,646+4n states**.
For n=3:

```text
33,550 old body +2 startup +11*462 pool =38,634 body
38,634 body +24 initializer             =38,658 states
24 init +2 startup +190 push3 +360 push4
  +716 call +86 successor +698 return   =2,076 transitions
```

Unary literals and repeated scans remain efficiency limitations. The pool
shares the allocation across literals without a maximum-width block at every
program site. This is a counted baseline, not a minimized interpreter or a
program-independent constant-state claim.

## Reproduction and checked evidence

From the repository root:

```sh
python3 -B research/catchup-reuse/literal/verify.py --full
```

All **fourteen strict Lean commands** passed: twelve core modules, Export and
Audit, with warnings as errors and auto-implicit disabled. All **119 new theorem
declarations** pass transitive axiom audit using only `propext`,
`Classical.choice`, `Quot.sound`, or fewer. No verified source uses sorry,
custom axioms, native-only proof computation or the unfinished Catch-Up theorem.

The exact bounded suite passes **16,221 routine cases /52,142,990 successful
routine transitions**, plus eight whole blank-family cases and the sample
initialization/full run. It compares entire tapes, controls and heads, including
literal 0, empty data, literals through 1,024, same-value literals with different
continuations, generated targets/continuations, literal-producing dynamic and
nested callees, and up to 128 repeated pushes. Earlier raw prefixes reach 1,024
bits and natural data/frame prefixes reach 128 words.

All **77,316 sample cells** match separate reconstruction, including **73,946
present and 3,370 missing** transitions. Native fixtures compare **55,432 sites**
across all 800 seven-opcode skeleton/label-profile variants of lengths 0..3 and
six extra programs, including literal 1,024. They exercise both scanned bits at
literal start, write and bridge states, pool-end guards, old dispatch and
conditional branches, and the new startup. Large variable tables are reconstructed
on demand using exact integer state keys; hash equality is never a proof premise.

All **thirteen** deliberate corruptions are rejected: initial write, header,
payload, closing delimiter, early continuation, wrong continuation, wrong head
motion, wrong startup offset, wrong dynamic literal offset, damaged saved frame,
premature return, invalid-address wrap and missing row. Timeouts never count as
mathematical outcomes. No game counterexample or strategic invariant was tested
in this component session.

The numeric table (`machine.txt` in the historical layout) publishes all 38,658 rows, scanned 0 then 1,
using `write L/R next` or `---` per cell. The row-generator equality is proved
using the previous generic kernel theorem, avoiding concrete enumeration in
Lean. Native export/serialization/fixtures remain diagnostic bytes, rather than
a separate numeral-only kernel certificate or theorem premise.

All **nine previous snapshots** and their recorded sources, objects, scripts and
artifacts match, with all pinned backend source/cache checks and 27 baseline
axiom reports intact. The isolated package remains Lean 4.35.0-rc4, compiler
`c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`, Mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`, Cryptids source blobs at
`8fed07fa2981ecd96141303b0d8982116106f6eb`. The original game package remains
Lean 4.27.0 / Mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900`.
Pinned ordinary imported objects retain their usual cache boundary; this is not
a full dependency rebuild or a cross-version theorem.

## Proof size and resources

Final Lean replay took **33.587 seconds**, physical replay **13.458 seconds**.
Peak recorded individual-child high-water RSS was **3,813,212,160 bytes**, on
macOS 26.6.2 arm64 with 16 logical CPUs. Each child has a 120-second wall bound;
Lean has an 8,192-MiB allocator budget, not an OS RSS cap. Lean output is bounded
to 16 MiB, physical output to 1 MiB. These are checking times, excluding interactive
proof/code-generation cost.

The twelve new core sources contain **74,991 bytes /119 theorems**, compiled
objects 5,924,704 bytes. Two auxiliary objects add 460,064 bytes. Helpers and the
plain table total 620,241 bytes; output artifacts/receipts total 2,972,012 bytes.
All new supporting mathematics is recorded, including pool indexing/traversal,
actual call composition and repetition. Existing operational proofs were adapted
to the richer opcode/dispatch target and replayed, with the original modules
preserved and nine predecessor manifests linked. These are upper-bound
artifacts; no state or proof-size minimality claim is made.

Frozen benchmark SHA256:
`c408de965671542daf4fe9853e7656cc313252aeb72002026e16d8e4f6e31500`.
Independent review is recorded in REVIEW.md (`REVIEW.md` in the historical layout).

The fresh independent review **accepted** this component. Fourteen isolated
strict Lean replays produced objects byte-identical to the frozen ones, and all
119 axiom audits passed. A separate numeric implementation matched all 77,316
sample cells and 55,432 fixture cells, passed 10,519 physical cases with
49,531,168 successful transitions, and rejected thirteen deliberately corrupted
variants. It independently checked 63 new records, 382 records in nine earlier
manifests and the dependency pins. Review scripts, receipts, logs and their
hashes are archived in review-evidence (`review-evidence/README.md` in the historical layout). The matching
large export log is shared with artifacts/Export.log; fresh object hashes match
the preserved compiled objects. This review supports the specified component
and retains the dependency-cache and native-serialization boundaries above.

The highest-value next step is a **shared discard-word routine matching the
source language's `.tail`**, including empty data and frame preservation. It
connects this stack-growing instruction set to an actual primitive used by the
existing verified search (`dropCode`/list addressing), before attempting the
complete source simulation. Further data access/copying operations and a full
compiler/simulation remain open obligations.
