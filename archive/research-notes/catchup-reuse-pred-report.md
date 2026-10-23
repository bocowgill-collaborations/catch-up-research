> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Conditional predecessor, zero testing and branch dispatch

Implemented and proved two conditional arithmetic instructions in the smaller
binary-interpreter prototype:

```text
pred(zeroTarget, positiveTarget):
    if n=0: keep0, jump zeroTarget
    else:   replace n by n-1, jump positiveTarget

test(zeroTarget, positiveTarget):
    keep n, jump zeroTarget if n=0, otherwise positiveTarget
```

The decision uses the **original** operand. In particular, predecessor sends
input 1 to the positive branch while producing 0. Both instructions preserve
arbitrary earlier data and frames and restore the physical head before the
selected instruction starts.

The complete binary demonstration is `CatchUp.Machine.Pred.M : Machine 33606 2`:
**33,550 body states plus 56 initialization states**. From an all-zero tape it
creates operand 3, target 0, continuation 4 and all markers; calls predecessor;
tests the resulting 2; returns through its saved continuation; and halts with
data `[2]`, empty frames and head 0 after **1,332 successful transitions**.

This is a richer component baseline, with explicit per-site branch storage.
The complete Catch-Up cryptid remains **388,819,712 states**, with its preserved
`Halts M ↔ ¬C` theorem. C is unresolved. Connection of this new instruction set
to the complete verified search remains unfinished.

## Kernel-checked contracts

The six opcode forms are `halt`, `call`, `ret`, `succ`, `pred z s`, `test z s`.
Theorems quantify over every finite program, all natural operands and addresses,
and arbitrary finite earlier data/frame stacks. No fixed numerical bound appears
in those operational statements.

| Theorem | Exact effect |
| --- | --- |
| `predecessor_bits` | For arbitrary raw prefixes u,v, change `u ++ word(n)` to `u ++ word(n-1)` on the left, preserve v and the head, enter the zero/positive branch selected from n. |
| `zero_test_bits` | Preserve both raw banks including n, restore the head, and enter the zero/positive branch selected from n. |
| `predecessor_nat`, `zero_test_nat` | The corresponding contracts for arbitrary earlier natural data words and frames. |
| `lookup_correct`, `entry_saturated` | Consume the complete runtime PC, select the actual six-opcode entry, retain a conditional's instruction site, and route every out-of-range address to the error control. |
| `branch_pred`, `branch_test` | Branch from the retained site to that instruction's own labels. This is uniform over both natural labels, including invalid ones. |
| `call_predecessor_branch`, `call_zero_test_branch` | Save the whole caller continuation, consume both call operands, execute the selected conditional and enter its selected branch with the saved continuation still present. |
| `call_predecessor_return`, `call_zero_test_return` | If the selected branch is `ret`, execute its real return and dispatch the saved continuation, preserving the arithmetic result and every earlier frame. |
| `nested_predecessor` | Execute an outer call to call, inner predecessor call, selected return, inner return to ret, then outer return; preserve arbitrary earlier data/frames. All selected opcode hypotheses are explicit. |
| `predecessor_invalid_branch`, `test_invalid_branch` | An out-of-range selected label reaches the distinct terminal error control, with the proved result data and unchanged frames. |
| `successor_nat`, `call_successor_return` | The existing successor and its calling convention remain correct in the extended machine. |
| `predecessor_full`, `zero_test_full` | The contracts hold in the complete initialized machine family for arbitrary runtime data/frames. |
| `blank_run`, `blank_terminal`, `blank_halts` | For every n, the demonstration initializes from blank, computes n-1 with saturation at0, returns and halts. |
| `state_count`, `family_count`, `M_count` | Exact allocated control counts, including all initialization. |

A branch reaches its instruction entry; arbitrary branch programs are not assumed
to return or terminate. General `call_callee_return` composes only an actual
finite callee run with the saved frame intact. The immediate-return and nested
contracts supply proved runs under the listed branch/return hypotheses.

The tape hypotheses are canonical finite banks with blank exterior, using the
preserved marker/data layout. They do not give natural-number meaning to all
malformed tapes. Closing-one errors are proved for both instructions;
empty-operand underflow is also checked diagnostically.

## Arithmetic mechanism and exact costs

Naturals remain unary self-delimiting words `word(n)=0 1^n 0`, width n+2.
Data grows left, frames right; lists are bottom first. Both routines pop the
closing zero, then inspect the next bit by a second pop.

- At zero, that second bit is the opening zero. Both zeros are restored before
  selecting the zero branch.
- At a positive predecessor, the second bit is one. Replacing it with a closing
  zero removes exactly one payload one.
- At a positive zero test, both popped bits are restored as one then zero.

Every pop/push invokes the existing proved bit operation and its paid two-step
head-restoration bridge. If u is the earlier raw data prefix:

```text
predCost(u,0)   =16*length(u)+56
predCost(u,n>0) =12*(length(u)+n)+42
testCost(u,n)   =16*(length(u)+n)+56
```

These costs include all bit operations and head restoration, through the actual
branch entry. The natural-stack contracts use u=`encode data`. Call/return use
the preserved transfer and lookup costs; return uses the updated data length.

## Reuse and paid branch information

The existing Separate, Words, Dispatch, Call and Succ modules, objects and
artifacts are byte-preserved. Successful primitive runs lift through one proved
relabeling lemma; the newly extended missing boundaries are proved separately.
The inherited closed `afterReturn`/right-source invariants justify exactly the
word push/return runs reused here. No unrestricted equivalence across changed
lookup handoffs is assumed.

The old successor/call body is retained. Its completed-PC lookup bounces now
select the actual six-opcode program. A lowering maps new conditional opcodes to
old halt only for allocation/body reuse. It is not used as the actual dispatch
answer. `entry_saturated` handles the new detail that a conditional must retain
its original site as well as its opcode.

Each instruction site gets nine contexts of 460 bit controls plus 2 bridge
controls, retaining the conditional's site until its branch is selected. The
two natural labels in a conditional are **compiled into explicit transition
destinations**. They are not runtime words supplied on a free program tape.
The table generator resolves each label to the corresponding compiled entry,
or the error control if invalid. The source semantics of those jumps is proved
for arbitrary labels. All per-site storage is counted, including nonconditional
sites and one dummy site. This simple baseline deliberately allocates unused
controls; no minimization claim is made.

For program length L and initial encoded data length D:

```text
Preserved successor/call/lookup body        6,202 +480*L
Conditional contexts                       (L+1)*9*(460+2)
                                          =4,158*(L+1)
Complete body                              10,360 +4,638*L
Initializer bits                           2 +2*D
Initializer states and successful steps     4 +4*D
Complete initialized machine               10,364 +4,638*L +4*D
```

Every allocated parameter combination and terminal control is included.
The increase over the earlier two-instruction successor demonstration reflects
a larger program and the added per-site conditional baseline. It does not
represent a reduction in the current complete Catch-Up cryptid.

Initialization reuses the proved reflection of FlatInit: emit all input words
and markers leftward from blank tape, return home and enter the ordinary body.
Initial frames are empty. Operational contracts separately allow arbitrary
existing frames. No initial data, return address, marker or program oracle is
supplied without its control or writer cost.

## Complete blank-tape family

The demonstration program and input are

```text
0: pred(1,2)
1: ret
2: test(1,3)
3: ret
4: halt
input data=[n,0,4], frames=[]
```

Zero returns from instruction 1. Positive inputs decrement and enter instruction 2;
its zero branch returns from 1 and its positive branch returns from 3. Thus n=0,
n=1 and n≥2 exercise the three distinct reachable paths. Lean proves the whole
family, including termination, with output `[n-1]` and empty frames.

Here L=5, D=n+10, hence **33,594+4n states**. At n=3:

```text
33,550 body +56 initialization                         =33,606 states
56 initialization +2 boot +506 call +78 predecessor
  +88 test +602 return                                =1,332 steps
```

The published table has **67,212 cells** (33,606 rows, scanned 0 then 1):
64,282 present and 2,930 missing transitions. `table_cells` and `table_correct`
prove the generated rows reconstruct M. The plain numeric serialization is
machine.txt (`machine.txt` in the historical layout), using `write L/R next` or `---` per cell.

A naive proof that simplified the concrete `finRange 33606` encountered the
existing recursion bound. Two generic row-reconstruction lemmas, proved for a
variable machine size and then instantiated, avoid that enumeration. The final
build needs no increase to the existing recursion or memory budgets. This is a
uniform proof of the row generator, not native computation treated as a proof
or a separate numeral-only certificate for the exported bytes.

## Reproduction, exact tests and trust boundary

From the repository root:

```sh
python3 -B research/catchup-reuse/pred/verify.py --full
```

All **eleven strict Lean commands** passed: nine core modules, Export and Audit,
with warnings as errors and auto-implicit disabled. All **101 new theorem
declarations** pass transitive axiom audit with only `propext`, `Classical.choice`,
`Quot.sound`, or fewer. No new verified source uses sorry, custom axioms,
native-only proof computation or the unfinished Catch-Up theorem.

All **37,580** finite cases passed, with **58,409,552 successful routine
transitions** recorded separately from demonstration initialization. The suite
compares whole tapes, controls and head positions. It checks both arithmetic
branches, input 1's positive predecessor path, non-destructive zero testing,
six opcode forms, invalid dynamic/compiled addresses, distinct conditional
sites, selected returns, changed-data nested calls and the blank family.
Operands/dynamic addresses reach 1,024, compiled labels reach 1,027, raw prefixes
reach 1,024 bits and earlier natural data/frame depths reach 128.

All 67,212 sample cells match separate reconstruction. Native fixtures compare
**144,320 sites across 3,110 program variants**: every six-opcode skeleton of
length 0..4 with two label profiles, covering valid, out-of-range and large labels.
These compare actual dispatch entries and both scanned symbols at conditional
branch bridges, including dummy sites. Variable-program traces use reconstructed
tables whose changed sites are checked against those fixtures. Universal
correctness comes from Lean, not extrapolation from these tests.

All **twelve** deliberate corruptions are rejected: initial write, zero routed
positive, input 1 routed zero, predecessor failing to decrement, zero test
changing data, lost zero delimiter, incorrect head restoration, old immediate
return restored, saved payload damaged, wrong conditional site's positive
label, invalid continuation wrapped into the program, and missing row.
Four malformed/underflow diagnostics also pass. Timeouts never count as game
or machine outcomes. The input 1 corruption is a diagnostic counterexample to
testing zero after decrement; it is not a game counterexample.

The native export bytes and variable-program fixtures remain diagnostics,
not theorem premises. No separate numeral-only Lean certificate of their
serialization is claimed. Pinned imported Lean/Mathlib/backend objects retain
their ordinary cache boundary; this replay is not a full dependency rebuild
or a cross-version proof.

All **eight** previous snapshots and their recorded sources, objects, helpers
and artifacts match, with baseline source/cache pins and 27 axiom reports intact.
The isolated toolchain stays Lean 4.35.0-rc4, compiler
`c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`, Mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`, and Cryptids dependency source blobs
at `8fed07fa2981ecd96141303b0d8982116106f6eb`. The original game package stays
Lean 4.27.0 / Mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900`.

Fresh independent review accepted this component after eleven isolated strict
replays, all 101 axiom audits and frozen-record/pin checks. A separately authored
binary model matched every sample cell, all 144,320 fixture cells and 8,622
foundational bit/word cells. It passed **20,332 further physical cases /46,686,970
successful transitions**, including operand 4,096, a 1,077-bit raw prefix, 128
earlier data words, 64 earlier frames, nested predecessor and test calls, and
both general initialization and whole blank-family runs. Eight independent
corruptions were rejected. See REVIEW.md (`REVIEW.md` in the historical layout) and the retained
review evidence (`review-evidence/README.md` in the historical layout). This is model criticism and
independent diagnostic evidence alongside Lean verification, not human approval
or a proof about the complete Catch-Up source.

## Proof and checking costs

Final strict Lean checking took **24.995 seconds**, bounded physical checking
**9.212 seconds**. Peak recorded individual-child high-water RSS was
**3,851,829,248 bytes** on macOS 26.6.2 arm64 with 16 logical CPUs. Each child has
a 120-second wall bound; Lean has an 8,192-MiB allocator budget, not an OS RSS cap.
Lean output is bounded to 16 MiB and physical output to 1 MiB. These checking times
exclude interactive proof-generation/development cost; no search-time minimality
claim is made.

Nine formal sources contain **58,890 bytes /101 theorems**, with 4,520,960 compiled
bytes. Two auxiliary objects add 351,960 bytes. Helpers and the plain table total
538,565 bytes; output artifacts/receipts total 5,517,318 bytes. All newly introduced
supporting mathematics, including primitive relabeling, site saturation and generic
row reconstruction, is recorded. Eight predecessor manifests link the inherited
support. These are retained upper-bound artifacts, not state/proof-size lower
bounds; no large proof is hidden behind a one-line invocation.

Frozen benchmark SHA256:
`1c499c3d3bd04efc8bfd0b03043de146ddf54f66efffe37a1978bfd5e0d10f96`.
Fresh independent review is recorded in REVIEW.md (`REVIEW.md` in the historical layout).

No game counterexample or new theorem about C was found in this component
session. The highest-value next primitive is **literal push**, so a running
program can construct new call operands and grow its working data rather than
consume only the initially supplied words. Its paid word-generation control,
frame preservation and connection to dynamic calls should be proved before
attempting the complete source-to-interpreter simulation.
