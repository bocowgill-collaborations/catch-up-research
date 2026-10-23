> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Shared discard and the source `.tail` contract

Added `.tail` to the counted binary interpreter. Every instruction site uses
the same two-stage discard callee. It removes one whole natural word, succeeds
on empty input, restores the head to home and enters the real return routine.
Lean proves this for every natural, program length and earlier data/frame bank.

The complete blank-tape demonstration is
`CatchUp.Machine.Tail.M : Machine 39608 2`: **39,560 body states plus 48
initialization states**. It initializes source input `[3,0,2]`, generates its
call target and continuation during execution, calls `.tail`, returns and halts
with source output `[0,2]` and no saved frames after **2,772 transitions**.
The empty-input demonstration has **39,564 states** and halts after **1,250
transitions**, returning `[]`.

This completes a source-primitive contract and another smaller-interpreter
component. It does not complete the new search-source simulation. The full
Catch-Up cryptid remains **388,819,712 states**, with its preserved
`Halts M ↔ ¬C` theorem; C remains unresolved. No game outcome or strategy was
tested or proved in this session.

## Exact source and tape semantics

Physical data is a bottom-first list of framed unary naturals,
`word(n)=0 1^n 0`, encoded as marker/data pairs. Source head must be physical
stack top, so the explicit representation is:

```text
sourceBanks(source,frames) = natBanks(reverse(source),frames)
```

`source_banks_injective` proves this representation is injective in both lists.
Frames retain the earlier bottom-first convention. Reversing the source list
does not reverse, remove or reinterpret saved continuations.

`tail_source_correct` states the literal pinned Mathlib source semantics
`Turing.ToPartrec.Code.tail.eval source = pure source.tail`, together with the
actual binary run producing `sourceBanks(source.tail,frames)`. Its quantifiers
cover every source list and frame list, including empty lists and zero-valued
heads. It is a primitive compiler contract, not an assumed whole-source compiler.
The source `Code.tail` definition is unchanged.

| Theorem | Kernel-checked effect |
| --- | --- |
| `discard_bits` | Remove an entire natural word of any size, preserving arbitrary earlier raw data u and opposite raw bank v, and restore home. |
| `discard_empty_bits` | Empty initial data succeeds in eight transitions with the entire opposite bank preserved. |
| `discard_nat`, `discard_empty_nat` | Actual `.tail` instruction lookup starts the shared callee, preserving all earlier natural data and saved frames. |
| `malformed_tail_closer`, `missing_tail_opener` | A closing one or exhausted mid-word input reaches the distinct error control. |
| `tail_source`, `tail_source_correct` | The actual output is source `.tail` under the injective reversal representation, including empty input. |
| `call_tail_return` | Actual dynamic call, shared tail and return consume the saved continuation and preserve every earlier frame. |
| `generated_tail_return` | Two executed literals generate both call operands; actual target lookup reaches the shared tail and real return reaches the continuation. |
| `repeated_source_tail` | One fixed program performs any finite number k of calls, giving `source.drop k` and unchanged earlier frames, including k beyond source length. |
| `tail_source_full` | The arbitrary source/frame contract survives the complete initialized machine embedding. |
| `blank_run`, `blank_halts`, `blank_source_correct` | Every finite source list is initialized from binary blank tape, evaluated by the actual generated-call program and returned as source.tail at a terminal control. |
| `blank_repeated_source` | One fixed initialized program reaches `source.drop k` for every source and finite k; no control depends on k. |
| `state_count`, `family_count`, `M_count` | Exact allocated counts include every body, pool, startup and initialization control. |

The raw contracts assume canonical finite banks with blank exterior and one
well-framed natural at the top when nonempty. They permit arbitrary earlier
raw prefixes and arbitrary opposite raw bits. No universal interpretation of
all malformed tapes is claimed. The explicit malformed cases above strengthen
the diagnostic boundary without replacing that hypothesis.

## Mechanism, sharing and costs

Two contexts reuse the existing proved bit-pop routine. The first removes and
checks the closing zero; the second pops payload ones until the opening zero.
Each context has 460 old controls, two successful-pop restoration bridges and
one empty-pop restoration bridge: **463 controls per stage, 926 total**.
The shared controls have no instruction-site argument. All `.tail` entries are
definitionally the same `tailStart`; no routine is replicated at its call sites.

An initial empty pop returns successfully. A mid-word empty pop instead selects
error. The separate empty bridges preserve this distinction. Restoration bridges
perform two real transitions and return home before the next action.

Successful primitive runs lift using the existing `primitive_run` proof; new
stopping boundaries are proved explicitly. `discard_ones` proves the variable
payload loop by induction, and `discard_bits` joins closing/payload/opening
removal. The complete nonempty cost is:

```text
discardCost(u,n) = (n+2)*(4*length(u)+2*n+16)
emptyCost       = 8
```

Every bit removal pays its scan of the current bank and restoration to home.
Repeated-call cost is an explicit recursive sum, with source tail updated on
each iteration. The routine has fixed control for unbounded runtime naturals;
its repeated scans are a time-efficiency limitation.

Let L be program length, P the sum of n+2 over literal instructions, and D the
encoded initial-data length:

```text
Preserved arithmetic/call/lookup body     10,360 +4,638*L
Startup                                      2
Literal pool contexts                        462*P
Shared discard contexts                      926
Complete body                           11,288 +4,638*L +462*P
Initializer bits                        2 +2*D
Initializer states and steps            4 +4*D
Complete initialized machine            11,292 +4,638*L +462*P +4*D
```

All inherited unused controls, per-site conditional copies and literal pool
contexts remain counted. The 926 shared controls are counted even if a program
has no `.tail` instruction. Static code/literals live in the counted finite
transition table. No program or call operand is supplied on a free tape.

The example program is `[push(3,1),push(4,2),call,tail,halt]`. Its fixed body has
L=5, P=11 and 39,560 controls. Only `source.reverse` is initialized; both dynamic
call operands are created afterward. Thus its full family count is
`39,564 +4*length(encode(source.reverse))`. For source `[3,0,2]`, D=11:

```text
39,560 body +48 initialization =39,608 states
48 initialization +2 startup +310 push3 +504 push4
  +980 call +230 tail +698 return =2,772 transitions
```

The reflected FlatInit writer emits all data and markers from the two-way
infinite binary zero tape and restores home. General runtime theorems allow
arbitrary existing frames; all blank initializations start with empty frames.

## Reproduction, assurance and experimental evidence

From the repository root:

```sh
python3 -B research/catchup-reuse/tail/verify.py --full
```

The strict target has fourteen core modules, Export and Audit, with warnings
as errors and auto-implicit disabled. Its **142 new-namespace theorem
declarations** include adapted earlier operational proofs replayed against the
eight-opcode dispatcher. All transitive axiom reports permit only `propext`,
`Classical.choice`, `Quot.sound`, or fewer. Verified source has no sorry,
custom axiom, unsafe definition, native-only proof computation or dependence on
the unfinished conjecture theorem. Original component files are preserved.

The exact bounded diagnostic suite passes **17,299 routine cases /42,775,708
successful transitions**, plus eleven whole blank-family/repetition cases and
the complete sample run. It checks entire tapes, heads and controls. Coverage
includes every pair of raw prefixes through length three with naturals 0..31,
empty data, all source lists on 0..2 through length four with frame lists
through length two, nonzero `.tail` instruction sites, generated call operands,
nested returns, invalid labels and repetition beyond source length. Additional
cases reach natural/address 1,024, 1,024 raw prefix bits, 129 natural data words,
128 saved frames and 128 repeated calls.

All **79,216 sample cells** match separate numeric reconstruction: 75,846
present and 3,370 missing transitions. Native fixtures compare **119,164 sites**
across all 1,170 eight-opcode/program-profile variants of lengths 0..3 and nine
larger programs. Both scanned symbols are covered at discard starts, stops,
empty boundaries and bridges, literal contexts, old/new dispatcher entries and
conditional branches. Large variable tables use exact integer dictionary keys;
hash equality is never a proof premise.

All **seventeen** deliberate corruptions are rejected, covering initialization,
tail dispatch, premature word termination, wrong head restoration, incomplete
erasure, empty/underflow confusion, malformed closers, literal creation,
continuations, return storage, premature return and missing rows. These tests
are computational evidence about the exact finite cases, separate from the
universal Lean contracts.

machine.txt (`machine.txt` in the historical layout) serializes every finite row, scanned zero then one,
with `write L/R next` or `---`. The kernel proves equality for the row generator
using the earlier generic table theorems. Native export and serialized bytes
are independently reconstructed diagnostics; no numeral-only kernel certificate
of the serialization is asserted.

All ten previous benchmark snapshots and their recorded sources, objects,
scripts and artifacts are preserved, including the complete Catch-Up baseline.
Toolchains stay pinned: isolated Lean 4.35.0-rc4, compiler
`c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`, Mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`, Cryptids source blobs at
`8fed07fa2981ecd96141303b0d8982116106f6eb`; original game package Lean 4.27.0 /
Mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900`. Ordinary imported objects
retain their pinned dependency-cache boundary; this is not a full dependency
rebuild or cross-version theorem.

Final Lean replay took **42.500 seconds**, physical replay **14.714 seconds**.
Peak recorded individual-child high-water RSS was **3,858,841,600 bytes**, on
macOS 26.6.2 arm64 with sixteen logical CPUs. The fourteen core sources contain
**88,581 bytes /142 theorem declarations**, compiled objects 7,195,160 bytes.
Two auxiliary objects add 538,432 bytes. Helpers and table total 635,636 bytes;
output artifacts/receipts total 5,165,255 bytes. This counts all new-namespace
supporting mathematics, including adapted proofs and source representation,
discard induction, actual calls and repeated source tails. Existing original
operational sources are preserved, with ten predecessor manifests linked.

The frozen benchmark SHA256 is
`bbbc25d2dc3418f9ed9355309d1bed4d1ff8a76c65132a880976dac74ba8dc06`.
Complete supporting proof sizes and hashes are recorded in benchmark.checked.json.
Each child has a 120-second wall bound,
Lean an 8,192-MiB allocator budget, and output limits of 16 MiB for Lean /1 MiB
for the physical checker. The allocator budget is not an OS RSS cap. Checking
cost is separate from interactive proof/code generation, and no state/proof-size
minimality is claimed.

Fresh independent review **accepted** this component. All sixteen isolated
strict Lean objects match the frozen object bytes, and all 142 axiom reports
pass. Its separate implementation reconstructed all 79,216 sample cells,
119,164 fixture sites and exact serialized table, passed **5,828 physical cases
/38,773,776 transitions**, and rejected seventeen independent corruptions.
All 71 new records, 445 records in ten earlier manifests, ten snapshot hashes
and pins were rechecked. REVIEW.md (`REVIEW.md` in the historical layout) records the scope and verdict;
scripts, receipts, logs and hashes are archived in
review-evidence (`review-evidence/README.md` in the historical layout). The byte-identical large export is
shared at artifacts/Export.log, and fresh object hashes match preserved objects.
Model review is independent criticism; the universal conclusions remain the
encoded Lean statements, with the dependency-cache and serialization boundaries
stated above.

The highest-value next step is a **source `.case` contract including empty
input**, combining the existing predecessor/zero-test branching with `.tail`.
The verified search uses this source operation for its actual branches. Closing
its representation and empty-input obligations would advance source compilation;
general composition, list construction/copying and fixpoint simulation remain
separate obligations. No smaller complete Catch-Up state count is claimed here.
