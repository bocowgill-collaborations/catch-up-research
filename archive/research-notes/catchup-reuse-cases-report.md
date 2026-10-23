> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Source `.case`, both branches and empty input

The binary interpreter now implements the literal pinned source `Code.case`
argument transformation and branch selection for every source list:

| Input | Selected computation | Argument |
| --- | --- | --- |
| `[]` | f | `[]` |
| `0 :: rest` | f | rest |
| `(n+1) :: rest` | g | `n :: rest` |

All frames survive dispatch and the head returns home. The positive arm remains
positive when the original head is one, even though its transformed head is
zero. Empty input does not manufacture a word.

The complete initialized example is `CatchUp.Machine.Cases.M : Machine 62780 2`:
**62,732 body states plus 48 initialization states**, from binary blank tape.
It implements source `Code.case .zero' (.comp .zero' .zero')`, mapping
`[3,0,2]` to `[0,0,2,0,2]` in **5,268 transitions**, with empty frames and head
home at halt. The zero example `[0,0,2] → [0,0,2]` takes **4,194 transitions**;
the empty example `[] → [0]` takes **2,602 transitions**.

`.case` adds **zero controls** for a fixed program length, literal pool and
initial data. It reuses predecessor controls and an existing restoration bridge.
The larger demonstration contains more instructions and literals for its two
branch bodies, all included in the count.

This is a source-constructor contract and executable example. Complete new
source compilation and reverse whole-source halting simulation remain missing.
The full Catch-Up cryptid stays **388,819,712 states**, with its preserved
`Halts M ↔ ¬C` theorem. C remains unresolved; no game outcome, strategy or
counterexample was tested in this session.

## Exact contract and partial branch programs

The existing injective representation is unchanged:
`sourceBanks(source,frames) = natBanks(source.reverse,frames)`. Source head is
physical stack top; the established frame order stays unchanged.

`case_source_eval` proves the exact source equation for arbitrary partial
branch codes f and g. `case_source_correct` pairs it with actual binary dispatch
to the selected label and transformed argument, preserving arbitrary frames.
It does not assume that arbitrary labels contain correct compiled code.

`case_compose` is the constructor rule: a result witness for the selected
partial source computation, together with an actual finite callee run returning
that result with the same frames, gives source membership for `Code.case f g`
and the combined binary run. **The unselected branch has no termination or
execution premise.** The selected callee witness is explicit, not an oracle or
compiler axiom. This is not a whole-source reverse-halting theorem.

`case_call_return` composes incoming call, dispatch, selected callee and real
return. `generated_case_return` first creates the entire target and continuation
words by executing two literals. The three immediate-return corollaries cover
empty, zero and successor input with no premise about the unselected label,
including invalid labels. Earlier frames are preserved; the actual saved
continuation is consumed by its corresponding return.

| Theorem | Kernel-checked effect |
| --- | --- |
| `case_empty_bits` | Eight transitions select zero on empty data, preserving arbitrary opposite raw bits. |
| `case_zero_bits` | Consume word(0) and select zero, preserving arbitrary earlier raw data and the opposite bank. |
| `case_positive_bits` | Replace word(n+1) by word(n) and select positive, for every n and both arbitrary raw prefixes. |
| `case_source`, `case_source_correct` | Literal source argument/branch behavior for all source/frame lists and labels. |
| `case_compose` | Selected partial source/callee witnesses give the composed constructor result. |
| `case_call_return`, `generated_case_return` | Actual calls, generated operands and return with arbitrary earlier frames. |
| `case_return_empty`, `case_return_zero`, `case_return_positive` | Closed immediate-return instances without an unselected-label premise. |
| `case_invalid_branch` | Invalid selected label reaches error with the correct argument and frames. |
| `case_bad_closer`, `case_payload_underflow`, `ordinary_empty_boundary` | Explicit malformed/underflow behavior and confinement of the empty patch. |
| `example_constructor`, `program_run` | Concrete branch bodies supply the witnesses and preserve arbitrary existing frames. |
| `blank_source_correct`, `blank_run`, `blank_halts` | Every source list is initialized from blank and evaluated by the complete concrete source-case program. |
| `state_count`, `family_count`, `M_count` | Exact allocated counts including initialization. |

## Reused control and costs

`caseOf(z,s)` starts in the existing predecessor context at its actual program
site. After checking and removing the closing zero, a second zero is removed
and the existing stage-one zero bridge directly enters z. A second one uses
the existing predecessor path to restore the closing zero and enter s.
Initial empty data uses that same zero bridge directly.

The empty extension is guarded by the actual instruction lookup and stage.
Other instructions retain their old underflow behavior. In the new namespace,
ordinary zero helpers explicitly require a non-case site: predecessor/test
restore word(0), while source case removes it. Their headline contracts still
hold and are rechecked. Original earlier component files remain unchanged.
Successful primitive runs reuse the existing lifting proof; changed stopping
boundaries are proved separately. `Instruction.lower` selects allocation only,
not a semantic lowering of the richer instructions.

Raw proofs use canonical finite banks with blank exterior and a well-framed
top natural when nonempty. Earlier raw prefixes and opposite raw bits are
arbitrary. No interpretation of every malformed tape is claimed. Existing
shared-tail proofs remain valid. With A=length(encode(reverse(rest))):

```text
[]              8 transitions
0::rest         8*A +32
(n+1)::rest     12*(A+n+1) +42
```

The zero cost is exactly two pops, each including restoration of the head to
home. The positive cost is the existing predecessor cost. No native computation
or search answer is a premise.

## Count and complete blank initialization

L is program length, P is the sum of n+2 over literal instructions, and D is
the initial encoded-data length:

```text
Preserved arithmetic/call/lookup body     10,360 +4,638*L
Startup                                      2
Literal pool                                462*P
Preserved shared tail                         926
Extra case controls                           0
Complete body                           11,288 +4,638*L +462*P
Initializer bits                        2 +2*D
Initializer states and transitions      4 +4*D
Complete initialized machine            11,292 +4,638*L +462*P +4*D
```

Every inherited per-site context, unused control, tail control, literal context,
startup and writer/restoration state is counted. The program is:

```text
0 push(3,1)       3 caseOf(4,5)      6 push(0,7)
1 push(8,2)       4 push(0,7)        7 ret
2 call            5 push(0,6)        8 halt
```

Only `source.reverse` is initialized, with no frames. Both call operands are
created during execution. The zero branch executes one push zero; positive
executes two. They share actual return. L=9, P=21 give 62,732 body states and
full family `62,736 +4*length(encode(source.reverse))`.
The proved reflected FlatInit writer emits all data/markers from binary zero
tape and restores home. There is no free program tape or initialized call operand.

```text
[3,0,2]: D=11, 48 init, 62,780 total states
48 init +2 boot +310 push3 +920 push8 +1572 call
  +150 case +224 positive branch +2042 return =5268 transitions

[0,0,2]: D=8, 36 init, 62,768 states, 4194 transitions
[]:      D=0,  4 init, 62,736 states, 2602 transitions
```

These are counted baselines, not minimized machines or smaller complete Catch-Up
cryptids. Repeated scans and unused per-site controls remain limitations.

## Reproduction and checked evidence

From the repository root:

```sh
python3 -B research/catchup-reuse/cases/verify.py --full
```

All **seventeen strict Lean commands** pass: fifteen core modules, Export and
Audit, warnings as errors, auto-implicit disabled. All **163 new-namespace
theorem declarations** pass transitive audit with only `propext`,
`Classical.choice`, `Quot.sound`, or fewer. This includes adapted earlier
operational proofs and all new supporting case/call/source proofs. There is no
sorry, custom axiom, unsafe definition, native-only proof computation or
dependency on the unfinished Catch-Up theorem in the verified target.

Bounded exact diagnostics pass **16,458 routine cases /23,195,974 transitions**,
plus nine blank-family cases and the complete sample. Entire tapes, heads and
controls are compared. Coverage includes raw prefix pairs through length three
and heads0..31; all source lists on0..2 through length four and frame lists on0..2
through length two; empty/zero/one distinctions; nonzero case sites; generated
calls; nested returns; invalid selected labels; immediate-return calls with an
invalid unselected branch; and ordinary predecessor/test regressions. Additional
cases reach natural/runtime PC1,024, raw prefixes1,024 bits, source length129 and
128 earlier frames.

All **125,560 sample cells** match reconstruction: 120,230 present and 5,330
missing. Native fixtures match **212,722 sites** over all **1,640** nine-opcode
profiles through length three and fourteen larger programs, both scanned bits
at guarded empty/underflow, zero/positive bridges, entries, tail, literals,
dispatch and conditional boundaries. All **twenty** corruptions are rejected,
including keeping the zero, branching after decrementing one, fabricating zero
on empty input, bad erasure, wrong motion/labels, leaking the empty guard,
invalid underflow success, broken literals/frame storage/return and missing rows.
Timeouts never count as outcomes.

machine.txt (`machine.txt` in the historical layout) lists zero-based rows, scanned zero then one, with
`write L/R next` or `---`. The kernel proves row-generator equality using the
prior generic table theorem. Native export, serialization and reconstruction
are diagnostics, not a numeral-only kernel certificate of those bytes. Lazy
numeric tables use exact integer keys; no hash match is a proof premise.

All eleven prior snapshots and their recorded artifacts match, along with
baseline pins/audits. Versions stay isolated Lean4.35.0-rc4, compiler
`c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`, Mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`, Cryptids source blobs
`8fed07fa2981ecd96141303b0d8982116106f6eb`; original game Lean4.27.0 / Mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900`. Ordinary pinned imported objects
were reused, not fully rebuilt. No cross-version theorem or upgrade is asserted.

Final Lean replay **50.332s**, physical replay **22.476s**; peak recorded child
RSS **3,929,964,544 bytes**, macOS26.6.2 arm64, sixteen logical CPUs. Bounds are
120s/child, Lean-M8192 allocator, 16MiB Lean /1MiB physical output. Allocator
budget is not an OS RSS cap. Interactive proof/code-generation cost was not
instrumented and is excluded from these checking times.
Fifteen core sources total **104,129 bytes /163 declarations**, compiled
8,147,568 bytes; two auxiliary objects592,304 bytes; helpers/table1,001,941 bytes;
artifacts8,901,950 bytes. All new support and eleven predecessor manifests are
recorded, without state/proof-size minimality claims.

Frozen benchmark:
`319eeca9c94ae4d2373e7b06b6f446a7ea21719af228b4323d7c86b4fff3f5be`.
Independent review **accepted** this source-constructor/component milestone.
REVIEW.md (`REVIEW.md` in the historical layout) records seventeen fresh, byte-identical compiled objects
and logs, 163 standard-axiom audits, all 75 new manifest records and 516 earlier
records across eleven preserved snapshots. Its separate numeric reconstruction
checks every sample table cell and all 212,722 fixture sites; **7,314 full-tape
cases /28,058,980 transitions** pass, and **22 independent corruptions** are
rejected. The referee found no proof or machine defect. One wording ambiguity
about restoring the head, rather than the discarded zero word, was corrected.
The referee's initial hand-entered expected subtotal was also corrected; its
failed diagnostic log is retained as a review-check error, not a candidate defect.
Scripts, receipts and logs are archived in review-evidence (`review-evidence/README.md` in the historical layout).
The original reviewed report hash and final closure documents are separately
recorded in finalization.json (`finalization.json` in the historical layout); the benchmark is unchanged.

Next is the source **`.comp` contract**, using existing dynamic calls and
generated continuations to run g then f on its result, with no new primitive
opcode. Input preservation for `.cons`, source successor projection and full
fixpoint simulation remain further obligations for the complete search compiler.
