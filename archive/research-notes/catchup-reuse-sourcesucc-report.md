> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# sourceSuccBody and the final added bank site

The frozen 8,643-state source-successor input routine now has a Lean contract,
including empty input, physical tail clearing and arbitrary caller bit frames.
Its single actual relocation is proved in the candidate body and initialized M,
including the paid entry bridge and exact continuation.

The body normalizes input for successor; the arithmetic increment is a separate
shared core instruction. In the existing bottom-first bank convention:

```
data (encode input), frames F
  --> data (word input.getLastI), frames F
```

For empty input, getLastI is zero. Both zero delimiter bits are created by real
pushes onto data. For nonempty input, the actual capture routine moves the top
word above the frames, clears all earlier data, then moves the retained word
back onto the empty data bank. All caller bits and the original head position
are preserved exactly. No length, value, return-address or caller-depth bound
is imposed. A stronger nonempty theorem allows arbitrary earlier bit data,
provided the final natural word is complete.

`SourceSucc/Contract.lean` provides source_succ_empty_bits,
source_succ_nonempty_bits, source_succ_bits and source_succ_correct. The proof
reuses word transfer, the first-left-return invariant, shared bit push, and
the clearing cursor geometry. The scan/erase induction is instantiated against
this body's actual rows. No general replacement machine is introduced.

`SourceSucc/Relocation.lean` provides all_source_succs_bits/all_source_succs,
both initialized contracts, direct program_source_succ coverage, and the concrete
actual_source_successor endpoint. It starts at the actual projected entry,
executes the paid bridge and copied body, then resumes the real continuation.
The kernel checks exactly one site, **PC9 to PC6**. PC6 is proved to contain
`.core .succ`. This identifies the handoff; executing that core operation in
the patched interpreter remains a separate integration obligation.

All four added bank routines now have verified contracts and relocations:
92 save, 92 switch, 92 finish and one source-successor site, totaling 277.
That completes the added bank-routine layer. It does not by itself establish
whole-program source/binary equivalence or the frame invariants at all callers.

## Reproduce and assurance

From the repository root:

```sh
python3 -B research/catchup-reuse/sourceSucc/verify.py --full
```

The isolated strict runner uses Lean 4.35.0-rc4, compiler commit
`c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`; Mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`; Cryptids sources
`8fed07fa2981ecd96141303b0d8982116106f6eb`. The original game package remains
on Lean 4.27.0/Mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900`.
Pinned ordinary dependency objects are reused, not all rebuilt.

Seven new modules contain 56 new supporting theorems. All 56 and 8 reused endpoints
are audited, with only `propext`, `Classical.choice`, `Quot.sound`. No unfinished
proof, custom axiom, external solver assertion, native-only proof or circular
conjecture dependency is accepted. New receipts bind source hashes. All 20 prior
snapshots and 870 source/object/artifact records are preserved byte for byte.

The complete native transition export queries all 8,643 local controls for both
symbols in the actual candidate body and initialized M, plus hook and bridge.
Every queried cell is compared with the frozen local table and relocation.
All diagnostic executions then use exported M cells at every step, without a
fallback transition oracle. This is a finite exported table for the actual
routine, not execution of the uncompiled source program. The export is still
experimental evidence, not a premise of the kernel proofs. Complete tape, head
origin and exact continuation are checked. Tests cover empty input, nonempty
zero words, multiple-word inputs, arbitrary bit frames, arbitrary earlier
bit prefixes and larger widths/depths. Ten corruptions are tested for rejection.

Limits: 120 seconds/child, Lean -M8192 allocator/16 MiB output; physical 1 MiB output,
50 million steps per positive case and 100,000 per corrupted case. Exhaustion is
an error. The allocator bound is not an OS RSS cap. Recorded timings are for
successful checking, separate from uninstrumented interactive proof-generation
and failed-attempt cost. SELF_AUDIT.md records the implementing agent's hostile
second pass; independent review remains recommended before final publication.

## Remaining before certifying the smaller cryptid

The certified machine remains **388,819,712 states**, with its existing
`Halts(M) ↔ ¬C` theorem. The candidate remains **211,100,482 kernel-counted
states**, including four initializer states. No state was added or removed;
the candidate's whole-program halting equivalence remains open.

The remaining substantive obligations are:

1. Preserve and integrate inherited interpreter operations under actual hook
   redirection, including the shared increment, literal push, calls and returns.
   Contracts for the unmodified interpreter cannot be assumed to apply unchanged.
2. Prove the full 204-node partial source/binary simulation, composing the bank
   contracts with core operations and caller-frame invariants, including cons,
   composition, case, fixpoint and both halting directions.
3. Compose with the already-verified source/search equivalence and paid blank
   initialization, then audit the final smaller-machine halting theorem.

The next step is **core preservation under hook redirection**: classify shared
controls and private literal blocks, prove unaffected transitions/runs retain
their contracts, then compose the complete lowered-program simulation. The
Catch-Up conjecture remains unresolved in this campaign. No new game outcome,
counterexample or proof-size minimality claim is made.


## Checked measurements

The final replay used **eight ordinary Lean commands** (seven proof modules
and Audit) in **25.418 seconds**. All **64 axiom audits** pass:
56 new supporting theorems and 8 reused endpoints, all standard-axiom-only.
The separate complete native export took **4.974 seconds**;
the physical checker subprocess took **3.698 seconds**.

All **34,580 native cells** agree: both symbols at every one of 8,643 local
controls, plus hook and bridge, in both body and initialized machines.
**2,175 whole-tape executions** completed, totaling **1,349,110 transitions**,
maximum **334,398** per case. This includes 651 arbitrary-earlier-bit-prefix
cases and four larger cases. Every diagnostic execution step used an exported
M cell. All **ten deliberate corruptions** were rejected. No intact-controller
counterexample or new game outcome was found.

The seven new UTF-8 Lean sources total **27,205 bytes** and their
ordinary compiled objects **1,313,624 bytes**, including all 56 new
supporting lemmas. Prior support remains counted in earlier manifests.
The complete native export is **819,651 bytes**.
Peak child RSS was **6,232,195,072 bytes** on macOS 26.6.2 arm64,
16 logical CPUs. There are **41 new manifest records**, plus 870 preserved prior
records. Artifact sizes are upper bounds, not shortest-proof claims.

Checked benchmark SHA-256:
`1089a59763b6b9e0312c16f86bd18d4a2a0d7dbdf5b1f63bff0c28d9879f8a20`.
Complete native export SHA-256:
`94e0bed784ab0ae6455fc3fb999cb454592cdf4113693cd8fb5da58e041b63df`.
Prior local-table export remains:
`056a67ec46fc1082715ed52d32d176f92d0d88131ac9a954885396555c5c2746`.
