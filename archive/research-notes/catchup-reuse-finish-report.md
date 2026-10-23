> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Actual finishBody and all 92 relocations

The frozen 3,855-state finish routine has a Lean contract for arbitrary bit
data, arbitrary earlier caller bit frames, and every retained natural value.
It removes the required retained word from above the caller frames, appends
that word to the data bank, and returns at the original head position. Empty
data, empty earlier frames and retained value zero are included.

Writing banks bottom first, the contract is:

```
data D, frames (F ++ word n)  -->  data (D ++ word n), frames F.
```

The retained word must be present; the previous switch routine supplies it.
Arbitrary caller frames mean the prefix below that word is arbitrary. The
contract does not assert behavior for a missing or malformed retained word.

`Finish/Contract.lean` reuses the existing arbitrary-width `Words.word_transfer`
theorem. It checks the actual embedded template at offset 1 and separately
proves the four actual return steps. `finish_bits` gives whole-tape correctness
for arbitrary bit prefixes; `finish_correct` specializes to natural banks.
The exact local step count is `transferCost F D n + 4`, where the already-proved
transfer cost is `(n+2) * (4 * (F.length + D.length + n + 1) + 24)`.

`Finish/Relocation.lean` proves the actual copied-routine contracts:

- `all_finishes_bits` and `all_finishes`: execution from the real projected
  instruction entry, through its paid bridge, copied body and exact continuation.
- `initialized_finishes_bits` and `initialized_finishes`: the same execution
  in the actual initialized machine with its paid four-state numeric offset.
- `program_finish`: direct coverage of any real `.bank .finish next` instruction.

Every global contract has exact step count `transferCost F D n + 6`, including
both entry-bridge steps. The result uses the existing placement bounds,
first-match lookup, hook uniqueness, projected-entry identity and initialization
simulation. The new target-closure proof ensures every non-return target stays
inside the local body. A negative local exit resumes the actual continuation;
the allocated global entry bridge is not mistaken for a stopping state.
Theorems do not assume that the continuation halts or that every site is reached
from blank. The kernel checks exactly 92 finish placements and proves coverage
of every actual program finish instruction.

No library transition, program instruction, allocation or initializer changed.
The four new proof modules are Contract, Sites, Lift and Relocation, under
`CatchUp/Machine/Lowering/Finish`. All 24 new supporting theorems are counted
and audited, together with six reused word-transfer/count/initialization results.

## Reproduce and assurance

From the repository root:

```sh
python3 -B research/catchup-reuse/finish/verify.py --full
```

The isolated strict runner uses Lean 4.35.0-rc4, commit
`c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`; Mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`; Cryptids sources
`8fed07fa2981ecd96141303b0d8982116106f6eb`. The original game package remains
on Lean 4.27.0/Mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900`.
Pinned ordinary dependency objects are reused, not all rebuilt.

All 30 axiom audits pass with only `propext`, `Classical.choice`, `Quot.sound`.
No unfinished proof, custom axiom, external solver assertion, native-only proof
or circular conjecture dependency is accepted. New receipts bind input source
hashes. All 19 prior snapshots and 841 manifest records are preserved exactly.

The separate native export probes actual body and initialized transition
functions at all 92 sites, for both symbols. Physical diagnostics use those
cells where available and frozen local rows with the proved relocation formula
elsewhere. This is a hybrid diagnostic execution, not a native full-machine
execution at every step. Complete tape, original head, exact continuation and
exact step cost are checked. Both arbitrary raw bit prefixes and natural banks
are sampled, with empty prefixes and zero retained values on every copy.
Ten controller/offset/metadata corruptions are tested for rejection.

Limits: 120 seconds per child, Lean `-M8192` allocator and 16 MiB output;
physical checker 1 MiB output, 50 million steps per positive case and 100,000 per
corrupted case. Exhaustion is an error. The allocator bound is not an OS RSS
cap. Successful checking costs are recorded separately from uninstrumented
interactive proof-generation cost. `SELF_AUDIT.md` records the implementing
agent's hostile second pass; it is not independent model review.

## Remaining before the smaller cryptid is certified

The certified cryptid remains **388,819,712 states**, with the existing
`Halts(M) ↔ ¬C` theorem. The candidate remains **211,100,482 kernel-counted
states**, including four initializer states. Zero states were added or removed
in this milestone. The candidate's whole-program halting equivalence is open.

Save, switch and finish now have contracts and relocations covering 276 of the
277 added bank sites. This is a count of bank sites, not a percentage of the
complete certification effort. The substantive remaining obligations are:

1. The actual source-successor routine and its single placement.
2. Preservation and integration of inherited interpreter operations under the
   actual hook redirects; unmodified-interpreter proofs cannot simply be assumed.
3. Simulation of the actual 204-node source DAG, including partial `cons`,
   composition, case and fixpoint, with both halting directions.
4. Compose that simulation with the already-verified source/search equivalence
   and paid blank initializer; audit the final smaller-machine halting theorem.

The next step is **the actual sourceSuccBody contract and its single relocation**.
It is the final missing added bank routine; then work moves to program integration.
The Catch-Up conjecture remains unresolved in this campaign. No new game outcome,
counterexample, state-count reduction or proof-size minimality claim is made.


## Checked measurements

The final strict replay used **five ordinary Lean commands** (four proof modules
and Audit) in **16.774 seconds**. All **30 axiom audits** pass:
24 new supporting theorems and six reused word-transfer/count/init results.
All use only the permitted standard axioms. The separate native diagnostic
export took **49.383 seconds**; the physical checker took
**5.970 seconds**.

The diagnostics completed **54,100 whole-tape executions**, totaling
**11,312,788 transitions**, maximum **71,286** per case. Every copy received
588 small-grid executions; four larger cases exercise wider words, long data
and long caller frames. All **15,456 direct native transition probes** agree,
and all **ten deliberate corruptions** reject. Exact step cost agrees in every
successful execution. No intact-controller counterexample was found.

The four new UTF-8 Lean sources total **12,809 bytes**, and their
ordinary compiled objects **392,240 bytes**. This includes all
24 new supporting lemmas; earlier support is retained in the prior manifests.
The diagnostic native export is **357,800 bytes**.
Peak child RSS was **6,227,427,328 bytes** on macOS 26.6.2 arm64,
16 logical CPUs. There are **29 new manifest records**, plus 841 preserved
prior records. Artifact sizes are upper bounds, not proof-size minimality claims.

Checked benchmark SHA-256:
`717d14bec4658506baad4f372e88fbccef0da6de6e3fdd659b0f5e9a20fccf50`.
Native diagnostic export SHA-256:
`075509c3488f40a049feb89f13b4b6c9336d78ae124ccae349b814620f954506`.
Prior frozen local-table export remains:
`056a67ec46fc1082715ed52d32d176f92d0d88131ac9a954885396555c5c2746`.
