> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# The actual switch restore loop, for arbitrary input lengths

Lean now proves the **unbounded input-restoration interval of the existing switch
controller**, from local state 6742 to local state 1395. This is a proof about the
actual frozen `switchBody` binary table used in the costed Catch-Up candidate.
No new controller, demonstration program, tape layout or initialization was added.

This closes one substantive controller obligation, not the whole switch contract.
The candidate remains **211,100,482 states**, with its existing four initialization
states; the certified complete cryptid remains **388,819,712 states**. The new
candidate's complete `Halts(M) ↔ ¬C` theorem and C itself remain unresolved.

## Exact proved statement

Both banks store bits bottom first using the existing marker/bit encoding. Define

```
savedFrames D = [0] ++ flatMap(reverse D, n => [n,1])
savedPayload D = encode(savedFrames D).
```

For **every** natural-number list D and arbitrary bit lists A and F, the actual
restore loop has a finite run taking

```
pc = 6742, data = A,             frames = F ++ savedPayload D
pc = 1395, data = A ++ encode D, frames = F.
```

`Finite.binary_restore_input` states this with `FlatInit.runFrom` of a finite,
binary Turing machine whose cells are exactly the existing template. The thin
finite view adds one local stopping state for the external port; that is a proof
boundary, not an extra control allocated to the whole candidate. `binary_step`
and `binary_run` prove the execution correspondence, including absent cells and
out-of-range states. The result is not merely about a separate list interpreter.

The retained-head specialization `binary_restore_retained_head` says that, for
any retained natural h and earlier natural-word frames F,

```
(6742, natBanks [h] (F ++ savedFrames D))
    reaches (1395, natBanks (h :: D) F).
```

Here D is the original **bottom-first data bank**, so it is the reverse of the
source-list convention. The retained head is already staged on the data bank
when this theorem starts. The theorem preserves it below D; it does not yet
prove its capture from f's result or its subsequent extraction to the frame bank.
State 1395 is the actual extraction entry, not the switch return boundary.

## Why the proof is uniform

The cell-location lemmas identify the exact three tag-pop copies, word-transfer
copy, and bridges in `switchBody`; their lookup equations are checked by ordinary
kernel reduction. Their hypotheses are discharged by those actual locations.
No unverified operation specification is assumed at the headline theorem.

The proof reuses the verified Separate bit-pop and Words word-transfer theorems.
A tagged-word iteration consumes all three bits of tag 1, transfers exactly one
framed natural to the data bank and returns to state 6742. The two-bit tag 0
stops at state 1395 while preserving the earlier frame bank. Induction on D
therefore proves finite completion and original order for every list length,
natural value and caller-frame depth. Neither bank prefix needs to be a sequence
of natural words: arbitrary bit strings in the marker/bit geometry are allowed.

This is not a statement about arbitrary malformed physical tapes or tags.
Sentinel stopping preserves earlier frames; the bit primitives may scan across
them physically, so no claim of avoiding all reads of those cells is made.

## Checks and trust boundary

Reproduce from the repository root:

```sh
python3 -B research/catchup-reuse/switch/verify.py --full
```

All four strict Lean commands passed. All **33 theorem endpoints** were audited;
their only axioms are among `propext`, `Classical.choice` and `Quot.sound`. There
are no unfinished proofs, custom axioms, native-only proof computations, or
dependencies on the unfinished conjecture theorem at these endpoints.

Separate bounded tests load the frozen native binary rows and simulate full
tapes, without importing the new proof interpreter. They pass **18,604 cases**
and **30,341,190 transitions**: 18,600 combinations of arbitrary short bit
prefixes and saved inputs, plus four boundary cases including 129 saved words,
128 earlier frames, and 1,024-valued words in each relevant bank. All six
corruptions are rejected: premature halt, wrong motion, a changed sentinel write,
sentinel overrun, treating tag 1 as the sentinel, and a damaged word-transfer cell.
The maximum positive case uses 4,301,308 steps. Tests have a 20-million-step
per-case limit and a 120-second aggregate child deadline; exhaustion is failure,
not an outcome. These tests are evidence separate from the universal proof.

Final checking took **12.009 seconds Lean + 5.262 seconds physical tests** on
macOS arm64 / 16 logical CPUs, with peak child RSS **5,962,203,136 bytes**. Each
Lean child uses the pinned compiler, warning-as-error, no automatic implicit
variables, an 8,192-MiB Lean allocator budget and 16-MiB output bound. The physical
child has a 1-MiB output bound. The allocator budget is not an OS RSS limit.
Interactive proof-generation cost was not instrumented and is not checking time.

The three new core sources total **18,657 bytes**, and their compiled objects
**821,736 bytes**. The full list of new support, hashes, commands, receipts and
14 prior manifests / 668 preserved records is in `benchmark.checked.json`, hash
`3d5f4b0a04ce47ba27226cb1703cf9f74dc2e6a18395362b98bd9e0d29c84551`.
The frozen candidate generator, count, initializers and earlier certificates are
unchanged. There is no state- or proof-size minimality claim. The adversarial
review is a **self-audit**, not an independent agent review.

Lean remains 4.35.0-rc4, compiler
`c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`; Mathlib is
`1f414401f69059aa7eead47b53ee40bd38455eeb`. Cryptids sources remain pinned to
`8fed07fa2981ecd96141303b0d8982116106f6eb`. The original Lean 4.27.0 game package
is preserved. Ordinary pinned compiled dependencies were reused; they were not
all rebuilt in this session.

## Remaining obligation and next step

The next difficult piece is the **actual bottom-word extraction routine beginning
at state 1395**. It must take `(data = h :: D, frames = F)` to
`(data = D, frames = F ++ [h])`, preserving the tape geometry, including empty D
and both boundary-marker cases. Its copying and shifting loops need their own
uniform proof. That is the highest-value next theorem.

Switch entrance/head staging and tail clearing, relocation into all 92 allocated
switch copies, the other new controllers, and the complete two-direction
source/binary simulation also remain open. This session proves a real unbounded
loop in the selected whole-program design; it does not certify that design's
complete halting behavior. No game outcome or counterexample was discovered.
