> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Actual switch prefix extraction: proved

The requested prefix-extraction contract is now proved in Lean for the unchanged
`switchBody` table, for **every retained natural h, natural-word input D and caller
frame list F**. Empty input and both boundary-marker cases are covered. The proof
also composes with the previously verified restoration loop.

The main finite binary-machine theorem is `Extract.binary_extract`:

```
entry 1395: data = h :: D, frames = F
external return port: data = D, frames = F ++ [h].
```

Banks are bottom first. Thus h is the retained bottom word beneath D, not the
top word of D. `binary_restore_extract` starts at restoration entry 6742 with
data `[h]` and frames `F ++ savedFrames D`, and proves the same final banks.
The finite view's local stopping state represents the existing external return
port; it does not add a control to the whole candidate. The actual return port
is reached after both exit-bounce steps, with the head back at the origin.

This is controller correctness, not a new complete cryptid or a game outcome.
The full candidate remains **211,100,482 states, including four initialization
states**. The certified full machine remains **388,819,712 states** with its
existing equivalence theorem. No transition table, initializer or earlier proof
artifact was modified.

## Proof architecture

The seven new Lean modules contain 76 supporting theorems. Every local control
equation is proved equal to the corresponding cells of the actual frozen table.
No semantic operation specification is accepted as an axiom.

1. **Right-bank push with a marked left context.** The original bit-push argument
   is generalized to an arbitrary physical left context. This matters: the
   extraction cursor temporarily changes a left-bank marker to zero, so the old
   contract for an entirely well-formed opposite bank cannot simply be invoked.
   The new frame theorem proves that the right-bank push leaves this context
   unchanged. Its three actual template copies are connected by cell-location
   theorems and the existing successful-run lifting proof.
2. **Copy and restore each cursor bit.** The carry loop returns home, appends one
   bit to the frame bank, finds the temporary zero marker, restores it and
   advances. Induction copies the framed unary word for arbitrary h, including
   h=0, while preserving the entire later input and earlier frames.
3. **Install the boundary.** The next physical marker is remembered as flag 0 or
   1, and a temporary `01` pair marks the boundary. Empty input has flag 0;
   nonempty encoded natural-word input has flag 1 and begins with payload bit 0.
   That zero-payload precondition is essential to the stated contract and holds
   for every nonempty encoded natural-word bank. An arbitrary raw bit suffix
   beginning in 1 is not claimed to be preserved by this operation.
4. **Shift the retained prefix away.** A pass copies all ordinary pairs and the
   temporary boundary inward, ending on a real blank pair. `copy_all` proves a
   run of `8*length+6` steps for an arbitrary list of nonblank pairs. `find_home`
   proves that both ordinary pairs and the temporary `01` boundary are crossed
   without mutation; the boundary is not confused with the true home separator.
   Induction removes every pair of the retained word.
5. **Restore the boundary and return.** Flag 0 restores an empty bank, justified
   using the tape's blank-extension quotient. Flag 1 restores the original first
   marker and zero payload. Both exit motions preserve the complete final tape.
6. **Finite binary execution and composition.** The existing exact `binary_run`
   correspondence transfers the actual-table run to the finite binary machine.
   The new theorem composes directly with `restore_retained_head`; there is no
   remaining extraction hypothesis in the composed result.

The proof uses induction over word payloads, physical pair lists and deleted
prefixes. All lengths, values and caller depths remain quantified; none is
replaced by a bounded table of tested inputs.

## Verification and reproducibility

From the repository root:

```sh
python3 -B research/catchup-reuse/extract/verify.py --full
```

All **eight strict Lean commands** and **76 theorem axiom audits** passed. The
only audited axioms are among `propext`, `Classical.choice` and `Quot.sound`.
There are no unfinished proofs, custom axioms, native-only proof premises or
dependencies on the unfinished Catch-Up conjecture theorem at these endpoints.
The pinned ordinary imported objects are reused; Mathlib and the entire previous
backend were not rebuilt in this session.

Separate full-tape tests load the frozen native switch rows and use the natural
bank contract as their oracle. **4,685 cases / 7,455,628 transitions** passed:

- 2,600 extraction cases and 2,080 restoration-plus-extraction cases.
- Five larger boundary cases, including a retained head of 256, an input word of
  1,024, 129 input words, 512 caller frames, and a caller word of 1,024.
- 118 flag-0 cases and 4,567 flag-1 cases; each run checks the actual observed flag.
- Nine corruptions rejected: wrong empty/nonempty marker restoration, confusing
  the boundary with home in either flag branch, early cursor stopping, a wrong
  opening-bit copy, a missing one-bit push, a nonblank terminator, and damage to
  the frame separator during exit.

The largest positive case uses 673,654 steps. Each positive execution has a
50-million-step bound, each corruption 100,000 steps, and the aggregate child a
120-second deadline. Exhaustion is failure, never a mathematical result.
These finite diagnostics are separate from the universal kernel proofs.

Final checking: **55.157 seconds Lean + 1.793 seconds physical tests**, peak child
RSS **6,074,417,152 bytes**, on macOS arm64 with 16 logical CPUs. Lean children use
warning-as-error, no automatic implicit variables, a 120-second deadline,
`-M8192` allocator budget and a 16-MiB output bound; the physical child has a
1-MiB output bound. The allocator limit is not an OS RSS limit. Interactive proof
generation cost was not instrumented and is excluded from checking cost.

New supporting Lean source totals **34,881 bytes**, compiled objects
**6,034,384 bytes**. Every new supporting theorem and source/object/artifact hash
is recorded, together with **15 prior snapshots / 689 preserved records**, in
`benchmark.checked.json`, SHA-256
`6370d8d5ba7188a6b5d7320172fc3eb9b08e37313e34534dd12a9bc4d04a4742`.
No proof-size or state-count minimality claim is made. The adversarial review
record is a self-audit, not an independent model review.

Lean remains 4.35.0-rc4, compiler
`c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`; Mathlib is
`1f414401f69059aa7eead47b53ee40bd38455eeb`; Cryptids sources remain pinned to
`8fed07fa2981ecd96141303b0d8982116106f6eb`. The original Lean 4.27.0 game package
and its Mathlib pin remain preserved. No source or toolchain upgrade occurred.

## Remaining work

The next theorem is the **actual switch entrance contract, from 15379 to 6742**:
retain the top/default-zero word of f's result, clear its remaining data, and
preserve the tagged original input and earlier frames. The now-proved
restoration-plus-extraction theorem then supplies the rest of the local switch
contract. The source list's head corresponds to the top word of its reversed,
bottom-first data bank; this perspective must remain explicit.

Relocation into all 92 allocated switch sites, the remaining new controllers,
and the complete source/binary simulation in both halting directions are still
open. In particular no new `Halts(M) ↔ ¬C` theorem for the 211,100,482-state
candidate is claimed. No counterexample to the requested extraction contract or
new Catch-Up game outcome was found.
