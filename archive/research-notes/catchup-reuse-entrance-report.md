> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Complete actual switch contract

The frozen `switchBody` now has a kernel-checked contract from its real entrance
15379 through its real external return -1. This closes the missing entrance and
composes the existing restoration and prefix-extraction proofs. It changes no
transition, representation, initialization or allocation.

For arbitrary natural lists `result`, `data` and `frames`, `switch_correct` proves:

```lean
∃ steps, run switchBody steps
  (Int.ofNat switchBody.entry, natBanks result (frames ++ savedFrames data)) =
  some (-1, natBanks data (frames ++ [result.getLastI]))
```

The banks are bottom first. `result.getLastI` is the top result word, and is zero
on the empty list. `savedFrames data = [0] ++ data.reverse.flatMap (fun n => [n,1])`
is the exact existing saved-input format. The theorem has no bound on natural
values, result length, saved input length or caller depth, and no termination
hypothesis. It proves the existence of a finite execution for every such input.
`binary_switch` gives the same execution for the finite binary transition table.
Its local external-port stopping state is the existing proof view's state 15387;
it is not a new allocated whole-program state.

The entrance theorem is stronger than the saved-input specialization. For every
result and arbitrary opposite **bit** bank, `entrance_bits` proves execution from
15379 to 6742 with exactly the retained/default-zero word on the data bank and
that opposite bank unchanged. It thus preserves saved inputs and caller frames
without inspecting or assuming their internal format.

The five new Lean files are in `CatchUp/Machine/Lowering/Switch/`:

- `EntranceTransfer.lean`: finite control invariant and first-return simulation.
- `EntranceRows.lean`: equations about the frozen entrance, clear, word, default
  and bridge cells. No replacement transition table.
- `EntranceClear.lean`: arbitrary-bit scan, physical erasure and frame preservation.
- `EntranceStage.lean`: existing word transfer and bit push proofs applied to the
  actual clones, head staging and the empty-result default word.
- `Entrance.lean`: empty/nonempty entrance and complete raw/finite switch contracts.

## The difficult reuse obligation

The left-to-right word clone returns at old state 1926. The old word primitive
has a successful outgoing instruction there, so the existing `word_present`
lemma for old stopping state 3850 cannot be used unchanged.

We prove the old control predicate `q = 2 or q >= 1927` is forward closed. Its
finite transition check replays in Lean's kernel. Executing old state 1926 enters
state 2, hence cannot later return to 1926. Induction on a finite run ending at
1926 therefore establishes that none of its executed instructions came from
1926. `left_prefix_present` lifts exactly this prefix into a clone with its
modified return. `capture_prefix` can now reuse `Words.word_transfer false`
without assuming the modified instruction agrees with the original one.

The retained word is temporarily on the opposite bank. `clear_correct` erases
all remaining data bits, including their physical markers, for arbitrary bit
lists and arbitrary opposite banks. Its proof scans outward and then erases
pairs inward by induction. The existing right-to-left word transfer returns the
retained word to the now-empty data bank. Empty results instead execute the two
actual zero-bit pushes, creating both framing zeros of word zero. Every bridge
and final head position is included. Existing restoration and extraction then
supply the rest of `switch_correct`.

## Checks and proof cost

Reproduce from the repository root:

```sh
python3 -B research/catchup-reuse/entrance/verify.py --full
```

The completed replay ran six strict Lean commands: five modules and the audit.
All **41** new supporting theorem endpoints passed the axiom audit. The only
reported axioms are subsets of `propext`, `Classical.choice`, `Quot.sound`.
There is no `sorryAx`, custom axiom, unfinished conjecture dependency or
native-only computation accepted as a proof. Imported pinned ordinary objects
are reused; the entire imported library was not rebuilt.

Pinned versions are unchanged: Lean 4.35.0-rc4 commit
`c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`, Mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`, Cryptids blobs
`8fed07fa2981ecd96141303b0d8982116106f6eb`. The original Lean 4.27.0 game package
and its Mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900` are preserved.

The five new UTF-8 Lean sources total **20,686 bytes**; their compiled objects
are **1,194,128 bytes**, excluding previously recorded imported support. All
16 earlier benchmark manifests and their **726** source/object/artifact records
were checked unchanged before and after replay. New evidence has 29 manifest
records. These are proof-size upper bounds in the documented serialization,
not minimality claims or a complete short proof of the conjecture.

The six Lean commands took **40.252 seconds** in total; peak child RSS was
**6,517,440,512 bytes** on macOS 26.6.2 arm64 with 16 logical CPUs. Each Lean child
has a 120-second deadline, 8192 MiB Lean allocator limit and 16 MiB output limit.
The allocator limit is not an OS RSS cap. Interactive proof-generation cost was
not instrumented separately; replay/checking cost is recorded in the receipts.

The independent Python bank oracle executes the frozen native-export rows and
compares the **entire tape and final head position**. It passed **10,018 cases**
and **39,492,130 transitions**: 6,760 complete switches, 1,600 entrances, 1,651
raw-bit clearing cases and seven larger cases. The complete-switch grid includes
169 empty results, 2,197 zero top words, 6,084 nonempty discarded tails and 520
empty saved inputs. Larger cases include 1024-valued words, 129 result/input
words and 512 caller frames. Maximum case: 18,217,566 transitions. Every entrance,
clear and relevant bridge controller is visited. Ten targeted corruptions are
rejected. These are bounded diagnostics, separate from the universal Lean proofs.

The physical test subprocess took **8.524 seconds**, under 120 seconds and 1 MiB
output. Positive cases have 50 million steps each; corruptions have 100,000.
Exhaustion is an error, never an outcome. Native rows have SHA-256
`056a67ec46fc1082715ed52d32d176f92d0d88131ac9a954885396555c5c2746`.

Benchmark SHA-256:
`42e0595a9d4f65eea6292abca33ee9de199425762a50959774a09a8b83d28fc6`.
See `benchmark.checked.json`, `artifacts/` and `SELF_AUDIT.md` for detailed evidence.
The new hostile review is by the implementing agent, not an independent model.

## Remaining scope

No intact-controller counterexample or new game outcome was found. This result
advances verification of the actual smaller candidate; it does not settle C.

The complete certified machine remains **388,819,712 states**, with its existing
`Halts(M) ↔ ¬C` theorem. The newer candidate remains **211,100,482 kernel-counted
states**, including four initializer states, with full equivalence still open.
The actual local switch has 15,387 allocated controls; no controls were added.

The single next integration step is a reusable relocation/frame theorem applying
this complete switch contract at all 92 actual whole-program switch sites.
Actual save/finish/source-successor contracts and the full two-direction
source/binary simulation must also be completed before claiming a smaller
certified Catch-Up cryptid. No new blank-tape theorem is claimed here.
