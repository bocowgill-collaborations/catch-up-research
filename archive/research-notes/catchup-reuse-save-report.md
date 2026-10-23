> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Actual save contract and all 92 copies

The frozen 3,723-state `saveBody` now has a uniform Lean contract, relocated into
all 92 actual save copies in `Lowering.machine` and initialized `Lowering.M`.
Every input length, every natural word width and arbitrary earlier bit frames
are covered. The entire input tape and caller frame payload are preserved.
No transition, allocation or initializer was changed.

The saved format is the existing one consumed by the proved switch routine:

```
savedFrames D = [0] ++ D.reverse.flatMap (fun n => [n, 1])
```

For natural banks, bottom first, the final contract is

```
data D, frames F  -->  data D, frames (F ++ savedFrames D).
```

`Save/Contract.lean` proves `save_bits` for arbitrary earlier bit frames and
`save_correct` for natural frames. The proof pays both sentinel pushes, the
outward scan, every inward bit copy, all three tag pushes per word, marker
restoration and the final return at the original head position. Empty input
appends only the sentinel. Zero words retain both zero delimiters.

The argument uses the existing arbitrary-physical-left-context right push while
the input cursor marker is zero. Each successful copy restores that marker and
moves inward. `copy_ones` covers arbitrary unary widths, `copy_word` copies a
whole symmetric word backward, and `copy_input` uses reverse-list induction.
The caller bank is not assumed to consist of natural words in the stronger
bit-frame statements. None of these proofs rests on a bounded test grid.

`Save/Relocation.lean` supplies:

- `all_saves_bits` and `all_saves`: actual candidate-body execution, from the
  real projected instruction entry through the paid two-step bridge, copied
  routine and exact program continuation.
- `initialized_saves_bits` and `initialized_saves`: the same contract in the
  actual initialized machine, with its paid four-state numeric offset.
- `program_save`: coverage directly for any actual instruction satisfying
  `program[pc]? = some (.bank Bank.save next)`; no supplied placement needed.

`save_count` kernel-checks 92 copies. `save_mem` and `save_coverage` identify
exactly the real program sites, reusing existing placement geometry, hook
uniqueness and entry identities. Save target closure and successful-run lifting
map negative local returns to real continuations. The local finite stopping
index is not mistaken for the executable bridge at offset 3,723. No statement
asserts that all sites are reachable from blank or that their continuations halt.

## Reproduce and assurance

From the repository root:

```sh
python3 -B research/catchup-reuse/save/verify.py --full
```

The isolated strict runner uses pinned Lean 4.35.0-rc4, commit
`c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`; Mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`; Cryptids sources
`8fed07fa2981ecd96141303b0d8982116106f6eb`. It preserves the original
Lean 4.27.0/Mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900` game package.
Existing pinned ordinary dependency objects are reused, not all rebuilt.

All 55 new theorem endpoints and five reused count/initialization endpoints are
axiom-audited. Their only dependencies are permitted standard Lean axioms:
`propext`, `Classical.choice`, `Quot.sound`. No unfinished proof, desired-result
axiom, external solver assertion, native-only proof or circular conjecture
dependency is accepted. The existing actual four-step blank initializer and
candidate count are re-audited. All 18 previous snapshots/800 source, object and
artifact records are preserved byte for byte.

The diagnostic native export queries actual body and initialized transition
functions at every save site, for both symbols. Whole-tape runs use those
queries where available and frozen local rows with the proved relocation
formula elsewhere. This is an explicit hybrid diagnostic boundary, not native
execution of the complete machine at every step. Full tape, head origin and
exact continuation are compared. Raw bit frames and encoded natural frames
are both sampled. Corruption checks target hooks, bridges, initialization
offsets, sentinels, branch dispatch, marker restoration, returns and metadata.

Resource bounds are 120 seconds per child; Lean `-M8192` allocator and 16 MiB
output; physical checker 1 MiB output, 50 million steps per positive case and
100,000 per corrupted case. Exhaustion is an error. The allocator setting is
not an OS RSS cap. Recorded costs concern successful checking; interactive
proof-generation and failed-attempt costs were not separately instrumented.
`SELF_AUDIT.md` records the implementing agent's hostile second pass.

## Remaining certification work

The full certified cryptid remains **388,819,712 states**, with its existing
`Halts(M) ↔ ¬C` theorem. The smaller candidate remains **211,100,482 kernel-counted
states**, including four initializer states. This milestone adds or removes zero
states and closes save correctness/relocation; it does not yet certify the
candidate's complete blank-tape halting equivalence.

Save and switch now cover 184 of the 277 added bank sites. Still required:

1. Actual `finishBody` and `sourceSuccBody` contracts and their 93 placements
   (92 finish copies and one source-successor copy).
2. Preservation/integration of inherited interpreter operations under the real
   hook redirects, rather than assuming unmodified-interpreter theorems apply.
3. Full simulation of the actual 204-node source DAG, including partial
   `cons`, composition, case and fixpoint, with both halting directions.
4. Composition with existing verified source/search equivalence and paid blank
   initialization, followed by the final smaller-machine axiom audit.

The single highest-value next step is the actual **finishBody** contract and
its 92 relocations, reusing the existing arbitrary-width word-transfer proof.
C remains unresolved in this campaign; no new game outcome or counterexample
is claimed. Artifact sizes provide upper bounds for these proofs, not minimality.


## Checked measurements

Final strict replay: seven proof modules plus Audit, eight ordinary Lean
commands in **28.767 seconds**. All 60 audits use only standard
axioms (55 new theorems plus five reused count/initialization endpoints).
The separate native diagnostic export took **86.014 seconds**.
The physical checker took **8.741 seconds**: **26,316 executions**,
**17,746,778 transitions**, maximum **498,796** per case. Every copy received
286 small-grid executions; four larger cases exercise long frames and inputs.
All **16,560 native body/initialized cell probes** agree, and all **ten
corruptions** reject. No intact-controller counterexample was found.

The seven new UTF-8 Lean sources total **30,783 bytes** and their
ordinary compiled objects **2,641,480 bytes**. All 55 new supporting
lemmas are included, with previous support recorded in the prior manifests.
The native diagnostic export is **383,126 bytes**.
Peak child RSS was **6,246,088,704 bytes** on macOS 26.6.2 arm64,
16 logical CPUs. There are **41 new manifest records**, plus 800 preserved prior
records. These are artifact upper bounds, not shortest-proof claims.

Checked benchmark SHA-256:
`d5ac30bb29aee22ec9bcc0bde67504ae890b41e545adedff74ec64f27fd5ea8d`.
Native diagnostic export SHA-256:
`224b8ea33f4b111ac8a9705b9d0e49f3015b5624a0e2aaec7a722f89aac90297`.
Frozen prior local-table export SHA-256:
`056a67ec46fc1082715ed52d32d176f92d0d88131ac9a954885396555c5c2746`.
