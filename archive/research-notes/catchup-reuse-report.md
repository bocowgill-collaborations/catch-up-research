> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Catch-Up on the existing verified Chess interpreter

The subsequent shared-restoration construction (`restoration/REPORT.md` in the historical layout)
proves an equivalent **388,819,712-state** machine. It saves 137,500 states
against the intervening decoder-sharing machine and 186,390 against the
389,006,102-state baseline reported here. All formal baseline artifacts are
preserved.

This preserved baseline is followed by two-site decoder sharing (`sharing/REPORT.md` in the historical layout),
which proves the same blank-tape iff for **388,957,212 states**, saving 48,890
more states. The baseline and all evidence below remain unchanged.

The new explicit binary machine has **389,006,102 states**, with the kernel-checked theorem

```lean
ConjectureMachines.Halts CatchUp.Machine.ReusedCryptid.M ↔
  ¬ CatchUp.Search.Conjecture
```

`C` still means `∀ N : Nat, Even (N * (N + 1) / 2) →
CatchUp.value (Finset.Icc 1 N) = Outcome.draw`, including zero. This construction
does not decide `C` or establish another game outcome. It packages the existing
proved counterexample search more efficiently. The previous 313,357,716,212-state
machine and all earlier machines remain intact in the Lean 4.27 package.

## What is reused and what is proved

Chess's `Compilation.Image.body` is a fixed universal interpreter with a shared
graph backend. Its `post_runtime_dom` theorem quantifies over arbitrary stack
inputs. Its proof does not require a chess outcome. We reuse that exact body,
its finite numerical transition generator, and its 388,936,472-state count;
we supply Catch-Up's program as newly initialized data.

The untrusted native compiler produced 204 literal DAG rows, rooted at 203.
`Literal.valid` applies the existing proved finite topology checker and
`decide +kernel`. `Literal.correct : dag.decode = Program.program` is proved
by `rfl`: the table reconstructs the exact source syntax. Hash matches or
native evaluation are not proof premises. The original program's search
semantics, including compulsory opening, equality ending a turn, repeated
picks by one player, outcome ordering and the zero case, are replayed unchanged.

`ReusedRuntime.dag_halts_iff` composes the paid initializer, binary lowering,
shared graph simulation and existing interpreter correctness in both directions.
`ReusedCryptid.generated_halts` connects the literal table to the proved source
program. `halts_iff_not_conjecture` transports it to the fixed numerical machine.
No proof of `C` or `¬C` is assumed.

The complete input consists of the root, all three words of every row, and the
table delimiter, on the initial main stack. There are no source arguments.
The stack has 3,165 symbols; the existing eleven-bit simultaneous-stack codec
produces 34,815 bits. All of these bits are written on an initially zero tape.

| Component | Count |
| --- | ---: |
| Reused fixed binary body | 388,936,472 states |
| Write and return initializer | 69,630 states |
| Complete Catch-Up machine | **389,006,102 states** |

`generated_states` proves the complete sum. `initializes` proves that exactly
69,630 physical transitions reach body state 69,630, with the full input tape
and head restored. The start is state zero on a two-way infinite all-zero
binary tape; program data are not preloaded for free.

The machine has a total transition generator for both symbols and every
`Fin 389006102` state. We have not serialized its entire table. The count includes
unreachable/default/return states of this construction and is not a reachable-state
count or a minimality claim. It saves 312,968,710,110 states, about 99.876%,
or a factor of 805.53 against the previous Catch-Up machine. Against the
392,046,832-state Chess baseline using the same body, Catch-Up now has a
smaller paid initializer. This does not compare difficulty of the conjectures.

## Compatibility and provenance

The original package remains on Lean **4.27.0**, Mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900`. This separate replay uses Lean
**4.35.0-rc4**, compiler commit `c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`,
and Mathlib `1f414401f69059aa7eead47b53ee40bd38455eeb`, matching the reused
Chess checkout at `8fed07fa2981ecd96141303b0d8982116106f6eb`.

`PORT.json` records every migrated file and its old/new hash. `verify.py`
reconstructs each of the five ported sources exactly from the original by
mechanical import, tactic and lemma renames, one elaborator-compatibility
option, and adding `List.nil_append` to one existing proof. The conjecture,
game definitions, evaluator and source program definitions have not changed.
There is no assertion of a Lean theorem spanning different kernel versions.

`PINS.json` records 80 reused Cryptids source modules (5,795,840 bytes), 320
compiled dependency artifacts, both toolchain/Mathlib environments and 49
preserved old sources/helper files. All 80 Chess sources agree with the pinned
commit; Mathlib's tracked working tree is clean. An unrelated Chess commit may
advance that shared checkout's HEAD: the verifier checks the reused files
against the pinned commit's actual Git blobs, together with compiled-cache
hashes, rather than requiring the whole checkout to stay on one HEAD.
The original upstream target
snapshots are additionally documented by `../catchup/SOURCES.json`.

We reuse Chess and Mathlib compiled dependencies through the ordinary Lean
import mechanism. The full check here re-elaborates all eight Catch-Up formal
modules, rather than rebuilding every imported backend/Mathlib module. This is
the normal dependency-cache trust boundary, with exact source/cache pins and
transitive axiom audits. No local dependency is silently upgraded or modified.

## Checks actually run

From the workspace root:

```sh
python3 -B research/catchup-reuse/verify.py --full
```

Result: `CHESS_REUSE_PASS`. All twelve strict Lean source commands exited zero:
the eight formal modules, the axiom audit, native export, count candidates and
finite physical fixtures. All 27 audited endpoints use only `propext`,
`Classical.choice` and `Quot.sound`, or fewer. There is no `sorryAx`, custom
result axiom, native-decision axiom, unfinished conjecture dependency or chess
draw premise. `Literal.correct` and `row_count` have no axioms.

An independent Python implementation of constructor interning, topological
decoding, natural-word encoding and the simultaneous-stack binary codec agrees
with the whole Catch-Up table and bit stream. It also independently simulates
all five retained physical traces from blank tape, validating the complete
initializer at its handoff. The fixtures use the same fixed interpreter body.

| Fixture | Physical steps | Observation |
| --- | ---: | --- |
| Zero source | 19,944 | Halt |
| Successor on `[3]` | 38,370 | Halt |
| Zero branch on `[0,6]` | 188,850 | Halt |
| Positive branch on `[2,6]` | 228,984 | Halt |
| `fix succ` on `[]` | 200,000 | Explicit bound reached |

The last observation is not a nonhalting proof. These tests cover 542,494
transition cells across the five visited-state exports, with overlaps retained;
they are not whole-table enumeration. Four controls reject a forward/self
dependency, an out-of-range root, a corrupted initialization write and a missing
physical row. The finite tests are regression evidence, not proof premises.
No unbounded Catch-Up search was run.

`benchmark.checked.json` is the executed, immutable evidence snapshot. The 12
Lean commands total **92.55 seconds** on macOS 26.6.2 arm64 with 16 logical CPUs;
the largest recorded individual-child high-water RSS is **8,367,374,336 bytes**.
The CPU model and RAM query was unavailable in this sandbox. Each child has a
120-second wall limit, `-M8192` Lean allocation budget, and a one-MiB output
limit except the 16-MiB fixture export. The allocation budget is not an OS RSS
cap. Figures exclude interactive design and the pre-existing backend build.

The three new mathematical modules total 9,887 source bytes and 16 theorems;
with the five ported semantic/source modules the total is 118,977 bytes. Their
compiled modules occupy 4,813,568 bytes. All reused supporting source modules
are separately counted above. The auxiliary checker, native generation code,
complete bit stream and serialized rows have individual byte/hash records.
This establishes an upper bound for this proof artifact; it is not a proof-size
minimality result. The smaller machine does not establish a shorter proof of `C`.

The fresh-context model referee independently checked source fidelity, final
assembly, selected strict Lean replays and retained finite traces; its final
scope and hashes are in `REVIEW.md`. Model review adds criticism, not a new
formal verification authority.

## Reproduction and next step

The replay deliberately has its own output directory and explicit import path.
It needs the pinned, already-built Chess checkout and its matching Mathlib cache.
It writes only here, including `build/`; it does not write to that checkout.
For a different location set `CATCHUP_CHESS_ROOT`; for the same compiler at a
different path set `CATCHUP_REUSE_LEAN`. Missing/mismatched dependencies fail the
checks. No `lake update` or toolchain change to the original package is needed.
Running without `--full` checks the stored receipts, hashes and independent
tests; use `--full` to replay Lean as well.

The failed direct-count route is recorded in `FAILURES.md`: reducing a native
hash-table compiler is unnecessary once its literal output is syntactically
checked. No game counterexample was discovered.

The highest-value next optimization is to test the already-proved shared
decoder at two actual interpreter read sites, keeping this exact 204-row
program and its source proof fixed. Prove that return-tag writes preserve
live tape data and charge every layout, continuation and blank-start cost.
The shared interpreter now accounts for more than 99.98% of the machine, so
reducing program data alone has little scope. Keep this baseline and require
a two-direction simulation plus a full kernel count before accepting another
machine.
