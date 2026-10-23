> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Baseline Catch-Up cryptid — 2026-10-20

The finite-control assembly is complete. The unoptimized binary machine has
**50,981,066,868,123,701,957,622 states**, including duplicate and unreachable entries.
The conjecture C and this machine's halting behavior remain unresolved.

```lean
CatchUp.Machine.Cryptid.M :
  ConjectureMachines.Machine 50981066868123701957622 2

CatchUp.Machine.Cryptid.halts_iff_not_conjecture :
  ConjectureMachines.Halts CatchUp.Machine.Cryptid.M ↔ ¬ CatchUp.Search.Conjecture
```

`Search.Conjecture` is the literal pinned reference proposition, including N=0.
The equivalence assumes neither C nor its negation. No new initial-game result is claimed.

## What the machine is

It starts in state zero on the all-zero two-way infinite binary tape. Each transition
writes one bit, moves left or right, and selects a numbered state; a missing transition
halts. The machine evaluates each eligible finite game exactly and halts at a non-draw.
The outer search is partial; every individual minimax evaluation terminates.

`Program.program` is the previously verified explicit 2368-node constructor-only
`ToPartrec.Code` program. Its enter/scan/return evaluator considers every legal pick,
handles the special opening separately, and negates outcomes only when roles swap.
`Program.program_dom_iff_not_conjecture` connects it to the reference semantics.
2368 measures source-program nodes, not machine states or proof size.

`Lowering` uses Mathlib's actual Code→TM2→TM1→binary-TM1 translations.
The four-stack tape alphabet has 1250 symbols; `Alphabet` supplies its reversible,
blank-preserving 13-bit code. Initialization writes the required marker
(`true` followed by twelve `false` bits) from blank tape and restores the head.
The source program itself resides in finite control; it is not supplied on initial tape.

New `Enumeration` definitions give computable lists covering the source labels and
continuations, stack auxiliary labels, binary write labels, and all five store values.
Their `toFinset` equalities prove support and closure. The machine data do not use
the noncomputable finite-support witness. `Boolean` connects Bool to the Fin 2 alphabet.

The existing `Binary` backend enumerates statement subterms and store values.
`Finite` reserves index zero for the default and numbers list entries at index i+1.
Its encoding uses the first equal occurrence; repeated entries are retained as states.
`Post` gives each index a normal and a return phase. A write uses a right/left bounce
which always completes; both directions of the halting simulation are proved.

## Exact table and count

`Assembly.M` instantiates this pipeline; `Cryptid.M` transports it along the proved
count equality so the numeral appears in its type. `Cryptid.rows` enumerates every
numbered state and both symbols. `Cryptid.rows_machine` proves
`Machine.ofRows Cryptid.rows = Cryptid.M`, and the rows have their own halting theorem.
table-spec.json (`assembly/table-spec.json` in the historical layout) records the precise numbering and interfaces.

The complete table is defined by a total finite generator. Its
101,962,133,736,247,403,915,244 entries have **not** been materialized into a text file.
No practical full-table export or full-support enumeration run is claimed.

`Count.state_count_eq` counts exactly the assembled states, preserving multiplicities.
`SourceCount.state_count_eq` proves a scalar recurrence computes that same number.
`ActualCount.scalar_count` checks the numeral with `decide +kernel`, and
`ActualCount.state_count` transfers it to the actual machine. No native computation
or external result is a proof premise. This is counting the original baseline,
not optimizing it. Two independent executable folds also obtained the same numeral.

The first successful isolated kernel numeral check took 52.53 seconds and peaked at
23,974,707,200 bytes of individual-child RSS on this Darwin arm64 host. CPU model and
installed RAM are unavailable through the sandbox. Interactive proof discovery was
not comprehensively timed. Final replay measurements are in `benchmark.json`.

## Reproduction and assurance

Run from `research/catchup`:

```sh
python3 machine/verify.py
```

Each subprocess is capped at 120 seconds; independent tape traces at 1000 transitions.
The verifier checks source pins and model fidelity, runs the warning-strict default
build, freshly replays all machine sources (including kernel numeral computation),
and audits the headline theorems and their dependencies. It also checks the five-store
and 1250-cell enumerations, independently measures the scalar count, and replays the
existing literal 6-, 30-, and 10-state compiler tests. A deliberately corrupted initial
write is detected. These native measurements and Python traces are regression evidence.

`benchmark.json` records exact commands, timings, RSS, all local machine/helper source
sizes and hashes, reused support and Mathlib compiler sizes, compiled sizes, and the
state count. All new supporting mathematics is counted; no proof minimality or
compactness claim is made. A large program-state count does not imply a large proof
lower bound, and a short theorem invocation does not count as the entire argument.

The build uses Lean 4.27.0 and Mathlib commit
`a3a10db0e9d66acbebf76c5e6a135066525ac900`. Cryptids is pinned at
`a0c1f56af53a76e985a656032b48015f7e48921b`. Its root toolchain is Lean 4.35.0-rc4;
`Model.lean` is the source-checked port of its seven core declarations, with the
documented import/module adaptations and `Turing.eval` name. A root-toolchain build
or cross-version Lean theorem is not claimed. See `PROVENANCE.json`.

Only the standard `propext`, `Classical.choice`, and `Quot.sound` dependencies are
accepted. No sorry, custom axiom, unfinished upstream conjecture, external solver
answer, or native-only proof is used. Independent assembly review (`assembly/REVIEW.md` in the historical layout)
checks support, numbering, initialization, and both halting directions separately.

## Failed attempts and next step

A native right-fold count exceeded the interpreter's stack limit; a left fold and the
proved scalar recurrence succeeded. A 30-second LeanProbe numeral check timed out;
the bounded 120-second CLI kernel check completed. These failures were not machine or
game outcomes. An optional simpler count recurrence met a kernel recursion limit;
the verified baseline does not depend on it. Retained logs separate failed generation
from successful checking. No state minimization occurred.

The highest-value next step is a verified reduction of the binary compiler's state
expansion, starting with its read dispatcher. Keep the original baseline and prove
blank-tape halting equivalence before reporting any smaller count. Solving C still
requires additional game structure or a certified counterexample; the present
encoding makes that problem a concrete halting question without resolving it.
