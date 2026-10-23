> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Constant continuation jumps without redundant reads

The new binary machine `CatchUp.Machine.DirectCryptid.M` has exactly
**1,377,576,954,792 numbered states**, including blank-tape initialization.
Lean proves

```lean
ConjectureMachines.Halts DirectCryptid.M ↔ ¬ Search.Conjecture
```

`Search.Conjecture` is the literal pinned Catch-Up proposition, including N=0.
Both earlier machine definitions are preserved. Lean also proves halting
equivalence with each, and the exact new count is over 6400 times smaller than
the immediately preceding shared-continuation machine. C remains unresolved;
this is progress on its encoding, not a new result about which player wins.

| Machine | Kernel-checked numbered states |
| --- | ---: |
| Original `Cryptid.M` | 50,981,066,868,123,701,957,622 |
| Shared `SharedCryptid.M` | 8,908,727,654,950,392 |
| New `DirectCryptid.M` | 1,377,576,954,792 |

The complete new transition table has 2,755,153,909,584 entries. `rows` is its
total finite generator and `rows_machine` proves reconstruction yields M.
The full table is not materialized. Its size is still enormous; no low-state
or state-minimality claim is made.

## What the optimization proves

The shared compiler ended each source operation with a named continuation.
The old binary translator read an entire encoded tape symbol even when that
continuation ignored it. `Direct.readAux_restore` and `Direct.read_restore`
prove that reading bits and restoring the head before such a continuation has
exactly the same effect as entering it directly. The identity holds on arbitrary
binary tapes, not just well-formed encodings.

`Direct.block_eq` proves equality of the old and new one-operation executions.
Generated physical-write returns need a separate argument:
`Direct.write_payload` proves every enumerated write return is a constant
`Share.jump`. This condition matters. `Direct.tail` is not a correct replacement
for arbitrary tape-dependent goto payloads. `DirectTest.unrestricted_shortcut_false`
is a kernel-checked diagnostic counterexample to that unrestricted claim, and
`bad_payload_not_enumerated` proves that payload cannot occur in the generated
support. Genuine source gotos retain their decoder.

`Direct.body_eq_on` and `body_supports_on` establish execution and support
preservation for every enumerated control label, every local store, and every
binary tape. `binary_supports` closes the graph. `binary_halts_iff` uses the
supported-state relation to prove both directions of evaluation-domain
equivalence; simulation makes positive progress. `Direct.halts_iff` composes
this with the reused alphabet simulation, continuation sharing, finite numbering,
Post-machine conversion, and explicit initializer. No assumption about C,
termination of the outer search, or bounded resource success is used.

`DirectSearch.halts_iff_code` applies this compiler to any source code. Its
Catch-Up instance reuses the existing exact evaluator and counterexample-search
proof. `DirectCryptid.M` transports its finite index type along the exact count
equality. `halts_iff_shared` and `halts_iff_baseline` connect the preserved
machines through the same literal conjecture.

## Exact count and proof size

`DirectCount.state_count_eq` proves for every source code c that the actual
finite enumeration has size `412 + 10 * sourceSupportCost c .halt`. It counts
all duplicated and unreachable labels, all 1250 write auxiliaries, five local
stores, default slots, the initialization, and both physical phases. A generated
write return costs 40 nodes. Each remaining genuine 13-bit read still expands
into a decoding tree. See count-report.md (`count-report.md` in the historical layout) for the operation
weights and count derivation.

`DirectCount.scalar_count` evaluates the scalar formula using `decide +kernel`;
`state_count` connects that numeral to the actual compiler count. Native
evaluation is used only as a separately logged candidate calculation.

benchmark.json (`benchmark.json` in the historical layout) records all five new Lean sources and their
helpers, reused local and Mathlib dependencies, compiled sizes, hashes, bounded
generation/checking commands, and peak individual-child memory. Interactive
discovery was not comprehensively timed. State reduction adds proof code and
does not establish a shorter proof or a reduction in checking cost. These are
constructive upper bounds, not proof-size lower bounds.

## Verification and regression scope

Run from `research/catchup`:

```sh
python3 machine/direct/verify.py
```

Each subprocess is capped at 120 seconds; each independent trace at 10000
transitions. A resource cap is an error, not a draw or halting verdict. The
verifier checks source pins and 28 preserved baseline-source hashes, builds
the default target with warnings as errors, freshly rechecks each new source,
audits all selected transitive axiom closures, exports four complete tiny
binary tables, and independently executes them in Python. Corrupting each
positive test's first initialization write must change it to an exact loop.
The independent traces are regression evidence, never Lean proof premises.

The first tiny source exercises nine loads, a branch, a write, a move, a goto,
and a back edge. Its initialized 550-state machine halts; the 514-state
blank-input instance loops. The second source has a genuine tape-dependent
goto: initialized 44-state and blank-input 38-state instances respectively halt
and loop. All four state counts and halting/non-halting claims are proved in
Lean. These finite instances test the compiler; they are not Catch-Up cases.

The auditable final gate is `DIRECT_CONTINUATIONS_PASS`, with command outputs,
trace results, and measurements saved beside this report. REVIEW.md (`REVIEW.md` in the historical layout)
records independent review of the arbitrary-tape identity, generated-payload
guard, support, both halting directions, initialization, exact counting, and
numeral machine. No `sorryAx`, custom axiom, native proof premise, or unfinished
Catch-Up theorem is accepted. Audited closures contain only the standard
`propext`, `Classical.choice`, and `Quot.sound`; the scalar count uses only
`propext`.

The final run returned that success marker: all 13 recorded commands exited 0,
all 28 preserved source hashes matched, and all 38 requested axiom inspections
passed. Independent review closed every gate. A fresh aggregate-only import
also checked the final machine and its headline axioms. The fresh kernel count
replay took 56.072 seconds; maximum individual-child RSS was 23547527168 bytes.
Recorded command times sum to 97.254 seconds on macOS 26.6.2 arm64, 16 logical
CPUs. The five new modules contain 34489 UTF-8 source bytes and 63 theorems,
with 192133 reused local source bytes and 2113600 new compiled-module bytes.
These are artifact measurements, not a claim of proof compression.

## Pins and remaining boundaries

Lean 4.27.0 and the existing Mathlib commit
`a3a10db0e9d66acbebf76c5e6a135066525ac900` are unchanged. The root Cryptids source
commit is `a0c1f56af53a76e985a656032b48015f7e48921b`. Its machine model is the
existing source-checked downstream port. Root Lean 4.35 integration remains a
separate compatibility task; no build in that newer toolchain is claimed.

No new original-game counterexample, strategy theorem, or proof of C was found.
This optimization completes the requested compiler step. For further machine
compression, the remaining per-operation decoding trees are the next target;
settling C still requires structural game mathematics or a certified game
counterexample. A smaller machine alone gives no evidence for either answer.
