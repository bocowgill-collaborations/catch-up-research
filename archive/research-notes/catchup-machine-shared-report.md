> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Shared continuation blocks — 2026-10-20

The new Catch-Up machine has **8,908,727,654,950,392 states**, with a kernel-checked
blank-tape theorem `Halts(M) ↔ ¬C`. The original 50,981,066,868,123,701,957,622-state
baseline is preserved. Both exact counts are formally proved; the reduction exceeds
a factor of 5,700,000. This remains an enormous machine and is not a low-state result.
C and the machines' halting behavior remain unresolved. No new game outcome is claimed.

```lean
CatchUp.Machine.SharedCryptid.M :
  ConjectureMachines.Machine 8908727654950392 2

CatchUp.Machine.SharedCryptid.halts_iff_not_conjecture :
  ConjectureMachines.Halts CatchUp.Machine.SharedCryptid.M ↔ ¬ CatchUp.Search.Conjecture
```

## Mechanism and uniform theorem

The original alphabet compiler copies its continuation into every leaf of a 13-bit
read tree. Nested loads compound that expansion. `Share.block` makes each source
operation end at a named residual statement. `Share.body` executes these blocks;
original labels remain separate entry points. Read leaves can now target one named
continuation rather than enclosing all its later reads.

This is continuation sharing around the existing decoder. It does not implement one
global bit-reader shared by every source operation. The remaining per-operation decode
and store machinery, repeated list entries, and unreachable states are still counted.

`Share.block_reaches` proves that the blocks finish each original finite statement.
`Share.respects` supplies positive progress: a source step takes at least one block
step. `Share.halts_iff` proves both halting directions for every source program and
input, excluding divergence introduced by splitting statements. `Share.supports`
connects a computable enumeration of entries/residuals to the original support proof.
No chosen noncomputable support supplies machine data.

`SharedSize.before_actual` proves an all-n identity for n nested loads. If A(n) is the
number of syntax nodes in the old translated normal binary body, then

    8191*A(n) + 139261 = 8192^n * (8191*A(0) + 139261).

`SharedSize.after` proves that the new shared support cost for n+1 loads is

    (n+2)*1140965373 + subtermsCost(q).

These metrics have deliberately stated scopes: the first counts one old translated
normal body; the second includes the new entry and shared residual syntax, root
multiplicity, and write auxiliary labels. This proves exponential-versus-linear
compiler syntax growth for the fixed residual q. It is not a universal full-machine
state ratio, runtime bound, or proof-size lower bound. The complete Catch-Up instance's
state reduction is separately proved using the two actual machine counts.

## Complete compilation and count

`ShareBinary` reuses the verified Mathlib alphabet translator and the existing
Bool-to-Fin2, initializer, finite-control, and physical write/move backends. It proves
an unconditional source-to-blank-binary-machine halting equivalence. All source labels,
statement residuals, alphabet values, store values, and write labels are enumerated.

`Shared` instantiates that compiler on the existing Catch-Up stack emulator. It reuses
the exact source program and its proof that every legal game choice is evaluated.
No strategy choice, pruning rule, numerical payoff, or game rule changes. Entry/default
instances are set to the actual code-specific search entry. The initializer writes the
13-bit marker from the all-zero two-way infinite tape and restores the head. Program
data remain in finite control; there is no preloaded program tape.

`ShareCount` proves the exact count formula, including the initializer, every repeated
support entry, five local-store values, default slot, and both physical Post phases.
The formula is 412+10 times the weighted source-support sum. Its fused scalar
implementation is proved equal to that enumeration. `scalar_count` uses
`decide +kernel`; `state_count` transfers the numeral to `Shared.stateCount`.
Native measurements are corroboration, never proof premises.

`SharedCryptid.M` reindexes along this equality, so the exact numeral appears in its
type. It proves halting equivalence to C's negation and to the fixed original machine.
`SharedCryptid.rows_machine` reconstructs M from its full finite table generator.
The 17,817,455,309,900,784 entries are not materialized. No practical full-table export,
state minimality, proof minimality, or low-state claim is made.

## Finite tests and reproduction

`ShareTest` has nine nested loads, branching, writing, moving, halting and a back edge.
Its `source_step` theorem covers both possible read bits and both stores on arbitrary
tapes. The initialized machine is proved to halt; its blank-input counterpart is proved
to loop. Their exact counts 1198 and1162 use kernel computation. Their complete tables
are exported and independently simulated in Python. Corrupting the initial write of
one to zero changes the trace to an exact repeated configuration, as expected.
The old tiny-instance count 86074 is only a native measurement: direct kernel reduction
of that large unfolded list hit a recursion limit. No headline comparison depends on it.

From `research/catchup`:

```sh
python3 machine/shared/verify.py
```

The verifier checks source pins and unchanged baseline proof/data files, runs the
warning-strict default build, freshly replays all seven new modules including the
full kernel count, audits 35 headline/dependency declarations, measures counts, exports
the two tiny tables, and replays positive, negative and deliberately mutated traces.
Each subprocess is capped at 120 seconds and each trace at 10000 steps. See
`benchmark.json`, `axioms.txt`, `trace-checks.json`, and `REVIEW.md` for actual results.

The production count build took 54.59 seconds with approximately 24.06GB peak
individual-child RSS; a separate isolated kernel count took 54.95 seconds. Interactive
proof discovery is not comprehensively timed. Final fresh replay timings, hardware,
source/helper byte sizes, theorem counts, compiled sizes, and hashes are recorded in
`benchmark.json`. All newly introduced mathematics is counted; reused support and
Mathlib compiler sources are recorded separately.

The reduction in states adds supporting proof code. Numeral checking still costs
roughly 55 seconds and 24 GB; no proof compression or lower checking cost is claimed.

Lean 4.27.0 and Mathlib commit a3a10db0e9d66acbebf76c5e6a135066525ac900 remain pinned.
The canonical Cryptids model is the unchanged source-checked downstream port; root
Lean 4.35 integration remains separate. Only propext, Classical.choice and Quot.sound
are accepted. The scalar numeral uses only propext. There are no sorries, custom
result axioms, native-only proofs, source upgrades, pushes, or public claims.

## Highest-value next step

Remove redundant decoding for constant continuation jumps, first proving the read-and-
restore identity needed to replace those reads by direct jumps. This is another bounded
compiler lemma; preserve both verified machines and require halting preservation and
an exact new count. The campaign still needs game structure or a certified counterexample
to settle C; reducing the encoding alone supplies neither.
