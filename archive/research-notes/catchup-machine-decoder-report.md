> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Shared decoder with a tape-stored continuation

The experiment succeeds on a local routine: **242 binary states**, compared
with **284 states** for its two-copy reference, a saving of 42 states (14.8%).
Both counts are kernel-checked and include blank-tape initialization and all
continuation handling. `DecoderTest.M` has type `Machine 242 2`; Lean proves
`Halts M ↔ Halts referenceM` and proves that this positive instance halts.

This is a local compiler result. The strongest Catch-Up Cryptid remains the
unchanged 313,357,716,212-state `DenseCryptid.M` with `Halts ↔ ¬C`. No new
Catch-Up game outcome, counterexample, or full-machine size reduction follows.

## The protocol and its exact scope

There are two return destinations and five possible decoded results. A bit
immediately left of the payload stores the destination. A call moves left,
writes the bit, and restores the payload head. The shared reader decodes the
payload once, restores the head, and jumps to a result-specific dispatcher.
That dispatcher moves left, reads the return bit, moves right, and selects
the proper continuation. The binary compiler's variable store is `Unit`;
there is no omitted continuation variable whose values secretly multiply the
state count. The return bit is actually on the physical tape.

`DecoderShare.read_returns` proves exact decoding and head/tape restoration
on arbitrary binary tapes, by induction on the read width. `call_reaches`
proves that the optimized call reaches the matching reference result in
three TM1 steps. Other active reference configurations are simulated in one
step. `respects` handles arbitrary continuation bodies, including loops and
further calls. Mathlib's existing `tr_eval_dom` then gives **both** directions
of evaluation-domain equivalence: no extra target divergence can intervene
when the reference halts. `eval_dom` quantifies over every width, decoder to
`Fin 5`, continuation body, and input list. It does not depend on the example's
halting computation or finite tests.

The reference program **also writes the same return bit before its inline
read**. Thus the theorem preserves the entire tape, including this observable
write. It requires no initial value for that bit. This is an explicit
reserved-cell protocol, not a general replacement theorem for a reader that
leaves its left neighbor untouched. The reference is not claimed to be the
smallest equivalent implementation. The comparison measures replacing its
two reader copies within that same protocol.

The present Catch-Up tape has no proved reserved header at every symbol.
Destructively writing its left neighbor could overwrite live data. Applying
this optimization to the real compiler requires a new tape-layout invariant
and semantic bridge. It also requires more than two return destinations and
more than five decoded results. This experiment establishes the local
mechanism and its cost, rather than assuming those later obligations away.

## A routine that uses both calls

The initialized word is `[false,true,true,false]`: one header bit followed by
the little-endian three-bit payload representing three. The first continuation
requires decoded value three and clears its low bit, changing the payload to
two. The second requires decoded value two, clears the remaining one-bit, and
halts. Other first values loop. The decoder is total: the eight three-bit
words map to `value % 5`, so tests also cover the three unused encodings.

`DecoderTest.reference_word_halts` proves the positive reference computation
in five TM1 steps. Existing Boolean relabeling, finite-state enumeration,
the two-phase Post compiler, and blank initializer lift the generic semantic
result to actual binary machines. `blank_tape_preservation` proves equivalence
for **every initialized input**, not just the positive example. The numbered
242/284-state machines and their table reconstruction theorems are explicit.
Both start at state zero on an all-zero, two-way infinite tape. Initialization
creates all four input bits from finite control; no preloaded tape is assumed.

## Complete cost, including storage

For the displayed routine at width three, the source-node accounting is:

| Component | Two-copy reference | Shared reader |
|---|---:|---:|
| Entry | 2 | 2 |
| Both call sites, including tag writes | 112 | 8 |
| Single common reader | 0 | 53 |
| Five return dispatchers | 0 | 30 |
| Ten continuation bodies | 13 | 13 |
| Total source syntax nodes | 127 | 106 |

The common reader's 53 nodes include its restoring moves and result jump.
Each dispatcher costs six nodes, including both movements, the conditional
and both destinations. The initializer costs thirteen nodes for four bits.
All five decoded values and both destinations are enumerated, even when
unreachable on a particular input. The physical count also includes defaults,
the single store value, duplicate-preserving residual enumeration and both
Post phases. `Count.states_length` and the existing seed/rename/relabel counts
connect this accounting to the **actual** generated finite state type.

The experiment also establishes a uniform cost theorem for this concrete
two-caller, five-result handler family. Put `A = 2^n*(n+4)` and let `L` be the
input length. The complete counts are:

```
reference = 6*L + 36 + 4*A
shared    = 6*L + 106 + 2*A
```

`DecoderCost.original_formula` and `shared_formula` prove those equalities
for every width and decoder. `saves_iff` proves that sharing helps precisely
when `A > 35`. These absolute formulas use `DecoderTest.handler`; the more
general semantic theorem permits arbitrary handlers.

The proposed blanket rule that sharing always helps is false in this family:
at width two and input length four, Lean certifies **156 reference states
versus 178 shared states**. The 22-state penalty is retained in
`width-two-counterexample.json` and proved by `two_bit_counterexample`.
At width three the saving is 42 states for every input length. This is a
statement about the declared enumeration, not minimal or reachable states.
No state-count lower bound or global optimality is claimed.

## Checks and reproducibility

From `research/catchup`, using the unchanged Lean 4.27.0/Mathlib manifest:

```sh
python3 -B machine/decoder/verify.py
```

The completed run returned `SHARED_DECODER_PASS`. All twelve commands exited
zero: source/toolchain pins, warning-strict complete build, fresh replays of
all three new Lean modules, axiom audit, native candidate counts, full table
export and independent replay. All 37 transitive axiom reports use only the
standard allowed trio (`propext`, `Classical.choice`, `Quot.sound`) as applicable.
Concrete count proofs use `decide +kernel`; native outputs are not premises.
All 45 previous local source hashes matched. No previous machine, dependency,
source semantics, upstream file, or toolchain was changed. The default library
imports the experiment. Root Lean 4.35 integration remains a separate boundary.

Independent arithmetic matches actual finite enumerations at widths zero
through seven and input lengths zero/four (sixteen observations), separately
from the universal cost proofs. Complete tables for both programs on every
header/payload pattern and empty input cover **34 machines and 17,788 table
cells**. The parser checks both read symbols, every row count and every target
bound. Three deliberately malformed tables are rejected.

The separate Python source calculation and full-table simulator agree on all
cases. Words six and seven halt: reference after 54 transitions, shared after
66, with head at position two and tape ones exactly at position zero. All
other words and empty input repeat complete configurations, with periods
14/20 respectively. Thus this state reduction costs twelve extra transitions
on the successful example; it is not a speed improvement.

Corrupting the shared program's dynamic return-bit write at state 22, read zero,
from `1R140` to `0R140` changes the positive word-six case to a detected loop:
the full configuration repeats after 65 transitions with period 20. This
control exercises continuation storage rather than only initialization.
These executions and malformed-table tests are regression evidence; the
semantic and count theorems are independently kernel-checked.

Every verification subprocess has a 120-second wall cap and 1 MiB captured
output cap. Simulations have a 10,000-transition cap; exhausting it is an
error, never a mathematical outcome. The reused process runtime does not
enforce a child RSS cap. No unbounded search, external model invocation,
public message, push or PR occurred. REVIEW.md (`REVIEW.md` in the historical layout) records the fresh
independent model referee's criticism and evidence.

## Measurements and next obligation

On macOS 26.6.2 arm64 with sixteen logical CPUs, the twelve command times
sum to 36.817 s. Fresh kernel replays took 3.554 s (`DecoderShare`), 4.098 s
(`DecoderTest`) and 5.414 s (`DecoderCost`); table generation took 5.812 s.
Maximum individual-child high-water RSS observed was 5,452,627,968 bytes,
not an aggregate process-tree peak. Interactive proof design was not fully
timed. benchmark.json (`benchmark.json` in the historical layout) separates generation and checking costs
and records the pinned commits, all source/compiled/artifact hashes and traces.

The three new Lean modules contain 20,240 UTF-8 source bytes and forty theorems;
their compiled files occupy 1,399,760 bytes. The local imported support has
34 source files totaling 216,279 bytes; inherited Mathlib compiler sources
and auxiliary checking/export code are recorded separately. All supporting
mathematics is included in these artifact-size upper bounds. A smaller machine
does not establish a shorter proof or lower proof-search/checking cost.

The next obligation is a reserved-header representation for the real
1,250-symbol Catch-Up tape, proving that tag writes leave the decoded payload
unchanged and that moves/writes preserve the layout. Test a pair of actual
reader call sites and charge the added layout and return costs before
attempting full compiler integration. C remains unresolved.
