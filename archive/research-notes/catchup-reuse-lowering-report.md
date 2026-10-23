> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Costed lowering of the actual Catch-Up program

The size gate passes: the complete provisional binary candidate has **211,100,482
states**, including initialization. This is **177,719,230 fewer states (45.7%)**
than the certified 388,819,712-state machine. This result is about the actual
204-node Catch-Up program, not a separate demonstration program.

**It is not yet a certified replacement cryptid.** Lean proves the source table's
identity, allocation and initialization. The new binary bank controllers and the
whole source-to-binary simulation remain unproved. The certified machine and its
`Halts(M) ↔ ¬C` theorem therefore remain at **388,819,712 states**. Nothing here
settles C or establishes any new game outcome.

## Exact allocation

| Paid component | States |
|---|---:|
| Inherited controller constant | 11,288 |
| 1,555 instruction slots × 4,638 | 7,212,090 |
| 436,700 unary literal-pool cells × 462 | 201,755,400 |
| 92 save bodies × (3,723 + 1 entry bridge) | 342,608 |
| 92 switch bodies × (15,387 + 1 entry bridge) | 1,415,696 |
| 92 finish bodies × (3,855 + 1 entry bridge) | 354,752 |
| 1 source-successor body × (8,643 + 1 entry bridge) | 8,644 |
| Blank-tape initialization | 4 |
| **Total** | **211,100,482** |

Every new operation occurrence receives its own full binary body. No saving from
future sharing is assumed. All internal primitive copies, exit bounces, error
states, return addresses and old projected literal cells remain charged, including
unused cells. All 277 new operation sites have distinct paid entry points.

The source DAG contains 77 compositions, 92 cons nodes, 23 branches, nine fixpoints
and one each of zero, tail and successor. Its 204 nodes and root 203 are retained.
The layout has seven root/helper instructions, and allocates 1/1/1/7/10/1/7
instruction slots for zero/tail/successor/composition/cons/branch/fix respectively.
Shared source nodes are compiled once. Branch and fixpoint use existing calls,
case dispatch and returns; they are not free semantic execution instructions.

The program resides in finite control and its charged literal pool. The initializer
only creates the empty-bank representation `#[0,0]`. Lean proves its four-step
run from the all-zero tape into the candidate body at state zero. There is no
unaccounted preloaded program tape.

## Missing operations are implemented, with proof obligations exposed

The candidate is an explicit finite binary transition generator, defined by
`Candidate.transition` and the concrete templates in `Library.lean`. Its runtime
instructions only read/write one bit, move left/right and change finite state.
The template generator uses the existing 460-state bit primitive and 3,851-state
word primitive, whose proofs remain in the preserved import closure. It does not
call a host list operation during Turing-machine execution.

For `.cons f g`, with data in reversed source-list order and earlier frames F:

1. **Save** preserves input D and appends a sentinel and tagged copy to F. The
   exact saved payload is `[0] ++ flatMap(reverse D, n ↦ [n,1])`.
2. Call f using the actual target and continuation literals.
3. **Switch** retains `headI(f D)`, using zero for an empty result; clears the
   result tail; restores D from the tagged copy; and leaves the retained head as
   one frame above F. A concrete shifting routine extracts the bottom word while
   distinguishing the following bank boundary from blank tape, even for empty D.
4. Call g on restored D, then **finish** transfers the retained head back onto
   g's result, leaving exactly F and performing the ordinary return.

The literal source successor returns the singleton `[headI(input)+1]`. Its new
body projects to a singleton defaulting to zero, then enters the already charged
stack-increment helper. It does not erroneously retain the input tail.

Fixpoints call their body, branch on its result, return its tail on zero/empty,
and otherwise discard the positive head and repeat. The back edge does not
accumulate one extra source-loop frame per iteration.

These are implemented behaviors supported by bounded diagnostics. Their
**universal canonical-bank contracts remain open**. Reusing primitive bit/word
proofs does not automatically prove the new controllers or rule out unintended
halting/divergence. After those contracts, the whole finite-DAG compilation needs
a partial-source correspondence and a contextual simulation in **both** halting
directions, including case/fixpoint. Only then can the existing search theorem
yield `Halts(new M) ↔ ¬C`.

## Kernel evidence and executable diagnostics

Five core Lean modules and Export/Audit are replayed strictly. Nineteen theorem
audits allow only `propext`, `Classical.choice`, and `Quot.sound`. There is no
`sorry`, custom axiom or native-only proof in the core target. In particular:

- `Source.correct` identifies the literal DAG with `Program.program` by reflexivity.
- `allocation_count` proves that the inherited body plus all actual cloned binary
  templates equals 211,100,478. The numeric machine type alone is not the argument.
- `generated_count`, `initializes` and `beats_baseline` prove the initialized
  count, blank initialization and numerical comparison.

The old program-table namespace collides with a newer prototype's namespace.
`Source.lean` contains the identical table in a distinct downstream namespace and
proves its decoded source identity. Neither the reference game nor old files were
edited. A previous count-reduction attempt hit the 8-GiB Lean allocation budget;
the retained failure receipt precedes a proof using the general cost formula and
separately checked counts, avoiding expansion of the 436,700-cell pool.

The ordinary Python/native diagnostics are separate from kernel evidence:

- 1,000 binary bank cases, 1,502,380 transitions, including empty data/results,
  zero words and nonempty earlier frames.
- All 63,216 cells of the four binary templates agree with Lean's native export.
- All 277 allocated new-operation sites execute with correct full tape, head and
  actual callback; 732,536 transitions. Twelve deliberately broken controllers
  are rejected, covering missing transitions, wrong motion and premature exit.
- A separate recursive literal-source evaluator agrees with the whole lowered IR
  in 1,005 completed comparisons. All 204 nodes were attempted on five inputs.
  Fifteen cases at nodes 164, 202 and 203 exhausted the source-fuel bound; they
  supply no outcome. The IR executes 432,387 steps in the completed comparisons.
- Deterministic regeneration agrees under Python hash seeds 0, 1 and 42. An
  unordered-set port-numbering bug was found and fixed before freezing the tables.

No full 211-million-row text dump or full root-game execution is claimed. The
finite generator and its serialized descriptors are retained in `candidate.json`;
native export supplies all new template rows and every hook/bridge. Bounded tests
do not establish universal semantics or turn timeouts into draws.

## Reproduction and dependencies

From the repository root:

```sh
python3 -B research/catchup-reuse/lowering/verify.py --full
```

This command checks thirteen prior frozen snapshots (620 manifest records), the
source/dependency pins, seven strict Lean commands and bounded diagnostics. Each
child has a 120-second deadline; Lean uses `-DwarningAsError=true`,
`-DautoImplicit=false`, `-M8192`, and a 16-MiB output bound. Diagnostic subprocesses
have a 1-MiB output bound. `-M8192` limits Lean's allocator, not operating-system RSS.
Commands, elapsed checking time, peak child RSS, source/object/artifact sizes and
hashes are in `benchmark.checked.json`. Interactive generation cost is separate
and was not instrumented. No proof-size, runtime or state-count minimality claim
is made; all new support and earlier manifests are included in the record.

The isolated build retains Lean 4.35.0-rc4 (compiler
`c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`) and Mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`, with Cryptids source blobs pinned to
`8fed07fa2981ecd96141303b0d8982116106f6eb`. The original game package remains on
Lean 4.27.0 / Mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900`.
No silent upgrade or cross-version kernel theorem is claimed.

## Decision

The complete design fits with substantial room: the additional binary controllers
cost about 2.12 million states, while the paid literals dominate at about
201.76 million. There is now a concrete whole-program reason to invest in its
correctness proof. Further isolated demo-count reductions are unnecessary for
this decision.

The highest-value next step is to prove the **actual cons bank controllers and
their frame contracts, starting with switch**, then connect the actual DAG to
this machine in both halting directions. This is the route to replacing the
388,819,712-state cryptid. Its mathematical proof work is still substantial; no
credible session-count or completion date follows from the size theorem.
