> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.CanonicalFive](../../CatchUp/CanonicalFive.lean), [CatchUp.CanonicalSmall](../../CatchUp/CanonicalSmall.lean), [CatchUp.CanonicalFour](../../CatchUp/CanonicalFour.lean).

# Canonical five-pair reserve: an unbounded structural reduction

Lean proves that five separated adjacent pairs with **even starts and minimum
at least six** are nonwinning at normalized deficit three. For starts
`a < b < c < e < f`, separated by at least two, the theorem is

```
a >= 6, all starts even
  -> Position.value ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1}, 3) != win.
```

`CanonicalFive.five_three_nonwin_min_six` has no bound on counter sizes or gaps.
Nonwinning means the player acting at this normalized position cannot force a
win; it does not assert a draw. The earlier reference correspondence connects
this value to the literal post-opening rules and outcome optimization.

For minimum four, `lowest_lower_child_nonloss` proves that picking the lowest
lower counter cannot win. Together with the previous theorem covering all
five upper-counter picks, `win_requires_anchor_four` proves that any remaining
canonical five-pair win must have minimum exactly four and use one of the four
other lower counters. The full minimum-four claim remains open, as do the
original interval conjecture and any uniform closure over arbitrary pair count.

## Supporting classifications and the repair

The proof establishes these exact classifications for separated even starts
with minimum at least six:

| Pairs | Deficit | Strictly winning start tuples, exactly |
|---|---|---|
| Two | 6 | `(6,10)`, `(6,12)` |
| Three | 5 | `(6,10,12)`, `(6,10,20)` |
| Four | 4 | `(6,10,20,40)` |

These are `two_six_win_iff`, `three_five_win_iff`, and `four_four_win_iff`
in `CanonicalSmall.lean` and `CanonicalFour.lean`. All other tuples in their
stated domains are nonwinning; they need not be draws. Each nonwinning proof
covers every legal initial pick, then supplies a legal defensive response.
The exceptional winning directions are separately replayed in the kernel.

After an opponent takes a lower counter `q` at deficit three, its upper mate
`q+1` normally gives the defender a safe response, leaving four pairs at
deficit four. The exact four-pair classification isolates the sole obstruction
`(6,10,20,40)`. For that obstruction, `sparse_repair` proves a different reply:
when `q >= 42`, take `6,10,20` in the same turn, then take `q+1` and catch.
The successive deficits are `q-3, q-9, q-19, q-39`, and the residual position
is `({7,11,21,40,41},40)`, a kernel-checked draw. This handles arbitrarily
large `q` symbolically. The remaining finitely many even `q` use explicit
friendly witnesses and kernel-checked leaves, with every opponent response
retained. The bounded leaf at `q=22` uses `20`; the other thirteen-case
family's leaves use `10`. Smaller classifications use analogous continued
pick repairs. The final theorem is not based on extrapolating a table.

The lowest-pick boundary at minimum four needs a separate response by `20`
for starts `(4,6,10,20,40)`. `boundary_mate_loses` formally proves that after
the opponent picks `4`, taking the mate `5` loses even though the defender's
position is nonlosing. Thus the proposed conditional rule "take the mate;
if it loses, take the smallest remaining counter" fails: both choices are
`5` here. This is a counterexample to a reply rule, not to the reserve claim
or the original conjecture. Other failed residuals and the failed direct
eight-counter checker route are preserved in `failed_attempts.md`.

## Checks actually completed

Run from `research/catchup`:

```
python3 canonical_five3/verify.py
```

The completed run passed pinned-source and prior-proof hash checks, the full
warning-strict downstream build, fresh elaboration of all five new proof
sources, and fifteen transitive axiom audits. Audits include the evaluator's
reference correspondence, classifier soundness, new results, and the existing
high-level search halting equivalence. Every axiom list contains only
`propext`, `Classical.choice`, and `Quot.sound`. No unfinished conjecture,
`sorryAx`, custom result axiom, or native-only computation supports these
theorems. A fresh-context independent mathematical review accepted the proofs
and their limited scope; see `review.md`.

Separate experimental checks completed:

- 87,419 five-pair shapes and all 437,095 lower-pick children, with no losing
  child. Of these shapes, 67,425 exhaust the range with minimum four or six
  and maximum even start at most 68; 19,994 are distinct held-out sparse
  samples, seed `20261022`. This is bounded evidence for the unresolved
  minimum-four claim, not its proof.
- 35,008 smaller classification cases, all matching the proved classifications;
  65 were also reproduced by the independent absolute-score evaluator.
- 510 five-pair child comparisons with the independent absolute-score evaluator.
- 263 installed defensive-response obligations, including every initial pick
  for 26 five-pair shapes and three lowest-pick boundary cases. Full policy
  expansion checked 19,274 distinct states, 13,348 opponent edges, 15,268
  friendly edges, 8,782 same-player continuation edges, and 473 terminals.
  Every visited state was independently compared with the absolute-score
  evaluator. Every opponent legal choice is expanded, including choices that
  keep the opponent acting. Below the installed repairs, the experimental
  policy retains exact safe friendly choices.

The C++/Python outputs are experimental and separate from Lean proof replay.
The earlier classifier's proved soundness supplies the formal assurance for
the finite leaves; these experiments introduce no new trusted checker or
certificate format. Inputs, outputs, source hashes, and complete commands
are retained in this directory and `benchmark.json`. Exact search uses
distinct missing-cache markers; a timeout is an error, never a game outcome.
Each final verification subprocess group was capped at 120 seconds; the
experimental C++ loops additionally have 25-second caps and save checkpoints.

## Versions and proof-size accounting

The unchanged downstream package uses Lean `4.27.0` and Mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900`. Cryptids is pinned at
`a0c1f56af53a76e985a656032b48015f7e48921b`; the compiled reference API blob is
`413bb420af5d78c79be7f55096862fa534ca0b7d`. The separately inspected literal
reference source is pinned at commit
`1646ca16afd6cc7a693d3bdc9f066c4d3cc01a89` (its own toolchain is `4.33.1`),
without upgrading this package or using the unfinished conjecture proof.
`SOURCES.json` and `benchmark.json` record the complete provenance.

All new supporting mathematics is counted: 22 theorem declarations in six
UTF-8 Lean files, totaling 33,740 bytes, plus 182,005 bytes of reused local
proof support in the recorded import closure. The six compiled modules total
12,697,152 bytes. These figures include the small exact classifications,
repairs, finite leaves, regression, and audit file; they exclude pinned
Mathlib. There is no separately serialized external proof certificate.

On the recorded 16-logical-CPU arm64 macOS 26.6.2 host, fresh source replay
plus the axiom audit took 61.75 seconds; all recorded verification subprocess
times sum to 86.53 seconds. Maximum observed individual child RSS was
8,025,309,184 bytes, not aggregate memory. Search/generation costs are separate:
the fresh five-pair scan took 1.07 seconds and classification scan 0.33 seconds;
interactive discovery was not timed. A failed direct finite-leaf proof hit
200,000 heartbeats after 28.08 seconds. Supplying friendly witnesses reduced
the leaves to seven counters; the final new files use the default heartbeat
budget. These are measured proof-size upper bounds and checking costs, with
no minimality or proof-size lower-bound claim.

## Relevance and the next obligation

This resolves an unbounded subfamily of the reserve problem used by the
pair-deletion approach to deficit-two interval positions. It also identifies
the exact sparse obstruction to the simple mate response, rather than hiding
it in an enlarged lookup table. It does not settle an arbitrary eligible
interval or add a binary Turing machine. The earlier high-level equivalence
between counterexample-search halting and the negation of the conjecture
remains compiled and audited, but binary compilation remains unfinished.

The single next target is the remaining anchored-four orphan family. For
sorted separated even `b,c,e,f >= 6`, put

```
S = {4,5,b,b+1,c,c+1,e,e+1,f,f+1}.
```

Prove, or refute, that for every `x` in `{b,c,e,f}`,
`Position.value (S.erase x, x-3) != loss`. The new theorem and previous
upper-pick reduction prove that these four obligations suffice for the full
canonical minimum-four five-pair deficit-three nonwinning claim. A useful
lead is an exact classification of the four-pair deficit-four obstructions
whose minimum is four; observations about a `(4,8,...)` prefix remain
experimental and must face every opponent reply.
