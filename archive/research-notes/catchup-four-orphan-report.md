> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.FourOrphan](../../CatchUp/FourOrphan.lean).

# Four-pair orphan reserves: certified counterexample

## Exact target and result

The proposed families have remaining counters `{z} ∪ pairs(B)`, with four
distinct even starts `B`, every start at least10, no start12, and z in{6,7}.
The acting player has deficit z or z+2. The desired invariant was nonwinning
for that acting player, so the waiting defender could avoid loss.

The equal-deficit family is **false** at

```
z=7, B={10,18,20,40}, deficit=7,
remaining={7,10,11,18,19,20,21,40,41}.
```

The acting player takes **41** and forces a strict win. The opponent then
faces `({7,10,11,18,19,20,21,40},34)`, whose exact value is loss.
`CatchUp/FourOrphan.lean` proves this finite loss by kernel replay through
the existing executable evaluator and its proved reference correspondence.
It reuses that subproof once to prove the winning pick, negate the quantified
four-pair invariant, and prove the same win under the frozen literal
absolute-score evaluator. The waiting defender cannot avoid loss.

This is a counterexample to the **auxiliary invariant**, not to original C.
The support is a normalized midgame, not an initial interval; no forcing
reachability from an eligible original interval or least-counterexample
claim is made. The two-pair state `({7,10,11,18,19},7)` is nonwinning by the
previous theorem. Adding20,21 and40,41 therefore provably breaks this
two-pair-to-four-pair lift.

## Why the failure matters to the triangle strategy

For every even q>=42, take a five-core-pair triangle support

```
reserve={6,7,13}, core starts={10,18,20,40,q}, deficit=1,
Player1 to move.
```

The previously proposed choices

```
Player1: 6
Player2: 13
Player1: q+1
Player2: q       (ordinary mate)
```

reach exactly the certified winning reserve above, with Player1 to act.
Lean proves this trace legal for all q>=42 (and the support is canonical
when q is even). It proves the reached mate q is a strictly losing choice
for Player2. This is an unbounded failure of the unchanged response recursion,
not just a root value observed by a solver.

It does **not** prove the five-core-pair triangle root is winning for Player1:
Player2 may choose a better response before entering the forbidden reserve.
Nor does it invalidate the proved three-core-pair triangle theorem.

## A uniform arithmetic replacement for large q

At the decision immediately before the bad mate, remaining counters are

```
{7,10,11,18,19,20,21,40,41,q}, deficit=q-7, Player2 to move.
```

For every q>=100, Player2 can take **10,40,41,q in one turn and win**.
The preparation totals91, strictly below q-7. Taking q last leaves
`({7,11,18,19,20,21},98)` to Player1. Its remaining sum is96, so catching up
is impossible. `uniform_far_turn` certifies the specific ordered turn;
`uniform_far_repair` proves strict win using the existing completed-turn
strategy API and this terminal comparison, without another game-tree search.

This abandons the false unconditional reserve invariant in favor of an
explicit arithmetic response at the reached node. It is not a universal
strategy for all five-core supports. The q98 boundary test rejects the
planned extra q pick: the preparation already equals its deficit91 and
equality immediately ends that turn.

## Retaining every opponent reply

The bounded exact probe reuses `seven_pairs/slots.hpp` unchanged. Inputs
include495 dense four-subsets of `(10,14,16,18,20,22,24,26,28,30,40,60)`,128 seeded sparse samples,
and additional diagnostics, deduplicated to626 supports. It computes all
four (z,deficit) instances of each support and retains every **ordered
complete opponent turn**, including all second choices after picking the
orphan below its deficit.

| z | deficit | wins | draws | losses |
|---|---:|---:|---:|---:|
| 6 | 6 | 0 | 626 | 0 |
| 6 | 8 | 0 | 535 | 91 |
| 7 | 7 | 1 | 625 | 0 |
| 7 | 9 | 0 | 552 | 74 |

These are exact experimental outcomes for2504 games, not universal theorems
for the other three families. The unique winning support **in this input
set** is the formally certified example; no minimality is inferred.

All31300 complete opponent turns were retained, including10016 turns with
continuing picks. Every friendly safe-first-choice set is recorded. The
ordinary mate fails608 times; most such failures are poor chosen responses
at roots where a different defense remains possible. They are not608
counterexamples to the invariant. At the certified winning root, however,
the branch41 leaves the defender no safe first choice.

An independent absolute-score recurrence reproduces every root value,
every turn endpoint, every safe-first-choice set, and every proposed mate
value. It also checks all224 complete first opponent turns after41 against
strict winning continuations.

The strict winning graph forces41 at the critical root, retains all winning
friendly alternatives thereafter, and retains every opponent move, with
actual continuation/role-swap rules. The final counts are in checks.json.
Every graph state is independently compared with the literal evaluator. A
separate local graph validator ignores solver value labels and checks legal
edges, complete opponent branching, decreasing counter count, and strict
terminal wins. Missing opponent branches, illegal picks, and circular links
are deliberately rejected. This Python graph/checker is experimental; the
Lean theorem is independently kernel-checked and does not trust the JSON.

## Formal assurance, size, and next obligation

Reproduce from the downstream package:

```
python3 four_orphan/verify.py
```

The final gate requires the strict complete build, fresh Lean source replay,
12 public transitive axiom reports restricted to the standard `propext`,
`Classical.choice`, `Quot.sound`, unchanged prior sources/solver/pins, bounded
experimental replay, and independent read-only review. There are16 new
theorems including four private transition lemmas. Lean4.27.0 and the
existing Mathlib pins are unchanged. No unfinished conjecture theorem,
custom result axiom, native-only computation, heartbeat increase, or binary
Turing machine is used.

The finite loss proof still performs exact eight-counter kernel computation.
Its short source is **not** described as a purely explanatory strategy proof.
It is shared by all the symbolic consequences and unbounded embeddings,
avoiding repeated nine-/thirteen-counter game evaluation. The far repair
is proved by arithmetic and turn semantics. benchmark.json counts all new
supporting source, reused local mathematics, compiled modules, and actual
verification time/memory; it makes no proof-size lower bound or minimality
claim. Interactive discovery time is unmeasured; independent replay also
generates the graph, so that command mixes experimental generation/checking.

Next: replace the losing mate adaptively in this embedded family for even
42<=q<=98, using the proved far repair from100 onward. A small-case repair alone
would not prove the full five-core triangle family. The equal-deficit
four-pair invariant must remain rejected. The other three reserve families,
original C, and binary-machine compilation remain unresolved.
