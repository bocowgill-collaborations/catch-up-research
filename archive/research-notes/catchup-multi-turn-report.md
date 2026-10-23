> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.ReserveTriangle](../../CatchUp/ReserveTriangle.lean).

# Pick-five defense through a balanced reserve triangle

## Proved result

The former obstruction is the normalized position

```
remaining = {5,6,7,10,11,13,20,21,40,41}, deficit = 4,
Player2 to move.
```

Taking its ordinary mate13 was already proved to lose. **Taking5 is now
proved safe.** It leaves Player1 acting at

```
{6,7,10,11,13,20,21,40,41}, deficit = 1.
```

The new theorem is uniform in three pairs' labels, not just this example:

```
value({6,7,13,b,b+1,c,c+1,e,e+1},1) != win
```

for even starts `10<=b`, `b+2<=c`, `c+2<=e`, none equal12. The exclusion
prevents overlapping the reserve counter13. The hypotheses ensure nine
distinct positive counters. `uniform_pick_five` proves the corresponding
deficit-four move5 is non-losing for all these labels.

The claim is **nonwinning for the acting opponent**, hence non-loss for the
waiting defender. It does not assert every member's optimal value is draw.
The concrete child's draw value remains experimental; formal nonwinning is
enough to prove the selected defense safe.

`all_nine_replies_safe` quantifies over every remaining counter at the actual
child. `after_five_reference_nonwin` transfers the result to the frozen
literal absolute-score evaluator. `uniform_repaired_branch` also proves that
the pick5 decision is safe at the reached node after `[q,4,q+1,12]` for every
`q>=42` in the previously certified unbounded seven-pair counterplay. It
does not assert safety against every other earlier choice from those roots.

## Why the rule works

The reserve is the arithmetic triangle `13=6+7`. Initial replies are:

| Opponent pick | Defender's completed turn | Result for the opponent |
|---|---|---|
| 6 | 13 | orphan7 + three pairs, deficit8 |
| 7 | 13 | orphan6 + three pairs, deficit7 |
| 13 | 6 then7 | three pairs, deficit1 |
| lower counter of a core pair | its upper mate | triangle + two pairs, deficit2 |
| upper counter of a core pair | its lower mate | triangle + two pairs, deficit0 |

These five clauses retain all nine opponent choices in the concrete case.
They are constructions, not choices selected using an outcome oracle.

The proof closes the **later** adversarial obligations as well. It proves:

- An orphan6 or7 with three allowed pairs draws at deficit orphan+1.
- With two allowed pairs, orphan deficits orphan and orphan+2 are nonwinning.
- With one high pair, orphan+3 is nonwinning.
- Triangle + one pair draws at deficit1 and is nonwinning at deficit3.
- Triangle + two pairs is nonwinning at deficit0 or2.

Deleting an intact pair changes the reserve offset by one. Taking a reserve
counter moves into the existing clean-pair theorems. When a mate falls below
the deficit, the same defender **continues** using the next lemma. In
particular, the upper-pair response at a tied triangle node does not end
after one pick. Every opponent choice at these nodes is quantified over in
the Lean proofs; no principal variation is substituted for that obligation.

There is one important adaptive geometric step. In an equal-deficit orphan
state with lower pair10, if the opponent takes upper counter `c+1` with
`c>=18`, answer with **11 then c**, on the same turn. The endpoint is
`({z,10},z+10)`, drawn by the existing score-sum lemma. The strict inequality
`11<c+1-z` proves that the first response pick cannot already end the turn.
The small remaining even cases c14/16 and z6/7 are kernel-checked four-counter
leaves. Another small boundary handles b10/14/16/18 with five counters. The
three-counter triangle has three finite offset leaves. These eleven small
checks are explicit; no large game-tree lookup table is hidden in the theorem.

## Experiments

The C++ probe reuses `seven_pairs/slots.hpp` unchanged. It tests the initial
triangle response clauses against **every** opponent counter and records all
safe friendly first choices, rather than keeping only one favorable line.

| Core pairs | Supports | Opponent replies | Candidate failures |
|---|---:|---:|---:|
| one | 13 | 65 | 0 |
| three | 286 | 2574 | 0 |
| five | 249 | 3237 | 0 |
| total | 548 | 5876 | 0 |

All sampled roots were exact draws experimentally. These finite results
**do not prove the five-core-pair generalization** or that recursively using
only the initial reply clauses forever is safe. The formal proof above
covers exactly three core pairs, with auxiliary one-/two-/three-pair reserve
families and unbounded labels.

An independent literal-score implementation checks all5876 candidate
endpoints, all311 selected full root values (all one-/three-core-pair supports
and12 five-core supports), and2795 complete sets of safe first choices. It
explicitly checks the compulsory continuation in each two-pick response.

A separate graph starts at the actual deficit-four obstruction, forces5 and
the nine prescribed response clauses, then retains **all** non-losing friendly
choices and **every** opponent choice. It contains1574 states,1003 opponent
edges,2248 friendly edges,1486 continuing edges, and164 terminals (162 defender
wins and2 draws). Every state is independently compared with the literal
score evaluator. The JSON graph is an experimental artifact, not a Lean
certificate. The symbolic theorem supplies the formal guarantee independently.

No counterexample to this three-core-pair family was found; it is now proved.
No counterexample to the original Catch-Up conjecture is claimed.

## Verification, size, and next obligation

Reproduce from the downstream package directory:

```
python3 multi_turn/verify.py
```

The verification script requires a warning-strict complete build, fresh
source replay,17 public transitive axiom reports restricted to `propext`,
`Classical.choice`, and `Quot.sound`, old source/pin/hash checks, the bounded
experiments, and independent review. There are20 new theorems, including
three private helpers, all counted in benchmark.json. Source size includes
the supporting mathematics, not only a short final invocation. No native
proof computation, extra heartbeat budget, custom result axiom, dependency
upgrade, or binary Turing machine is introduced.

Fresh Lean elaboration and the transitive audit give the formal checking
cost. Interactive proof discovery was not timed. The C++ experiment has its
own generation timing; the independent Python replay also builds the
experimental graph, so that command's time mixes graph generation and
experimental checking and is not a pure certificate-checking measurement.

The next pair-count obligation is the five-core-pair triangle family. Start
with its **four-pair orphan reserves at deficits z or z+2**, z in{6,7},
created by the same mate replies. The current proof only closes the
corresponding two-pair states. The positive five-core samples justify this
test, not an induction assumption. The original interval conjecture and
binary-machine compilation remain open.
