> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.NearRepair](../../CatchUp/NearRepair.lean).

# Adaptive repair of the reached orphan decision

For every even q >= 42, the defender can avoid loss at the decision reached
after picks `[6,13,q+1]` in `FourOrphan.start q`. Its explicit normalized
state is

```
remaining = {7,10,11,18,19,20,21,40,41,q}
deficit = q-7
player to move = Player2.
```

`CatchUp/NearRepair.lean` proves the following single adaptive response,
using the existing completed-turn and strategy-semantics API:

| even q | defender's ordered completed turn | opponent's endpoint |
|---|---|---|
| 42 through 56 | 11,20,19 | `{7,10,18,21,40,41,q}`, deficit `57-q` |
| 58 through 96 | 10,19,21,41 | `{7,11,18,20,40,q}`, deficit `98-q` |
| 98 | 7,10,11,21,41,98 | `{18,19,20,40}`, deficit 97 |
| at least 100 | 10,40,41,q | `{7,11,18,19,20,21}`, deficit 98 |

These are whole turns by Player2. The preparation sums are respectively
31,50,90,91, each **strictly** below its initial deficit. The last pick
reaches or exceeds that deficit. In particular, equality in the old far
preparation at q=98 ends the turn before the intended extra pick of98;
the new boundary preparation is90 instead of91.

## What is proved

`adaptive_turn` proves legality, compulsory continuation, turn completion,
and the exact endpoint for every even q >= 42. The first endpoint draws
for all eight eligible low-range cases; the second is nonwinning for all
twenty eligible middle-range cases. These claims use **28 finite kernel
game computations**, with at most seven counters, through the existing
executable evaluator and its proved correspondence. They are not described
as purely arithmetic or as a new arbitrary-label invariant.

The q=98 endpoint draws by the existing general score-sum theorem: its
remaining total is exactly97. The q >= 100 endpoint loses because total96
is smaller than deficit98; its turn proof is reused from
`FourOrphan.uniform_far_turn`. There is no finite test extrapolation in
assembling the unbounded result: every even q >= 42 falls into one of these
proved cases.

`adaptive_repair` proves `CanAvoidLoss .p2 (reached q)`.
`every_opponent_turn_safe` explicitly quantifies over **every** legal
complete opponent turn from the selected endpoint, preserving that
guarantee. `uniform_reached_nonloss` connects the guarantee to the minimax
value. `uniform_reference_nonloss` states the identical non-loss under the
frozen literal `valueAux` score semantics. These theorems do not depend on
the unfinished upstream conjecture or on external solver output.

The old ordinary mate q remains a proved strict loss at this decision for
every q >= 42. The repaired response therefore eliminates that diagnosed
strategy failure throughout its even-q embedding. It does **not** establish
the five-core triangle root's value against every earlier choice, a general
five-core support theorem, any of the other three four-pair orphan
invariants, or original C. No binary Turing machine is constructed here.

## Independent experiments and every opponent reply

The C++ probe reuses `seven_pairs/slots.hpp` unchanged and runs exactly the
29 requested even q values plus q=100 as a control. It records all300 first
choices and all2447 non-losing completed-turn sets, each with its final
counter and exact endpoint. An independent literal-score evaluator checks
all14692 legal completed-turn sets, including equality stopping, and compares
the entire safe set with the recorded output. Thus a missing safe alternative
or a falsely reported alternative is detected.

The chosen policy's endpoints retain all711 ordered complete first opponent
turns, including595 with continuing picks. All are replayed with literal
scores and retain a non-losing continuation for Player2. The q=100 control
ends in a terminal loss for Player1, so it has no opponent move.

The experimental strategy forest thereafter retains every opponent pick at
every depth and **all** non-losing friendly choices, with actual turn
ownership. It has3555 distinct states,2358 opponent edges,5117 friendly
edges,3754 continuing edges,256 defender-winning terminals and2 drawn
terminals. Every state is independently compared with the literal evaluator.
A separate local validator ignores stored values and checks legal transitions,
complete opponent branching, nonempty friendly choices, strict decrease of
the counter count, and non-losing terminal outcomes. Corruptions removing an
opponent branch, inserting an illegal move, or creating a circular child
link are rejected. Continuing the old turn after equality at q=98 is also
rejected.

The Python forest/checker is experimental, not a Lean-certified certificate
checker or a proof premise. Formal assurance comes from the independent
Lean proofs above. Experimentally, the reached node's optimal outcome is
draw at q=46,50,98 and win at the other tested values. Only the uniform
non-loss is claimed as a new formal root result; no strict-win uniform
claim or optimal-draw theorem is inferred from these observations.

## Reproduction, proof size, and remaining scope

From the downstream package directory:

```
python3 near_repair/verify.py
```

The final gate requires a warning-strict library build, a fresh source
replay, all12 public transitive axiom reports restricted to the standard
`propext`, `Classical.choice`, `Quot.sound`, unchanged prior source and solver
hashes, the pinned Lean4.27.0 and Mathlib versions, independent replay, and
a read-only mathematical review. No native-only proof, custom result axiom,
heartbeat increase, or dependency upgrade is introduced.

The benchmark counts all15 new supporting theorems (three private), the
adaptive definitions, all new source bytes, reused local proof sources, and
compiled modules. Finite computation remains part of the proof's checking
cost even though the source is short. The strategy forest serialization is
counted separately and is not the formal certificate. Generation and checking
costs are separated where measured; interactive discovery time is unmeasured,
and the independent replay also generates the forest. No proof-size
minimality or lower bound is asserted.

The next useful test is to transfer the adaptive response mechanism to
held-out five-core triangle supports, retaining every root opponent choice.
The present result closes one unbounded reached-decision family, with four
fixed core pairs. A transfer needs a new mathematical invariant rather than
an inference from the finite endpoint computations here.
