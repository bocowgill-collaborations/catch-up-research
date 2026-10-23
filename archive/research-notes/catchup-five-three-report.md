> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.FiveThree](../../CatchUp/FiveThree.lean).

# Five-pair deficit-three invariant: certified counterexample

The proposed arbitrary-support reserve invariant is false. Lean proves

```
Position.value ({4,5,7,8,14,15,23,24,31,32}, 3) = Outcome.win.
```

The pairs have starts `(4,7,14,23,31)`, satisfying minimum four and all the
required separation inequalities. Taking14 is a winning move. It leaves

```
Position.value ({4,5,7,8,15,23,24,31,32}, 11) = Outcome.loss.
```

`not_uniform_five_three` formally negates the quantified proposed theorem.
No claim that this is the least counterexample is made.

This refutes an **auxiliary normalized-state invariant**, not the original
Catch-Up conjecture C. Neither set is an initial interval game. The source also
proves the root win in the literal absolute-score reference evaluator,
`valueAux S 0 3 false = win`; `false` means a regular post-opening turn. It does
not assert any value for an original interval or establish `¬C`.

The witness is not a union of the canonical even-start pairs used by the
interval strategy:7 is present while its even-start mate6 is absent. Therefore
the explicitly restricted canonical reserve claim remains open. The earlier
uniform deficit-one theorem and finite N15 results remain intact.

## Formal argument and every opponent reply

`CatchUp/FiveThree.lean` uses the existing normalized evaluator and its proved
reference correspondence. `sparse_child_loss` uses `decide +kernel`; the kernel
replays exact outcome optimization, with no native-only or external solver
answer admitted as an axiom. `sparse_five_pairs_win` applies the existing
catching-move theorem to14. `sparse_every_reply_loses` quantifies over **every**
legal pick at the losing child, not a sample of favorable lines. Its recursive
outcome includes complete optimal continuation.

For the child at deficit11 the nine immediate replies are:

| Pick | Same player continues? | Move outcome for defender |
|---|---|---|
|4|yes|loss|
|5|yes|loss|
|7|yes|loss|
|8|yes|loss|
|15|no|loss|
|23|no|loss|
|24|no|loss|
|31|no|loss|
|32|no|loss|

The independent absolute-score implementation reproduces the root, child,
and every row. The separate experimental winning policy expands every
opponent decision throughout the game:453 distinct nodes,287 opponent edges,
337 friendly witnesses,229 continuing edges, and38 strictly winning terminals.
The checker rejects a drawn terminal for this strict-win task. Every visited
state is compared with the independent absolute-score evaluator. The policy
JSON is an experimental artifact; it is not presented as a Lean-checked JSON
certificate. The Lean value theorem is the formal assurance.

## A surviving unbounded structural theorem

`upper_move_nonwin` proves that every upper-counter pick is nonwinning at
deficit three for **arbitrary** five separated adjacent pairs, minimum four.
If the mover takes`u+1`, the defender takes`u`. This is legal and catches;
it leaves the original mover four pairs at deficit two. The existing uniform
four-pair nonwinning theorem proves that the defender avoids loss. All five
upper picks are included; there is no bound on magnitudes or gaps.

`five_three_win_iff_lower_loss` consequently proves the exact equivalence

```
five-pair value at deficit3 is win
  iff some lower counter x leaves a losing child at deficit x-3.
```

This narrows the repaired claim to five specific lower-pick orphan obligations.
The witness uses the lower counter14, consistent with this theorem.

## Completed checks and reproducibility

Run from `research/catchup`:

```
python3 five_three/verify.py
```

The completed verification checks prior source hashes and pinned reference
sources, the Lean/Mathlib versions, a warning-strict full downstream build,
fresh proof-source elaboration, ten transitive axiom audits, independent
absolute-score reproduction, full adversarial policy expansion, and the
checkpointed targeted even-start experiment. All passed. The axiom lists
contain only `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`,
custom result axiom, unfinished-conjecture dependence, or native evaluation
occurs in the formal result.

The package remains Lean4.27.0 and Mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900`, with all source pins in
`SOURCES.json` and `benchmark.json`. Reference definitions and earlier proof
files are unchanged. The pre-existing high-level search-halting equivalence
was re-audited; no binary machine or machine-state count was produced here.

Each verification subprocess has a120-second process-group bound. Discovery
and test scripts also have their own explicit limits. The original targeted
arbitrary-support probe found the witness after163 shapes and1620 prior
opening-reply checks. A separate checkpointed test completed436 targeted
**even-start** shapes and4360 reply checks, with no wins. These are bounded
computations; they prove no universal canonical claim. An initial uncheckpointed
exhaustive even-start attempt hit its45-second cap, so no completed-range or
outcome assertion is taken from it. See`failed_attempts.md`.

Fresh-context independent review accepted the mathematics, legal moves,
perspective changes, complete continuation coverage, and precise scope. Its
request for a reproducible companion to`independent.json` was addressed by
`independent.py`, which is included in verification. Model review is separate
from Lean's checks.

## Next precise obligation

Retire the false arbitrary-support deficit-three invariant. For five
separated **even** starts`a_i≥4`, put`S=⋃ᵢ{a_i,a_i+1}` and attack

```
for every lower counter x in {a_1,...,a_5},
  Position.value (S.erase x, x-3) ≠ loss.
```

The new equivalence makes this exactly the remaining canonical five-pair
nonwinning claim. The restriction comes from the interval strategy's actual
pair geometry; it is not an unexplained exception list. The known even-start
four-pair deficit-four obstructions and all of their opponent replies must
remain covered. The436 targeted tests justify investigating this statement,
without presuming its truth.

## Proof-size and checking record

The new formal sources total7,744 UTF-8 bytes and
7 theorems, including the child evaluation, quantified
refutation, reference bridge, and supporting structural results. All imported
local proof support is separately counted:174,839 bytes.
Pinned Mathlib/Lean are external library dependencies. The new proof directly
imports`DeficitTwo`; it does not depend on the larger dense three-pair proof or
finite N15 tied tables. New compiled modules total
2,084,744 bytes. The experimental policy JSON is
16,376 bytes and is separately labelled as such.

OnmacOS-26.6.2-arm64-arm-64bit with16 logical CPUs, fresh proof replay took
15.98s. All recorded verification commands totaled
49.97s. Maximum individual child RSS
observed during the run was
8,672,624,640 bytes,
not aggregate RSS. The full per-command times, hashes, sizes, and completed
experimental scopes are in`benchmark.json`. Discovery time is reported
separately where measured; interactive proof development was not timed.

These measurements give an upper bound for this explicit auxiliary
counterexample proof. They are not a proof-size lower bound, a minimality
claim, or a size claim for a proof or disproof of C. No compact universal
Catch-Up proof has been established.
