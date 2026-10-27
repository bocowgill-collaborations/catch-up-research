# Verified finite two-buffer protocol — CU-L026

The archived September 28 controller is now ported into the ordinary-kernel
library. This updates the assurance of **CU-L026**, not its mathematical scope.
The interval conjecture and uniform adjacent-hole transfer remain open.

## Exact statement

Protect the fixed player `p1`, independently of whose turn it is. The roots are

```text
U = ({2,5,6,9,10,11}, deficit 1, p1)
V = ({2,5,6,7,10,11}, deficit 1, p1).
```

These are the archived adjacent-hole instance `N=11,b=4,y=8`, corresponding to
absolute initial scores `(0,1)` in each game. The theorem
`CatchUp.TwoBuffer.mandatory_protocol` proves `Protocol U V`, using the explicit
table and a twelve-pick checker budget. “Uniform” means all permitted adversarial
replies at these fixed roots, **not** all interval sizes or holes.

The constructors of [Protocol](../CatchUp/TwoBufferProtocol.lean) specify:

- Both games terminal: require the raw buffer test and
  `V.completedMargin p1 - 2 ≤ U.completedMargin p1`.
- Actual `p1` turn: choose one legal pick in the nonterminal actual game.
- Actual `p2` turn: cover every legal actual pick.
- Shadow `p2` turn: choose one legal pick in the nonterminal shadow game.
- Shadow `p1` turn: require a nonempty set of legal strictly winning replies
  and cover **every** such reply, not just a margin-optimal one.

The constructor selects the side before the universal move is revealed. It may
depend on the paired state reached so far. Every nonterminal step advances one
game by one pick. The finite checker consumes one budget unit per pick; its
zero-budget case accepts only when both games are terminal. No waiting or
fairness assumption is used. `run_check_sound` proves acceptance constructs
this inductive protocol for any policy, roots and natural budget.

The strict-win filter is exactly `¬CanAvoidLoss p2 (V.afterPick x)`, proved by
`shadow_good_iff` from the already verified classifier. It restricts the supplied
shadow strategy; it is **not** a structural score-debt invariant. Universal
branching covers all locally strict-win-preserving choices, including those
made by history-dependent supplied strategies. No theorem extracting a separate
executable strategy object from `Protocol` is added in this port.

## Buffer and payoff conventions

At every paired node, each raw set difference has cardinality at most two:

```text
card(U.remaining \ V.remaining) ≤ 2
card(V.remaining \ U.remaining) ≤ 2.
```

This permits four unmatched counters in total; it is not a bound of two on their
union, or on intermediate score debt. Every child again carries the buffer
requirement, including leaves.

An early-terminal state's stranded counters remain in its `remaining` field.
Completion awards their payoff to the trailing player without an erase step.
Immediate erasure would invalidate this particular policy's buffer claim.
Equality switches the mover; a below-deficit pick retains it. Existing game
transitions and completed-margin definitions are unchanged.

The formal conclusion is the protocol and its terminal two-point comparison.
It is not a new interval draw theorem, a general nonloss transfer theorem, an
optimal-margin claim, or a certificate-size result. Archived scalar-bound and
parametric two-pick repair proofs remain outside this port.

## Evidence, sources and reproduction

[TwoBufferMandatory](../CatchUp/TwoBufferMandatory.lean) contains 76 explicit
nonterminal table entries. `mandatory_policy_checked` checks the root by
`decide +kernel`; `mandatory_protocol` applies the generic soundness theorem.
Neither Python, synthesis nor native evaluation is a proof premise. All four
public theorems are named axiom-audit endpoints; the all-public audit also
checks the imported/generated theorem closure.

The [source manifest](../verification/two-buffer-port.json) pins the original
Git blobs, branch, commit, archived inputs and ported hashes. Its checker
reconstructs the two sources and compares every Lean row, in order, with the
normalized retained JSON policy. It checks compatible actions when histories
collapse to the same normalized state. Only `exchangeLeft` and `exchangeRight`
are extracted from `AdjacentHoleExchangeObstruction`; its other statements do
not inherit this port's assurance.

The already supported [Python replay](../computation/experiments/earlier-campaign/two-buffer/)
separately checks 87 JSON nodes and 17 terminal histories, ownership, universal
edges and branch margins. Its evidence is computational, distinct from the new
kernel proof. Original reports and historical ledger labels remain unchanged;
see [the verification note](../verification/two-buffer-port.md) for current
checks and exact adaptations.

From the repository root with the pinned dependencies available:

```sh
python3 scripts/check_two_buffer_port.py
lake --wfail build
python3 scripts/check_axioms.py
python3 scripts/check_collection.py
```

The default build includes both modules. The collection check includes source
reconstruction, table matching, mutation controls and the Python replay.
