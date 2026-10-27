# A formal finite two-buffer controller

The five archived modules below are now source-preserving, maintained Lean ports.
They add 34 public theorem declarations. **Catch-Up remains open.** The main
certificate covers one complete finite instance, not a uniform adjacent-hole
translator. See [provenance and reproduction](../verification/controller-ports.md).

## What is certified

Protect player `p1` in the paired initial states

```text
U = ({2,5,6,9,10,11}, deficit 1, p1)
V = ({2,5,6,7,10,11}, deficit 1, p1).
```

`CatchUp.TwoBuffer.mandatory_policy_checked` checks the explicit policy with
budget 12. `mandatory_protocol` uses the proved `run_check_sound` theorem to
construct `Protocol U V`. Every step removes a counter from the selected game;
there are initially twelve counters across the two games.

The protocol is an inductive finite causal tree. Its constructors enforce:

| Turn advanced | Who chooses the pick | Branches required |
| --- | --- | --- |
| Actual `p1` | Controller | One legal pick |
| Actual `p2` | Adversary | Every legal pick |
| Shadow `p2` | Controller | One legal pick |
| Shadow `p1` | Supplied strictly winning strategy | Every legal strict-win-preserving pick; the reply set must be nonempty |

The selected game and action are fixed before the universal pick is revealed.
The shadow filter is exactly `¬CanAvoidLoss .p2 (v.afterPick x)`, not a
current-mover-relative win test with an implicit player switch. A pick below
the deficit retains its mover; equality switches. The protocol cannot advance
a terminal game or silently continue a turn after catching up.

At every state, including terminal states, both raw set differences satisfy
`card(U.remaining \ V.remaining) ≤ 2` and the reverse bound. Stranded counters
at early termination remain in these fields; they are not discarded to make
the buffer bound pass. At the final pair, both games are terminal and

```text
V.completedMargin p1 - 2 ≤ U.completedMargin p1.
```

This covers every actual opponent choice and every permitted shadow-strategy
reply, not just one favorable branch. The supported replay checks all five
actual second picks and both continuations after actual prefix `[2,11]`.

## Completion, scalar bounds and local repairs

The existing [completed-margin foundation](../CatchUp/Earlier/CompletedMargin.lean)
notionally awards all remaining counters to the trailing player at early
termination and proves that this preserves the outcome. Margins refer throughout
to fixed `p1` score minus fixed `p2` score. For these roots, the effective totals
are 44 and 42. The new parity lemmas also prove evenness for the stated general
punctured-interval family. A positive completed margin in the even-total shadow
is therefore at least two. The terminal comparison explains the intended
nonloss transfer; it does not construct a uniform translator.

`mandatory_scalar_bounds` gives matching enforceable upper and lower completed
margin bounds: zero in U and two in V. `protocol_necessary_bound` says that an
actual-opponent upper bound `a` and positive shadow-protected lower bound `b`
require `b-2 ≤ a` for any protocol. Here that gate passes with equality. The
necessary bound is not a sufficient construction.

`TwoPickDebtRepair` proves a symbolic repair for every natural `k`. The actual
preparation support is `{k+3,k+4,2k+5,2k+6}` at deficit `2k+6`, mover `p1`.
The legal completed turn `[k+3,2k+5]` leaves the common pair `{k+4,2k+6}` at
deficit `k+2`, mover `p2`. In the shadow setup, a bridge pick and a forced
strict-winning reply leave that pair at deficit `k+4`, mover `p2`. Under the
proved inequalities, copying both picks from the pair produces actual nonloss
and an exact terminal margin difference of two. Both possible opponent picks
are covered, including the `k=0` boundary.

At `k=2`, the raw prefix identities identify actual `[2,11]` and shadow `[5,2]`
with the preparation roots. Those identities alone are not legality theorems;
the preparation-turn/trace proofs and full-instance protocol supply the needed
legal transitions. This local parameterized gadget is not closure of a family
containing all original interval roots.

`ScoreDebtRepairCertificates` also retains useful negative results: one legal
copied suffix gives actual margin 2 and shadow margin 10, violating the proposed
two-point bound; extending a local maximum-pick rule globally gives actual
margin -2. Neither refutes the controller above or Catch-Up.

## Source map and assurance

| Module | Public theorems | Main contribution |
| --- | --- | --- |
| [ScoreDebtRepairCertificates](../CatchUp/ScoreDebtRepairCertificates.lean) | 7 | Parity, legal prefixes, forced bridge and failed policies |
| [TwoBufferProtocol](../CatchUp/TwoBufferProtocol.lean) | 2 | Protocol semantics, exact shadow filter and checker soundness |
| [TwoBufferMandatory](../CatchUp/TwoBufferMandatory.lean) | 2 | Kernel-checked policy and mandatory-instance protocol |
| [TwoPickDebtRepair](../CatchUp/TwoPickDebtRepair.lean) | 15 | Parametric preparation and copied-pair repair |
| [CompletedMarginBounds](../CatchUp/CompletedMarginBounds.lean) | 8 | Enforceable margins, necessary scalar bound and root bounds |

The original statements, proofs and docstrings are unchanged; only imports and
repository indexing attributes are adapted. Finite proof checks use
`decide +kernel`, not native computation. Named and full transitive axiom audits
allow only `propext`, `Classical.choice` and `Quot.sound`. No unproved Catch-Up
statement or Python solver answer is a proof premise.

The [unchanged JSON replay](../computation/experiments/earlier-campaign/two-buffer/)
retains absolute scores and persistent ownership histories. The Lean table keys
only the normalized states, including mover and deficit; it does not retain full
histories. A cross-language check exports the actual Lean table and matches all
reachable nonterminal replay states. Its 76 rows have 74 distinct normalized
keys, with identical actions at the two repeated keys. The replay covers 87
nodes and 17 terminal histories, with independent legality, ownership, margin
and adversarial-branch checks. Policy and source mutation controls must fail.
These checks complement, and are not premises of, the kernel proof.

## What remains

The port constructs the stated finite `Protocol`. It adds no separate general
extraction theorem taking an arbitrary supplied winning strategy to an ordinary
actual-game strategy. Such a semantic bridge would need explicit initial
strict-win/even-total hypotheses and a causal projection argument. Do not cite
`mandatory_protocol` as that stronger theorem; actual-root nonloss is already
certified separately and by the scalar bounds.

The main research gap is still a structurally defined, parametrically closed
transfer family covering the required adjacent-hole positions, with legal
first-catch turns, every adversarial response and well-founded progress. The
full lower-ray nonloss obligations and first-pair draw remain unresolved. See
the [current handoff](../docs/research-handoff.md) and [open questions](open-questions.md).
