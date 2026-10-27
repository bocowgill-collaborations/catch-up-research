# First-pair and failed-strategy atlas

Four source-preserving ports make earlier proof-search lessons available in the
maintained library. Their 67 public theorem declarations include structural
identities and kernel-reduced examples, not 67 new discoveries or a solution of
Catch-Up. The [verification record](../verification/atlas-ports.md) separates
source fidelity from proof checking. Original reports and archives are unchanged.

Write `P_N=Position({3,…,N},1)`. Values are current-mover-relative: a pick below
the deficit retains the mover; equality or overshoot switches players. Raw state
updates alone do not establish legal play.

## Adjacent-hole copying fails before the first repair

At `N=11, b=4, y=8`, the neighboring states are:

| State | Value | Nonlosing first picks |
| --- | --- | --- |
| `U = Position({2,5,6,9,10,11},1)` | draw | 2 (draw) |
| `V = Position({2,5,6,7,10,11},1)` | win | 5 (win), 10 (draw) |

The natural bijection fixes common counters and sends 7 to 9. Every nonlosing
right pick copies to a losing left pick. Preserving a right win and a left
nonloss forces different common picks, U:2 and V:5. Both switch to the opponent;
the new deficits are 1 and 4, and the unmatched sets are `{5,9}` and `{2,7}`.

This does **not** refute `V win → U nonloss`: U draws. It refutes the specified
copying rule. A sparse alternating-parity extension has a genuine loss/win jump,
so parity order cannot replace the interval hypotheses. A separate sparse-root
example has both neighbor replies losing while the distant reply 11 draws.

Formal source: [AdjacentHoleExchangeObstruction](../CatchUp/AdjacentHoleExchangeObstruction.lean).
Key theorems in `CatchUp.AdjacentHoleExchange` are
`safe_right_move_copies_to_loss`, `forced_first_repair_endpoints`,
`alternating_parity_jump`, and `parity_root_reply_eleven_draw`.

## First-pair descent must retain interval geometry

`CatchUp.FirstPairDescent.root_eq_pair` identifies P_N with deleting 1 and 2
from `{1,…,N}`. Each available first pick x≥3 catches, switches the player, and
leaves `Position({3,…,N}\{x},x−1)`. A hypothetical loss forces all those children
to win. Direct kernel proofs establish the bases P_7 and P_8 draw.

The sparse support `{3,7,9,14,17,20,29,34}` at deficit 1 loses, although its
minimum is 3, its effective total is even, and deleting 3 gives a winning
deficit-two shadow. Thus those hypotheses alone cannot justify a three-reserve
transfer. The support is not an interval.

A separate witness follows legal common prefixes `[5,7]` from two size-eight
states. At the reached bridges, the shadow's only winning pick is 8, but copying
8 loses in the actual game; actual pick 6 wins. Legal copied continuations give
completed protected-player margins −2 and 6, exposing an ownership conflict.
**The initial shadow in this prefix example draws.** This does not refute every
translator supplied with a strictly winning shadow-root strategy. The raw
two-pick reversal identity likewise promises no legality.

Formal source: [FirstPairDescentObstruction](../CatchUp/FirstPairDescentObstruction.lean).
Key theorems are `loss_forces_all_first_children_win`,
`no_geometry_free_three_reserve_transfer`, `bridge_legal_prefixes`,
`bridge_shadow_root_draw`, and `bridge_completed_copy_obstruction`.

## Shifted reply graphs are not tied opening graphs

Vertex a is an alternative first pick from deficit one. An edge a→b requires b
to be available, the child to be nonterminal, and b to be a winning reply from
`Position(S\{a},a−1)`. Vertices are not successive positions in a single play.

The module proves:

- A legal directed two-cycle can exist with its entire integer span present,
  including a witness whose deficit-one root loses.
- Sliding a cycle through an intermediate counter need not preserve its edges.
- On the intact interval `{3,…,7}`, winning edges need not decrease labels, and
  maximum vertex 7 has only one winning reply, 3.
- For any nonempty positive-counter support, a hypothetical deficit-one loss
  forces an outgoing edge at every vertex, hence a nonempty **closed directed
  walk**. No simple-cycle or acyclicity conclusion is asserted.

Adjacent reversed replies leave deficits 2 and 0, both switching players.
Nonadjacent reversal has different deficits and only one switch. A critical
continuation can invert rather than preserve a proposed companion edge.
Tied-root uniqueness therefore cannot be imported unchanged. The
[recovered maximum companion](reply-maximum-companion.md) is a different,
conditional tied-position result; its hypotheses remain essential.

Formal source: [ShiftedReplyCycle](../CatchUp/ShiftedReplyCycle.lean).
Key theorems are `no_loss_conditioned_local_span_exclusion`,
`interval_seven_no_max_companion`, `interval_loss_forces_closed_walk`, and
`critical_reply_inversion`. Raw reversal equations do not assert legal picks.

## The prepaid reserve envelope cannot initialize for N>7

After first pick a from P_N, let `S={3,…,N}\{a}` and `L=a−1`. The proposed
numerical envelope asks for an unpaired pool B⊆S and a natural budget D with

\[
|S\setminus B|\le2D,\qquad D+\sum B\le L,\qquad
L+D+\sum B\le x\quad\text{for every }x\in S\setminus B.
\]

For N≥7 and available a, this holds **if and only if N=7 and a=3**, without
parity or value assumptions. The proof uses the smallest paired counter to
force a=3 and B empty, then cardinality forces N≤7. The converse uses D=2.

This classifies one initialization envelope, not game outcomes. The separate
reserve-preservation strategy remains informal; the theorem excludes neither
eventual-entry strategies nor other invariants.

Formal source: [TurnReserveInitialization](../CatchUp/TurnReserveInitialization.lean),
`CatchUp.TurnReserve.budget_envelope_initialization_iff`.

## Remaining target

For N≥7 with even triangular total, the uniform first-pair draw still has separate
nonloss and nonwinning directions.
A new transfer must retain interval geometry, causal choices, every opponent
response, and first-catch turn legality. See the
[research handoff](../docs/research-handoff.md) for exact obligations and the
dependency-ordered verification backlog.
