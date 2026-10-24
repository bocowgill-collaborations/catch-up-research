# A conditional maximum-reply companion

**CU-R001**, related to historical [CU-L011](legacy-findings.md#cu-l011--tied-maximum-companion-claim).
This is a recovered conditional theorem, not an unconditional reply-graph result
or a solution of the interval conjecture.

Let `S` be any finite set of natural counters and `c∈S` bound every member of `S`.
Write

```text
P(a,c) = ((S erase a) erase c, c−a).
```

The value is from the player to move, trailing by the displayed deficit.
An edge `c→a` means `a∈S`, `a≠c`, and picking `a` after opening with `c`
has outcome WIN for the player making that reply. It does not mean that opening
`c` is winning for its opener. See [ReplyEdge](../CatchUp/Earlier/ReplyDigraphReduction.lean).

Assume that, **for every `x∈S` with `x<c`, `P(x,c)` is nonempty and catchable**:
its remaining total is at least `c−x`. If `c→a` is an edge, there is `b∈S` with
`b≠a`, `b<c`, and edge `c→b`. Moreover, picking `b` in `P(a,c)` wins and picking
`a` in `P(b,c)` wins. Thus an outgoing edge from this maximum cannot be unique
under those hypotheses.

The two public theorems in [ReplyMaximumCompanion](../CatchUp/ReplyMaximumCompanion.lean)
are `CatchUp.reply_edge_from_max_has_companion` and
`CatchUp.reply_edge_from_max_not_unique`. No positivity, parity, interval,
smaller-instance or conjecture premise is added. The explicit nonempty and
catchability premises must not be silently removed.

## Why the argument works

Because `a<c`, the first reply is a same-player continuation and leaves `P(a,c)`.
The edge says its value is WIN. Nonemptiness and catchability allow the exact
best-move recurrence to supply a winning next pick `b`. That pick is in `S`
and distinct from both removed counters, hence below `c`.

The existing cross-pick identity equates the outcomes of picking `b` in `P(a,c)`
and `a` in `P(b,c)`. Apply it in whichever order `a,b` occur. The second pick
therefore also wins. Catchability at `b` permits the recurrence in the other
direction, establishing that `P(b,c)` wins and hence `c→b`.
All opponent play is accounted for by the verified optimal-value semantics;
this is not an argument from one play sequence.

## What was recovered

A local ignored build cache retained `catch_up.ReplyMaximumCompanion.olean`
and its declaration-location metadata after the source checkout disappeared.
The [archived bytes](../archive/recovered/reply-maximum-companion/) contain six
source-level declarations: two definitions, two private helpers and these two
theorems. Four generated declarations bring the kernel replay total to ten.
Ten declarations are not ten new mathematical results.

All ten original declaration terms are freshly kernel-checked against the
current library. The reconstructed readable source is also independently built;
all four public types and both definition bodies match the cached expressions
up to Lean definitional equality. Both headline theorems use only `propext`,
`Classical.choice` and `Quot.sound`, with no native proof shortcut.

This does **not** recover the original tactic text or establish identity with
`ReplyMaximumCompanion_reply_digraph_global_20260812.lean`, whose reported
source hash remains unmatched. It also does not verify the historical bounded
observations, shifted deficit-one exclusion or a stronger unrestricted claim.
The historical ledger stays intact; this later recovery supplies a precisely
scoped additional building block. See [provenance](../verification/reply-maximum-companion.json)
and [reproduction and review](../verification/reply-maximum-companion.md).
