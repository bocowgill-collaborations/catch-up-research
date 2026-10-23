# Openings, replies and the draw conjecture

The library already distinguishes three different questions: does the root draw, does a specified opening draw, and does **every** opening draw? This guide explains the existing theorems; it does not prove a uniform interval strategy.

## Why a winning opening is unique

Suppose two distinct openings `a < b` both win for P1. P2 must then lose after either opening. After opening `a`, consider P2 taking `b`: the turn switches and leaves P1 the support with both counters removed, at deficit `b-a`. After opening `b`, consider P2 taking `a`: P2 continues on exactly the same support and deficit. That continuation cannot be both winning and losing for its acting player.

If P2 cannot catch after opening `b`, the remaining total after deleting `a` is smaller than `b-a`; the common continuation is directly losing. The [Lean proof](../CatchUp/WinningOpening.lean) handles this boundary too, for arbitrary finite supports. The uniqueness result was already reported in [von Stengel's public 2019 abstract](sources.md); it is not a new discovery of this collection.

The same exchange gives the existing identity `move_outcome_after_opening_comm`: swapping the first two distinct picks negates the outcome from the respective second picker's perspective. It does not assume that picks alternate players. See [DrawOpening](../CatchUp/DrawOpening.lean).

## A drawn root versus every opening drawing

For a nonempty support, `value_eq_draw_iff_exists_draw_after_opening` proves:

```text
The root draws  iff  some opening leaves a drawn continuation.
```

The reverse direction is a theorem specific to this game, using the opening exchange. In a general minimax game, one drawn child alone would not rule out another winning child.

`EveryOpeningDraw S` is stronger: all legal openings leave drawn continuations. A drawn root need not have this property. Small exact calculations give:

| N | Openings that draw |
| --- | --- |
| 3 | 1, 3 |
| 4 | 1, 2 |
| 7 | 1 through 4 |
| 8 | All |
| 11 | All except 10 |
| 12 | All |

These rows are reproducible computations, not a proof of an infinite pattern. For example, run `python3 computation/explore.py --initial 12` and inspect every `pick_outcome`.

## The connection to pair deletion

[ReplyDigraphReduction](../CatchUp/Earlier/ReplyDigraphReduction.lean) proves `every_opening_draw_Icc_iff_every_pair_neutral`: for **N >= 3**, every opening draws exactly when every pair of distinct initial picks has a drawn continuation. Catchability of every opening is proved at this threshold.

For `1 <= a < b <= N`, the normalized continuation is precisely:

```text
pairDeletionPosition N a b = ( {1,...,N} without a and b, b-a ).
```

The second pick may continue P2's turn. Reversing its order changes the perspective, while draw is unchanged. Thus a proposed all-opening theorem can be investigated through the entire pair-deletion family. Proving that family uniformly remains open; this equivalence is not a new solution to the conjecture. The [lower-ray reduction](../CatchUp/PairDeletion.lean) asks for weaker, explicitly stated hypotheses sufficient for the original root-draw target.

## Reachable positions need not draw

In N=8, the legal prefix P1: `3`, P2: `1,2` reaches tied scores with counters `{4,5,6,7,8}` and P1 acting. That position is winning via `4`, despite admitting a drawn play. Check it with:

```sh
python3 computation/explore.py --remaining 4 5 6 7 8 --deficit 0
python3 computation/explore.py --remaining 5 6 7 8 --deficit 4
```

The second command covers all four opponent replies after `4`. This does not refute the N=8 draw: P2 need not choose the displayed prefix. An [archived five-counter argument](../archive/catch_up/FiveConsecutiveTrap.lean.txt) proposes a parametric winning family and reachable traps for every N=4k, k>=2. It is source-only in this collection and requires a port, build and axiom audit before being promoted to the verified library.

A useful strategy invariant must survive the selected friendly choices and every opponent reply. It need not label every legally reachable position as drawn.
