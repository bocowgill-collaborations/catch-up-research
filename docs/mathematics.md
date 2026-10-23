# Sums, partitions and strategies

The arguments on this page are elementary **informal explanations**. They have not been added as new Lean declarations in this release. The existing [formal results](../results/) have their own precise statements and checks; the recovered [Parity module](../CatchUp/Earlier/Parity.lean) also proves the odd-effective-total obstruction under the game semantics.

## Why only N congruent to 0 or 3 modulo 4?

All counters end up in one player's score, so the final scores sum to

```text
T(N) = 1 + 2 + … + N = N(N+1)/2.
```

Equal scores require `T(N)` to be even. Examining the four possible remainders of `N` modulo 4 gives:

| N mod 4 | Parity of T(N) | Can final scores tie? |
| --- | --- | --- |
| 0 | Even | Yes |
| 1 | Odd | No |
| 2 | Odd | No |
| 3 | Even | Yes |

The empty game `N=0` draws. The open conjecture concerns every even-total interval, not a claim that odd-total games all favor the same player.

## Equal partitions exist in every eligible interval

For `N=4k`, group the counters into blocks of four consecutive integers. In a block `{m+1,m+2,m+3,m+4}`, the outside pair and inside pair have equal sums:

```text
(m+1)+(m+4) = (m+2)+(m+3).
```

Assign one pair to each player in every block. For `N=4k+3`, start with `{1,2}` versus `{3}` and partition the remaining four-counter blocks the same way. Thus an equal partition exists for every eligible `N`.

An equal partition can even be realized by a cooperative legal play. Assign each player one part, of total `T(N)/2`. P1 opens with one assigned counter. On a later turn, a player chooses only from their own assigned counters until catching the opponent. Those counters suffice: the opponent's score never exceeds the common target, while the player's score plus their unused assigned counters equals that target. If counters remain, the acting player has an assigned counter available; otherwise both players would already have reached the common target and nothing could remain. Both eventually finish at that target.

This proves the existence of a drawn play, not a defense. The opponent has no obligation to respect that partition. The [worked four-counter example](game.md) exhibits a losing opening that still admits a drawn line. The original paper also discusses the partition connection in §4.8 and its appendix: [Isaksen et al. (2015)](https://www.nealen.net/papers/catch-up-a-game-in-which-the-lead-alternates-2015.pdf#page=9).

## Why arithmetic still helps

A completed turn chooses a set of counters whose total catches the deficit, while all preparatory picks must stay below it. Therefore subset-sum information can constrain legal responses. The game-theoretic question is whether those responses remain safe against every reply.

Two useful verified results are:

- [IncompleteSubsumMass](../CatchUp/IncompleteSubsumMass.lean): for `r` distinct positive counters, an unattainable target between zero and their total forces `r(r+1)+2r ≤ 2·total+2`. This is an arithmetic restriction, with no game-value conclusion.
- [AlternativeSumDefense](../CatchUp/AlternativeSumDefense.lean): if every counter is at least `a>0`, `b` is present, a separate subset sums to `b`, and every counter is at most `b+a`, then the position at deficit `b` is nonlosing. The maximum bound and all subset hypotheses matter.

Total sum, parity, minimum, maximum and pair count alone do not determine the outcome: [AdviceFeatureCollision](../CatchUp/AdviceFeatureCollision.lean) certifies opposite values for supports sharing those features. Useful number theory must be connected to the actual turn structure.

## A basic counting perspective

For a fixed initial interval, [ReachableBounds](../CatchUp/ReachableBounds.lean) proves that every reachable remaining set is a subset of `{1,…,N}` and every normalized deficit is at most `N`. Counting those pairs gives the elementary upper bound `(N+1)·2^N` on distinct normalized state labels. Most labels need not be reachable. A fixed-player strategy representation also tracks whose turn it is.

This count helps explain memoization. It is neither a polynomial-time algorithm in the binary encoding of `N`, nor a lower bound on proof size. Counts of ordered picks, whole turns, terminal play sequences and merged states refer to different objects.
