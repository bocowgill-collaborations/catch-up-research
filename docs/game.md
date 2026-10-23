# A worked introduction

Start with the counters `1,…,N` and two zero scores. Player one takes exactly one counter. Thereafter, a player takes at least one counter and continues until catching or passing the opponent. Equality ends a turn. If catching is impossible, that player receives the remaining counters and scores are compared.

## A drawn game can contain losing choices

Consider `{1,2,3,4}`. One possible play is:

| Step | Action | Scores P1 : P2 | What happens next? |
| --- | --- | --- | --- |
| 1 | P1 opens with 3 | 3 : 0 | P2 acts |
| 2 | P2 takes 2 | 3 : 2 | P2 is still behind and must continue |
| 3 | P2 takes 4 | 3 : 6 | P1 acts |
| 4 | P1 receives the remaining 1 | 4 : 6 | P2 wins |

The game on `{1,2,3,4}` is nevertheless drawn under optimal play. These are the opening outcomes, measured for P1 and allowing optimal play afterwards:

| P1 opening | Outcome for P1 |
| --- | --- |
| 1 | Draw |
| 2 | Draw |
| 3 | Loss |
| 4 | Loss |

A drawn line after opening 3 also exists: P2 takes 1 and then 4; P1 takes 2. Both finish at 5. This shows why one favorable play sequence cannot certify a strategy.

These are reproduced small exact calculations, not additional Lean certificate declarations. Check all four opening outcomes yourself:

```sh
python3 computation/explore.py --initial 4
```

## A turn can contain several decisions

Suppose the remaining counters are `{2,4,7}` and the acting player trails by 3. Taking 2 leaves the same player acting, now behind by 1. Taking 4 instead ends the turn and leaves the other player behind by 1.

```sh
python3 computation/explore.py --remaining 2 4 7 --deficit 3
```

The output reports every first pick, whether the player continues or swaps, and the resulting outcome. `child_outcome` uses the child's acting-player perspective; `pick_outcome` uses the perspective before the pick. These differ in sign exactly when the turn changes players.

## Four edge cases

- At tied scores, a nonempty game still requires a pick. A tie before a turn does not end the game.
- Reaching equality **after** a pick ends that turn.
- If remaining total equals the deficit, taking all remaining counters catches exactly and draws.
- If remaining total is smaller than the deficit, the acting player loses even after receiving everything.

The explorer uses exact integers and the ordering win > draw > loss. Its default limits are 10 seconds and 200,000 newly examined states, with at most 20 counters. Exhaustion reports `incomplete` and exit code 2. It is a small research/teaching tool; it does not issue a Lean certificate.

Next: [the conjecture's number theory](mathematics.md), [the glossary](glossary.md), or [the formal rules](../CatchUp/Reference.lean).
