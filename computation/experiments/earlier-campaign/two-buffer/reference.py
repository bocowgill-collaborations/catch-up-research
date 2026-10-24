"""Fixed-player score recurrence and persistent ownership states.

Extracted from the earlier independent replay; no synthesis is imported.
Player 0 is protected, equality switches, and early completion awards
all remaining counters to the trailing player. See bundle provenance.
"""
from dataclasses import dataclass
from functools import cache


@cache
def absolute_value(remaining, score_one, score_two, mover):
    """Independent fixed-player recurrence, without normalized gaps or negation.

    Player one maximizes and player two minimizes. The answer is always from
    player one's perspective. A tie after a pick switches the mover.
    """
    if not remaining:
        return (score_one > score_two) - (score_one < score_two)
    scores = (score_one, score_two)
    if scores[mover] + sum(remaining) < scores[1 - mover]:
        return -1 if mover == 0 else 1
    children = []
    for x in remaining:
        updated = list(scores)
        updated[mover] += x
        next_mover = 1 - mover if updated[mover] >= updated[1 - mover] else mover
        children.append(absolute_value(tuple(y for y in remaining if y != x),
                                       *updated, next_mover))
    return max(children) if mover == 0 else min(children)



@dataclass(frozen=True)
class State:
    remaining: tuple
    scores: tuple
    mover: int
    owners: tuple = ()

    def terminal(self):
        return (not self.remaining or
                self.scores[self.mover] + sum(self.remaining) < self.scores[1-self.mover])

    def pick(self, x):
        assert not self.terminal() and x in self.remaining
        scores = list(self.scores)
        scores[self.mover] += x
        mover = 1-self.mover if scores[self.mover] >= scores[1-self.mover] else self.mover
        return State(tuple(y for y in self.remaining if y != x), tuple(scores), mover,
                     self.owners + ((x, self.mover, 'pick'),))

    def complete(self):
        assert self.terminal()
        scores = list(self.scores)
        scores[self.mover] += sum(self.remaining)
        owners = self.owners + tuple((x, self.mover, 'completion') for x in self.remaining)
        assert len({x for x, _, _ in owners}) == len(owners)
        return scores[0]-scores[1], owners
