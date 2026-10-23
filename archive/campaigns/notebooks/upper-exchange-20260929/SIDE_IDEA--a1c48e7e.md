> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Independent conceptual search: unformalized side idea

This is not part of the certified result. The helper searched independently of
the root's exact-sum tree, returned this candidate, and stopped. No source edits
or further research assignments were made to it.

Let min(T)>=2, M=sum(T), and a>M+d. A dominant adjacent pair {a,a+1}
appears to implement the following terminal utility for play on T:

- At empty T and deficit e: win for e=0, draw for e=1, loss for e>=2.
- At nonempty T, maximize over small picks, preserving the mover below e and
  negating the child outcome at or above e. Do not prune merely because T alone
  cannot catch: the large pair is still present in the actual game.

Candidate argument: taking either large counter prematurely loses. The opponent
can take all of T before the sibling, since its deficit exceeds M throughout.
The eventual empty-position deficit for the original mover is M+d+1 or M+d-1,
positive because T is nonempty and min(T)>=2. The inequality a>M+d persists
after each small pick because (M-x)+abs(d-x)<=M+d.

This is a change in terminal utility, NOT neutrality. It does not rescue a fixed
matching or prepaid-reserve mechanism and does not prove Target A.

For N=4k+3 with b,y odd, the continuing response y-1 to opening y leaves
[2,N] minus the two actual adjacent pairs {b-1,b} and {y-1,y}, at deficit1.
This is a union of 2k-1 actual adjacent pairs. The proposed nonloss invariant
for arbitrary odd unions of such pairs remains unproved and unrefuted here.
There is no permission to use it as a theorem.

## Reproducible diagnostic (not a theorem)

The helper evaluated only the following modified-leaf instance, in addition to
a few nondecisive small probes. Its reported result was draw, 24,733 cached
states, 0.023 seconds. This did not resolve the invariant. Exact encoding:

```python
from functools import cache
T = (3,4,6,7,15,16,58,59,66,67,77,78,82,83,97,98)
@cache
def g(s, d):
    if not s:
        return 1 if d == 0 else 0 if d == 1 else -1
    return max((1 if x < d else -1) * g(tuple(t for t in s if t != x), abs(d-x))
               for x in s)
print(g(T, 1), g.cache_info())
```

This file preserves the idea and its precise gap; it makes no audited proof claim.
