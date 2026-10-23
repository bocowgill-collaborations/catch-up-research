#!/usr/bin/env python3
"""Bounded exhaustive opponent-turn tests of a partial score-balancing rule.

No solver selects a reply. Missing replies are UNCOVERED, never draws/losses.
The subset test is exact for the encoded single completed turn, not a strategy.
"""
import itertools as it
import json
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEADLINE = time.monotonic() + 60


def guard():
    if time.monotonic() > DEADLINE:
        raise RuntimeError('resource cap; no outcome')


def pairs(B):
    return tuple(sorted(x for b in B for x in (b, b + 1)))


def turns(R, d, preparation=()):
    """Enumerate ALL ordered legal completed turns, including continued picks."""
    assert R and sum(R) >= d
    for x in R:
        guard()
        if x >= d:
            yield preparation + (x,)
        else:
            yield from turns(tuple(y for y in R if y != x), d - x,
                             preparation + (x,))


def endpoint(R, d, path):
    assert len(set(path)) == len(path) and set(path) <= set(R)
    assert sum(path[:-1]) < d or len(path) == 1
    assert sum(path) >= d
    return tuple(x for x in R if x not in path), sum(path) - d


def balanced(R, d):
    """Find a legal exact-quota turn; purely arithmetic, no game evaluation."""
    T = sum(R)
    if (T + d) % 2:
        return None
    q = (T + d) // 2
    # Every nonempty legal turn has sum < d+max(R), when d>0.
    if q >= d + max(R):
        return None
    for mask in range(1, 1 << len(R)):
        A = tuple(x for i, x in enumerate(R) if mask >> i & 1)
        if sum(A) == q and d <= q < d + max(A):
            return tuple(x for x in A if x != max(A)) + (max(A),)
    return None


def paired_reply(R, d, B, H, z):
    """One counter per intact pair, then orphan z; count-corrected quota."""
    e = z - d
    a = sum(H) + len(B) - e
    if e < 0 or a < 0 or a % 2:
        return None
    t = a // 2
    if t > len(B):
        return None
    P = tuple(b + (i < t) for i, b in enumerate(B))
    if sum(P) >= d:
        return None
    assert set(R) == set(H) | set(pairs(B)) | {z}
    assert len(R) == len(H) + 2 * len(B) + 1
    return P + (z,)


def check_reply(R, d, reply):
    E, e = endpoint(R, d, reply)
    assert sum(E) == e
    return {'picks': reply, 'remaining': E, 'deficit': e}


def main():
    inputs = {}
    for n, pool in [(7, (6, 10, 12, 14, 16, 18, 20, 22)),
                    (9, (6, 10, 12, 14, 16, 18, 20, 22, 24, 26))]:
        roots = {(4,) + c for c in it.combinations(pool, n - 1)}
        # Sparse held-out shapes, including the certified old obstruction.
        base = (4, 6, 10, 12, 20, 40) if n == 7 else (4, 6, 10, 12, 20, 40, 80, 100)
        for q in (base[-1] + 2, 2 * sum(base) + 20):
            roots.add(base + (q,))
        roots.add((4, 6, 10, 20, 40, 86, 88) if n == 7 else
                  (4, 6, 10, 12, 20, 40, 80, 180, 182))
        inputs[n] = sorted(roots)

    rows, stats = [], {}
    for n, roots in inputs.items():
        counts = dict(roots=len(roots), root_turns=0, residual_shapes=0,
                      residual_ordered_turns=0, residual_distinct_subsets=0,
                      continuing_turns=0, balance_replies=0, paired_replies=0,
                      uncovered=0, root_balance_replies=0, root_uncovered=0)
        for B in roots:
            R = pairs(B)
            for path in turns(R, 3):
                counts['root_turns'] += 1
                E, d = endpoint(R, 3, path)
                reply = balanced(E, d)
                counts['root_balance_replies' if reply else 'root_uncovered'] += 1
                row = {'kind': 'root', 'pairs': n, 'starts': B, 'opponent': path,
                       'reply': check_reply(E, d, reply) if reply else None}
                rows.append(row)
        # Every root's largest lower pick followed by the previous 4,q+1
        # defense reaches singleton5 + n-2 pairs, deficit8. Deduplicate.
        residuals = sorted({tuple(b for b in B if b not in (4, max(B))) for B in roots})
        for B in residuals:
            counts['residual_shapes'] += 1
            R = (5,) + pairs(B)
            subsets = set()
            for path in turns(R, 8):
                counts['residual_ordered_turns'] += 1
                counts['continuing_turns'] += len(path) > 1
                subsets.add(tuple(sorted(path)))
                E, d = endpoint(R, 8, path)
                reply = balanced(E, d)
                counts['balance_replies' if reply else 'uncovered'] += 1
                paired = None
                # Includes the complete opponent turn [5,x], not just [x].
                if len(path) == 1 or path[0] == 5:
                    x = path[-1]
                    b = x if x % 2 == 0 else x - 1
                    intact = tuple(a for a in B if a != b)
                    H = (5,) if len(path) == 1 else ()
                    z = b + 1 if x == b else b
                    paired = paired_reply(E, d, intact, H, z)
                if paired:
                    counts['paired_replies'] += 1
                    assert reply is not None
                rows.append({'kind': 'residual', 'pairs': n, 'starts': B,
                             'opponent': path,
                             'reply': check_reply(E, d, reply) if reply else None,
                             'paired': check_reply(E, d, paired) if paired else None})
            counts['residual_distinct_subsets'] += len(subsets)
        stats[n] = counts
    # The count correction matters: four pairs use zero uppers; six use one.
    corrections = []
    for B, r in [((6, 10, 20, 40), 86), ((6, 10, 12, 20, 40, 80), 180)]:
        R = (5,) + pairs(B) + (r + 1,)
        d = r - 8
        corrected = paired_reply(R, d, B, (5,), r + 1)
        assert corrected
        old = B + (r + 1,)
        E, e = endpoint(R, d, old)
        corrections.append({'starts': B, 'r': r,
                            'corrected': check_reply(R, d, corrected),
                            'all_lowers': {'remaining': E, 'deficit': e,
                                           'remaining_sum': sum(E)}})
    critical_R = (5, 6, 7, 10, 11, 13, 20, 21, 40, 41)
    assert balanced(critical_R, 4) is None
    result = {'status': 'complete', 'scope': 'Partial whole-turn balancing rule; no root outcome claims',
              'counts': stats, 'count_corrections': corrections,
              'mandatory_obstruction': {'remaining': critical_R, 'deficit': 4,
                                        'total': sum(critical_R), 'max': max(critical_R),
                                        'draw_quota': (sum(critical_R) + 4) // 2}}
    (HERE / 'inputs.json').write_text(json.dumps(inputs, indent=2) + '\n')
    (HERE / 'rows.json').write_text(json.dumps(rows, separators=(',', ':')) + '\n')
    (HERE / 'checks.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
