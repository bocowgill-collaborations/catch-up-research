#!/usr/bin/env python3
"""Replay literal small witnesses from CU-L016/019/022/023/028/029/033.

This is bounded computational regression, not a replay of the historical scans,
an archived Lean build, or a certificate for any parametric assertion.
"""
import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    reference = load('legacy_absolute', 'computation/check_semantics.py')
    explorer = load('legacy_normalized', 'computation/explore.py')
    count = 0

    def check(support, deficit, expected=None, moves=None, initial=False):
        nonlocal count
        support = tuple(sorted(support))
        solver = explorer.Solver(support, seconds=10, max_states=200_000)
        report = solver.report(None if initial else deficit)
        value = reference.absolute(support, 0, deficit, initial)
        assert report['outcome'] == explorer.NAMES[value]
        if expected is not None:
            assert value == expected, (support, deficit, value, expected)
        actual = {r['pick']: r['pick_outcome'] for r in report['picks']}
        for x in support:
            if not report['picks']:
                break
            child = reference.absolute(tuple(y for y in support if y != x),
                                       deficit if initial or x >= deficit else x,
                                       x if initial or x >= deficit else deficit)
            candidate = -child if initial or x >= deficit else child
            assert actual[x] == explorer.NAMES[candidate], (support, deficit, x)
        for x, result in (moves or {}).items():
            assert actual[x] == explorer.NAMES[result], (support, deficit, x)
        reference.absolute.cache_clear()
        count += 1
        return actual

    # Statewise four-lift failures, not interval-root counterexamples.
    for n, support, deficit in [(11, (1, 2, 8), 11), (12, (6, 12), 6)]:
        check(support, deficit, 0)
        check(support + tuple(range(n + 1, n + 5)), deficit, 1)
    check((3, 4, 5), 0, 1, initial=True)
    check((4, 5, 6, 7, 8), 0, 1, initial=True)
    # Natural correspondence of moves fails, despite U drawing and V winning.
    u = check((2, 5, 6, 9, 10, 11), 1, 0, {2: 0})
    v = check((2, 5, 6, 7, 10, 11), 1, 1, {5: 1, 10: 0})
    for x, value in v.items():
        if value != 'loss':
            assert u[9 if x == 7 else x] == 'loss'
    assert [(x, y) for x in u for y in v if u[x] != 'loss' and v[y] == 'win'] == [(2, 5)]
    check((6, 11, 14, 15, 18, 23), 1, -1)
    check((4, 11, 14, 15, 18, 23), 1, 1)
    check((4, 6, 11, 14, 15, 18, 23), 5, 0, {11: 0})
    sparse = (3, 7, 9, 14, 17, 20, 29, 34)
    assert 1 + sum(sparse) == 134
    check(sparse, 1, -1)
    check(sparse[1:], 2, 1)
    cycle = (3, 4, 9, 16, 17, 18, 26, 28, 31, 37)
    check(cycle, 1, -1)
    check(tuple(x for x in cycle if x != 3), 2, None, {4: 1})
    check(tuple(x for x in cycle if x != 4), 3, None, {3: 1})
    interior = (3, 4, 5, 6, 9, 19, 24, 26, 29, 38)
    check(tuple(x for x in interior if x != 3), 2, None, {5: 1})
    check(tuple(x for x in interior if x != 5), 4, None, {3: 1, 4: 0})
    check(tuple(x for x in interior if x != 4), 3, None, {5: -1})
    profile = check((3, 4, 5, 6), 6)
    assert [x for x in profile if profile[x] == 'win'] == [3]
    check((6, 7, 8), 3, 1, {6: 1, 7: 1, 8: 1})
    # An always-swap bug reverses a known continuing move; it must be detected.
    assert reference.absolute((4, 7), 2, 3) == 1
    assert -reference.absolute((4, 7), 2, 3) != 1
    print(f'Legacy example checks passed: {count} literal positions, every first pick, '
          'two independent recurrences; no historical scan or Lean proof replay')


if __name__ == '__main__':
    main()
