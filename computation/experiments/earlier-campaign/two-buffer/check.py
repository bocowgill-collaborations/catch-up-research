#!/usr/bin/env python3
"""Replay the frozen controller and independently check every stored game state."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(HERE))
import replay
from reference import State, absolute_value


def require(test, message):
    if not test:
        raise AssertionError(message)


def rejected(cert):
    try:
        replay.verify(cert)
    except AssertionError:
        return
    raise AssertionError('corrupt policy accepted')


def main():
    require(__debug__, 'Run without Python optimization')
    cert = json.loads((HERE / 'policy.json').read_text())
    result = replay.verify(cert)
    result['mutations_rejected'] = replay.mutation_tests(cert)
    historical = json.loads((HERE / 'historical-replay.json').read_text())
    require(json.loads(json.dumps(result)) == historical, 'historical full replay differs')
    spec = importlib.util.spec_from_file_location('two_buffer_public_reference',
                                                ROOT / 'computation/check_semantics.py')
    reference = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(reference)
    checked = 0
    for node in cert['nodes']:
        for side in ('U', 'V'):
            state = node[side]
            counters = tuple(state['remaining'])
            s0, s1 = state['scores']
            mover = state['mover']
            score, other = (s0, s1) if mover == 0 else (s1, s0)
            expected = reference.absolute(counters, score, other)
            actual = absolute_value(counters, s0, s1, mover)
            require(actual == expected * (1 if mover == 0 else -1),
                    'independent state recurrence differs')
            for x in counters:
                if counters and score + sum(counters) >= other:
                    scores = [s0, s1]
                    scores[mover] += x
                    next_mover = 1 - mover if scores[mover] >= scores[1 - mover] else mover
                    child = tuple(y for y in counters if y != x)
                    child_value = reference.absolute(child, scores[next_mover],
                                                     scores[1 - next_mover])
                    require(absolute_value(child, *scores, next_mover) ==
                            child_value * (1 if next_mover == 0 else -1),
                            'independent child recurrence differs')
            checked += 1
    # Targeted rule controls: strict continuation, equality switch and early completion.
    state = State((1, 2), (0, 2), 0).pick(1)
    require(state.mover == 0 and state.pick(2).mover == 1, 'turn switch boundary')
    require(not State((2,), (0, 2), 0).terminal(), 'exact catch pruned')
    require(State((1,), (0, 3), 0).complete()[0] == -2, 'early completion sign')
    bad = copy.deepcopy(cert)
    bad['nodes'][0]['ledger'] += 1
    rejected(bad)
    bad = copy.deepcopy(cert)
    branch = next(n for n in bad['nodes'] if len(n.get('edges', [])) > 1)
    branch['edges'].append(copy.deepcopy(branch['edges'][0]))
    rejected(bad)
    bad = copy.deepcopy(cert)
    branch = next(n for n in bad['nodes'] if n.get('action', {}).get('pick') is None
                  and 'action' in n)
    branch['action']['pick'] = branch['edges'][0]['pick']
    rejected(bad)
    bad = copy.deepcopy(cert)
    bad['nodes'][0]['buffer'] = [0, 0]
    rejected(bad)
    bad = copy.deepcopy(cert)
    bad['nodes'][0]['edges'][0]['child'] = 0
    rejected(bad)
    optimized = subprocess.run([sys.executable, '-O', str(HERE / 'replay.py')],
                               capture_output=True, text=True, timeout=15)
    require(optimized.returncode != 0 and 'Run without Python optimization' in
            optimized.stdout + optimized.stderr, 'optimized assertion bypass accepted')
    print(f'Two-buffer replay passed: {result["policy_nodes"]} nodes, '
          f'{result["terminal_histories"]} terminal histories, {checked} state comparisons, '
          'every legal reply, nine policy mutations and optimization bypass rejected')


if __name__ == '__main__':
    main()
