#!/usr/bin/env python3
"""Match the Lean table to every reachable state of the preserved Python replay.

Without --lean this uses a deliberately restricted literal parser. With --lean,
also compare the table exported by Lean itself. Neither check is a premise of
mandatory_protocol: its policy and all branches are checked by the Lean kernel.
"""
import argparse
import copy
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
BUNDLE = ROOT / 'computation/experiments/earlier-campaign/two-buffer'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def state(remaining, deficit, mover):
    require(all(type(x) is int and x > 0 for x in remaining), 'invalid counters')
    require(len(set(remaining)) == len(remaining), 'duplicate counter')
    require(type(deficit) is int and deficit >= 0 and mover in (0, 1), 'invalid state')
    return {'remaining': sorted(remaining), 'deficit': deficit, 'mover': mover}


def parse_table(text):
    before, separator, rest = text.partition(
        'def policyEntries : List ((GamePosition × GamePosition) × Action) := [\n')
    require(separator and before, 'missing policy declaration')
    body, separator, _ = rest.partition(']\n\n/-- Table lookup')
    require(separator, 'missing policy end')
    position = r'⟨⟨\{([\d, ]*)\}, (\d+)⟩, \.p([12])⟩'
    pattern = re.compile(r'  \(\((' + position + r'), (' + position +
                         r')\), \.(actualPick|actualOpponent|shadowPick|shadowStrategy)'
                         r'(?: (\d+))?\),?')
    rows = []
    for line in body.splitlines():
        m = pattern.fullmatch(line)
        require(m is not None, 'unparsed policy row')
        def unpack(counters, deficit, mover):
            return state([int(x.strip()) for x in counters.split(',') if x.strip()],
                         int(deficit), int(mover) - 1)
        # Capturing groups include the two complete position literals.
        u = unpack(m[2], m[3], m[4])
        v = unpack(m[6], m[7], m[8])
        action, pick = m[9], m[10]
        require((pick is not None) == action.endswith('Pick'), 'wrong action arity')
        rows.append({'U': u, 'V': v, 'action': action,
                     'pick': int(pick) if pick is not None else None})
    require(rows, 'empty policy')
    return rows


def key(u, v):
    return json.dumps([u, v], sort_keys=True)


def normalize(record):
    mover = record['mover']
    scores = record['scores']
    return state(record['remaining'], scores[1 - mover] - scores[mover], mover)


def verify(rows, cert):
    expected = {}
    for node in cert['nodes']:
        if 'action' not in node:
            continue
        u, v = normalize(node['U']), normalize(node['V'])
        action = node['action']
        if action['side'] == 'U':
            name = 'actualPick' if u['mover'] == 0 else 'actualOpponent'
        else:
            require(action['side'] == 'V', 'invalid side')
            name = 'shadowPick' if v['mover'] == 1 else 'shadowStrategy'
        row = {'U': u, 'V': v, 'action': name, 'pick': action['pick']}
        k = key(u, v)
        require(k not in expected or expected[k] == row, 'history-dependent action conflict')
        expected[k] = row
    actual = {}
    for row in rows:
        k = key(row['U'], row['V'])
        # Distinct replay histories can have the same normalized state. The
        # original table retains repeated rows; first-match lookup is harmless
        # only because all occurrences prescribe the identical action.
        require(k not in actual or actual[k] == row, 'conflicting Lean policy key')
        actual[k] = row
    require(actual == expected, 'Lean and replay policies differ')
    return len(expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', action='store_true', help='also export the table with Lean')
    args = parser.parse_args()
    cert = json.loads((BUNDLE / 'policy.json').read_text())
    # The preserved replay checks legal edges, every adversarial reply, strict
    # shadow wins, owner histories, raw atomic buffers and completed margins.
    sys.path.insert(0, str(BUNDLE))
    spec = importlib.util.spec_from_file_location('controller_replay', BUNDLE / 'replay.py')
    replay = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(replay)
    result = replay.verify(cert)
    rows = parse_table((ROOT / 'CatchUp/TwoBufferMandatory.lean').read_text())
    count = verify(rows, cert)
    mutations = []
    bad = copy.deepcopy(rows); bad[0]['pick'] = 5; mutations.append(bad)
    bad = copy.deepcopy(rows); bad[0]['action'] = 'shadowPick'; mutations.append(bad)
    bad = copy.deepcopy(rows); bad[0]['U']['deficit'] = 2; mutations.append(bad)
    bad = copy.deepcopy(rows); bad[0]['U']['mover'] = 1; mutations.append(bad)
    mutations.append(rows[1:])
    conflict = copy.deepcopy(rows[0]); conflict['pick'] = 5
    mutations.append(rows + [conflict])
    for bad in mutations:
        try:
            verify(bad, cert)
        except ValueError:
            continue
        raise ValueError('policy mutation accepted')
    if args.lean:
        run = subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run',
                              'computation/CheckTwoBuffer.lean'], cwd=ROOT,
                             text=True, capture_output=True, check=True, timeout=120)
        require(json.loads(run.stdout) == rows, 'Lean export and parsed table differ')
    print(f'Controller policy passed: {len(cert["nodes"])} replay nodes, '
          f'{len(rows)} Lean rows / {count} distinct nonterminal paired states, '
          f'{result["terminal_histories"]} terminal histories, '
          f'{len(mutations)} policy mutations rejected; '
          f'Lean export {"checked" if args.lean else "not requested"}')


if __name__ == '__main__':
    main()
