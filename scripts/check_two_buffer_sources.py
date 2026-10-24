#!/usr/bin/env python3
"""Check source reconstruction for the bounded two-buffer replay bundle."""
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
BUNDLE = 'computation/experiments/earlier-campaign/two-buffer/'


def require(test, message):
    if not test:
        raise ValueError(message)


def reference(absolute_source, state_source):
    a = absolute_source.index('@cache\ndef absolute_value(')
    b = absolute_source.index('\n\ndef verify_independently(', a)
    c = state_source.index('@dataclass(frozen=True)\nclass State:')
    d = state_source.index('\n\ndef play(', c)
    return ('"""Fixed-player score recurrence and persistent ownership states.\n\n'
            'Extracted from the earlier independent replay; no synthesis is imported.\n'
            'Player 0 is protected, equality switches, and early completion awards\n'
            'all remaining counters to the trailing player. See bundle provenance.\n'
            '"""\nfrom dataclasses import dataclass\nfrom functools import cache\n\n\n' +
            absolute_source[a:b] + '\n\n\n' + state_source[c:d]).encode()


def replay(text):
    text = text.replace('from adjacent_jump_probe import absolute_value\n'
                        'from score_debt_repair_probe import State',
                        'from pathlib import Path\nimport sys\n'
                        'from reference import State, absolute_value\n\n'
                        'sys.dont_write_bytecode = True\n'
                        'if not __debug__:\n'
                        '    raise SystemExit("Run without Python optimization: replay checks use assertions")')
    return text.replace("parser.add_argument('certificate')",
                        "parser.add_argument('certificate', nargs='?',\n"
                        "                        default=Path(__file__).with_name('policy.json'))").encode()


def main():
    manifest = json.loads((ROOT / 'verification/two-buffer-replay.json').read_text())
    records = {r['id']: r for r in
               json.loads((ROOT / 'verification/legacy-sources.json').read_text())['records']}
    inputs = {}
    for row in manifest['inputs']:
        record = records[row['source_id']]
        data = (ROOT / row['archive_path']).read_bytes()
        require(record['export_path'] == row['archive_path'], 'incorrect archive input')
        require(hashlib.sha256(data).hexdigest() == row['sha256'] == record['export_sha256'],
                'archive fingerprint changed')
        inputs[row['role']] = data
    expected = {
        'reference.py': reference(inputs['absolute'].decode(), inputs['state'].decode()),
        'replay.py': replay(inputs['checker'].decode()),
        'policy.json': inputs['policy'],
        'historical-replay.json': inputs['historical-replay'],
    }
    require(set(manifest['exports']) == set(expected), 'bundle source scope changed')
    for name, data in expected.items():
        actual = (ROOT / BUNDLE / name).read_bytes()
        require(actual == data, 'undisclosed replay-source change: ' + name)
        item = manifest['exports'][name]
        require(hashlib.sha256(actual).hexdigest() == item['sha256'] and
                len(actual) == item['bytes'], 'bundle fingerprint changed')
    # Controls exercise the real extraction/transformation boundaries.
    bad = inputs['absolute'].decode().replace('>= updated[1 - mover]', '> updated[1 - mover]')
    require(reference(bad, inputs['state'].decode()) != expected['reference.py'],
            'equality-rule mutation control accepted')
    bad = inputs['checker'].decode().replace('max(width) <= 2', 'max(width) <= 3')
    require(replay(bad) != expected['replay.py'], 'buffer-bound mutation control accepted')
    print('Two-buffer source reconstruction passed: four exports, exact archive hashes, '
          'equality and buffer mutation controls')


if __name__ == '__main__':
    main()
