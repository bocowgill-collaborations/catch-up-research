#!/usr/bin/env python3
"""Reconstruct the two additional endpoint ports; Lean checks validity separately."""
import hashlib
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
INPUTS = {
    'antepenultimate': ('archive/catch_up/LowerRayAntepenultimateDescent.lean.txt',
                       'CatchUp/LowerRayAntepenultimateDescent.lean'),
    'fourth': ('archive/catch_up/LowerRayFourthEndpoint.lean.txt',
               'CatchUp/LowerRayFourthEndpoint.lean'),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def reconstruct(kind, text):
    require(kind in INPUTS, 'unknown endpoint port')
    if kind == 'fourth':
        start = text.index('/-- An exact-deficit block proves nonloss')
        end = text.index('/-- A two-counter specialization', start)
        # This declaration is already exported by the existing generic interface.
        existing = (ROOT / 'CatchUp/ExactSumResiduals.lean').read_text()
        require(text[start:end] in existing, 'shared exact-sum declaration changed')
        text = text[:start] + text[end:]
        text = text.replace('import catch_up.ExactSumLossObstruction',
                            'import CatchUp.ExactSumResiduals')
    replacements = {
        'catch_up.DeficitWinningBound': 'CatchUp.Earlier.DeficitWinningBound',
        'catch_up.DrawOpening': 'CatchUp.DrawOpening',
        'catch_up.ExactSumLossObstruction': 'CatchUp.ExactSumLossObstruction',
        'catch_up.CompletedTurn': 'CatchUp.CompletedTurn',
        'catch_up.CanAvoidLossClassifier': 'CatchUp.Classifier',
    }
    for old, new in replacements.items():
        text = text.replace(old, new)
    return re.sub(r'^@\[category API, AMS 91\]\n', '', text, flags=re.M).encode()


def main():
    manifest = json.loads((ROOT / 'verification/endpoint-ports.json').read_text())
    legacy = json.loads((ROOT / 'verification/legacy-sources.json').read_text())
    records = {r['id']: r for r in legacy['records']}
    names = []
    require({row['kind'] for row in manifest['sources']} == set(INPUTS), 'port scope changed')
    for row in manifest['sources']:
        require(INPUTS[row['kind']] == (row['original_input'], row['path']), 'wrong port path')
        raw = (ROOT / row['original_input']).read_bytes()
        record = records[row['source_id']]
        require(hashlib.sha256(raw).hexdigest() == row['original_sha256'] ==
                record['original_sha256'], 'original hash changed')
        require(row['original_path'] == record['original_path'] and
                row['git_blob'] == record['git_blob'] and
                row['source_commit'] in record['observed_commits'], 'incorrect Git provenance')
        require(record['existing_path'] == row['original_input'], 'wrong archived original')
        actual = (ROOT / row['path']).read_bytes()
        require(actual == reconstruct(row['kind'], raw.decode()), 'undisclosed proof change')
        require(hashlib.sha256(actual).hexdigest() == row['sha256'] and
                len(actual) == row['bytes'], 'port fingerprint changed')
        mutated = raw.decode().replace('theorem ', 'theorem corrupt_', 1)
        try:
            expected = reconstruct(row['kind'], mutated)
            require(actual == expected, 'source mutation rejected')
        except ValueError:
            pass
        else:
            raise ValueError('source mutation control accepted')
        names += re.findall(r'^theorem\s+([^\s(:]+)', actual.decode(), re.M)
    require(names == manifest['public_theorem_names'], 'theorem inventory changed')
    print(f'Endpoint ports passed: 2 modules, {len(names)} public theorems; '
          'exact source reconstruction and mutation rejection')


if __name__ == '__main__':
    main()
