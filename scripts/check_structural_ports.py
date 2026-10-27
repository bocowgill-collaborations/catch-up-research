#!/usr/bin/env python3
"""Reconstruct four archived structural ports without changing mathematical code."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
MODULES = ('EffectiveTotalDescent', 'DenseLossInjection',
           'PrefixBlockedDenseEndpoints', 'LowerRayInteriorReduction')
IMPORTS = {
    'FormalConjectures.Paper.CatchUpConjecture': 'CatchUp.Reference',
    'catch_up.ExactSumLossObstruction': 'CatchUp.ExactSumLossObstruction',
    'catch_up.DenseLossInjection': 'CatchUp.DenseLossInjection',
    'catch_up.DeficitWinningBound': 'CatchUp.Earlier.DeficitWinningBound',
    'catch_up.LowerRayExactDeficit': 'CatchUp.Earlier.LowerRayExactDeficit',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def reconstruct(text):
    text = re.sub(r'^import ([^\n]+)$',
                  lambda m: 'import ' + IMPORTS.get(m[1], m[1]), text, flags=re.M)
    return re.sub(r'^@\[category (?:API|test), AMS 91\]\n', '', text, flags=re.M).encode()


def theorem_names(text):
    require(text.count('\nnamespace CatchUp\n') == 1 and
            text.count('\nend CatchUp\n') == 1, 'unexpected namespace structure')
    return re.findall(r'^theorem\s+([^\s(:]+)', text, re.M)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-ports', action='store_true',
                        help='mechanically regenerate only these four Lean ports')
    args = parser.parse_args()
    if args.write_ports:
        for name in MODULES:
            raw = (ROOT / f'archive/catch_up/{name}.lean.txt').read_text()
            (ROOT / f'CatchUp/{name}.lean').write_bytes(reconstruct(raw))
        print('Generated four source-preserving structural ports')
        return
    manifest = json.loads((ROOT / 'verification/structural-ports.json').read_text())
    records = {r['id']: r for r in json.loads(
        (ROOT / 'verification/legacy-sources.json').read_text())['records']}
    require([r['module'] for r in manifest['sources']] == list(MODULES), 'scope changed')
    audit = (ROOT / 'AxiomAudit.lean').read_text()
    count = 0
    for row in manifest['sources']:
        name = row['module']
        require(row['original_input'] == f'archive/catch_up/{name}.lean.txt' and
                row['path'] == f'CatchUp/{name}.lean', 'wrong structural path')
        raw = (ROOT / row['original_input']).read_bytes()
        record = records[row['source_id']]
        require(digest(raw) == row['original_sha256'] == record['original_sha256'],
                'original fingerprint changed')
        require(record['existing_path'] == row['original_input'] and
                record['original_path'] == row['original_path'] and
                record['git_blob'] == row['git_blob'] and
                row['source_commit'] in record['observed_commits'], 'wrong provenance')
        actual = (ROOT / row['path']).read_bytes()
        require(actual == reconstruct(raw.decode()), 'undisclosed mathematical change')
        require(digest(actual) == row['sha256'] and len(actual) == row['bytes'],
                'port fingerprint changed')
        names = theorem_names(actual.decode())
        require(names == row['public_theorem_names'], 'public inventory changed')
        require(['CatchUp.' + n for n in names] == row['qualified_theorem_names'],
                'qualified inventory changed')
        for theorem in row['qualified_theorem_names']:
            require(f'#print axioms {theorem}\n' in audit, 'missing named axiom endpoint')
        mutations = [re.sub(r'^theorem\s+', 'theorem corrupt_', raw.decode(),
                            count=1, flags=re.M), raw.decode().replace('omega', 'sorry', 1)]
        if name == 'EffectiveTotalDescent':
            mutations.append(raw.decode().replace('hdeficit : 0 < deficit',
                                                  'hdeficit : 0 ≤ deficit', 1))
        if name == 'LowerRayInteriorReduction':
            mutations.append(raw.decode().replace('hpairDraw : (pairDeletionPosition N 1 2).value = .draw',
                                                  'hpairDraw : (pairDeletionPosition N 1 2).value ≠ .loss', 1))
        for mutation in mutations:
            require(mutation != raw.decode() and actual != reconstruct(mutation),
                    'contract/proof mutation control accepted')
        count += len(names)
    print(f'Structural ports passed: {len(MODULES)} modules, {count} public theorems; '
          'exact reconstruction and contract/proof/hypothesis mutation rejection')


if __name__ == '__main__':
    main()
