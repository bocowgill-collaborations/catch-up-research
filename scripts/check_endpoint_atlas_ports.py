#!/usr/bin/env python3
"""Check exact archived-source reconstruction for the endpoint and trap atlas."""
import hashlib
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
MODULES = ('LowerRayEndpoints', 'AdjacentPairGeometryObstruction', 'FiveConsecutiveTrap')
IMPORTS = {
    'FormalConjectures.Paper.CatchUpConjecture': 'CatchUp.Reference',
    'catch_up.DeficitWinningBound': 'CatchUp.Earlier.DeficitWinningBound',
    'catch_up.TopFourClassification': 'CatchUp.Earlier.TopFourClassification',
    'catch_up.WinningOpening': 'CatchUp.WinningOpening',
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


def validate_port(actual, original, row):
    require(actual == reconstruct(original), 'undisclosed mathematical source change')
    require(digest(actual) == row['sha256'] and len(actual) == row['bytes'],
            'port fingerprint changed')
    namespace = row['namespace']
    text = actual.decode()
    require(text.count('\nnamespace ' + namespace + '\n') == 1 and
            text.count('\nend ' + namespace + '\n') == 1, 'namespace changed')
    names = re.findall(r'^theorem\s+([^\s(:]+)', text, re.M)
    require(names == row['public_theorem_names'], 'public theorem inventory changed')
    require([namespace + '.' + n for n in names] == row['qualified_theorem_names'],
            'qualified theorem inventory changed')
    return len(names)


def main():
    manifest = json.loads((ROOT / 'verification/endpoint-atlas-ports.json').read_text())
    records = {r['id']: r for r in json.loads(
        (ROOT / 'verification/legacy-sources.json').read_text())['records']}
    require([r['module'] for r in manifest['sources']] == list(MODULES), 'scope changed')
    audit = (ROOT / 'AxiomAudit.lean').read_text()
    count = 0
    controls = 0
    for row in manifest['sources']:
        name = row['module']
        require(row['original_input'] == f'archive/catch_up/{name}.lean.txt' and
                row['path'] == f'CatchUp/{name}.lean', 'wrong source path')
        expected_namespace = ('CatchUp.AdjacentPairGeometry'
                              if name == 'AdjacentPairGeometryObstruction' else 'CatchUp')
        require(row['namespace'] == expected_namespace, 'wrong namespace')
        raw = (ROOT / row['original_input']).read_bytes()
        record = records[row['source_id']]
        require(digest(raw) == row['original_sha256'] == record['original_sha256'],
                'original fingerprint changed')
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        require(blob == row['git_blob'] == record['git_blob'], 'Git blob changed')
        require(record['existing_path'] == row['original_input'] and
                record['original_path'] == row['original_path'] and
                row['source_commit'] in record['observed_commits'], 'wrong provenance')
        actual = (ROOT / row['path']).read_bytes()
        count += validate_port(actual, raw.decode(), row)
        for theorem in row['qualified_theorem_names']:
            require(f'#print axioms {theorem}\n' in audit, 'missing axiom endpoint')
        text = actual.decode()
        mutations = [re.sub(r'^theorem\s+', 'theorem corrupt_', text, count=1, flags=re.M),
                     text.replace('omega', 'sorry', 1)]
        premise = {'LowerRayEndpoints': ('hm : 4 ≤ m', 'hm : 3 ≤ m'),
                   'AdjacentPairGeometryObstruction': ('ha : 6 ≤ a', 'ha : 5 ≤ a'),
                   'FiveConsecutiveTrap': ('hk : 2 ≤ k', 'hk : 1 ≤ k')}[name]
        mutations.append(text.replace(*premise, 1))
        if name == 'FiveConsecutiveTrap':
            mutations.append(text.replace('deficit := 0, toMove := .p1',
                                          'deficit := 0, toMove := .p2', 1))
        for mutation in mutations:
            require(mutation != text, 'inactive mutation control')
            try:
                validate_port(mutation.encode(), raw.decode(), row)
            except ValueError:
                controls += 1
            else:
                raise ValueError('contract/proof/perspective mutation accepted')
    print(f'Endpoint atlas ports passed: {len(MODULES)} modules, {count} public theorems; '
          f'exact reconstruction, provenance and {controls} mutation controls')


if __name__ == '__main__':
    main()
