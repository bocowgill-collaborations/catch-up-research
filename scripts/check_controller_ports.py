#!/usr/bin/env python3
"""Check the five source-preserving controller ports against archived inputs."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
MODULES = (
    'ScoreDebtRepairCertificates', 'TwoBufferProtocol', 'TwoBufferMandatory',
    'TwoPickDebtRepair', 'CompletedMarginBounds',
)
IMPORTS = {
    'catch_up.ScoreDebtTerminalRepair': 'CatchUp.Earlier.ScoreDebtTerminalRepair',
    'catch_up.AdjacentHoleExchangeObstruction': 'CatchUp.AdjacentHoleExchangeObstruction',
    'catch_up.ScoreDebtRepairCertificates': 'CatchUp.ScoreDebtRepairCertificates',
    'catch_up.TwoBufferProtocol': 'CatchUp.TwoBufferProtocol',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def reconstruct(text):
    text = re.sub(r'^import ([^\n]+)$',
                  lambda m: 'import ' + IMPORTS.get(m[1], m[1]), text, flags=re.M)
    return re.sub(r'^@\[category (?:test|API), AMS 91\]\n', '', text, flags=re.M).encode()


def theorem_names(text):
    """These inputs use explicit, nonnested namespace/end blocks."""
    namespace = None
    names = []
    for line in text.splitlines():
        if line.startswith('namespace '):
            require(namespace is None, 'unexpected nested namespace')
            namespace = line.split()[1]
        elif line.startswith('end '):
            require(line.split()[1] == namespace, 'unexpected namespace end')
            namespace = None
        elif line.startswith('theorem '):
            require(namespace is not None, 'theorem outside namespace')
            names.append(namespace + '.' + re.match(r'theorem\s+([^\s(:]+)', line)[1])
    require(namespace is None, 'unclosed namespace')
    return names


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-ports', action='store_true',
                        help='mechanically regenerate only the five Lean ports')
    args = parser.parse_args()
    if args.write_ports:
        for name in MODULES:
            raw = (ROOT / f'archive/catch_up/{name}.lean.txt').read_text()
            (ROOT / f'CatchUp/{name}.lean').write_bytes(reconstruct(raw))
        print('Generated five source-preserving controller ports')
        return
    manifest = json.loads((ROOT / 'verification/controller-ports.json').read_text())
    records = {r['id']: r for r in json.loads(
        (ROOT / 'verification/legacy-sources.json').read_text())['records']}
    require([r['module'] for r in manifest['sources']] == list(MODULES), 'scope changed')
    audit = (ROOT / 'AxiomAudit.lean').read_text()
    count = 0
    for row in manifest['sources']:
        name = row['module']
        require(row['original_input'] == f'archive/catch_up/{name}.lean.txt' and
                row['path'] == f'CatchUp/{name}.lean', 'wrong controller path')
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
        qualified = theorem_names(actual.decode())
        require(qualified == row['qualified_theorem_names'], 'qualified inventory changed')
        require([n.rsplit('.', 1)[1] for n in qualified] == row['public_theorem_names'],
                'public inventory changed')
        for theorem in qualified:
            require(f'#print axioms {theorem}\n' in audit, 'missing named axiom endpoint')
        mutations = [re.sub(r'^theorem\s+', 'theorem corrupt_', raw.decode(),
                            count=1, flags=re.M)]
        # Reject proof changes as well as theorem-contract changes.
        proof_token = 'exact not_congr' if name == 'TwoBufferProtocol' else 'decide +kernel'
        mutations.append(raw.decode().replace(proof_token, 'sorry', 1))
        if name == 'TwoBufferProtocol':
            mutations.append(raw.decode().replace('¬CanAvoidLoss .p2', 'CanAvoidLoss .p2', 1))
        if name == 'TwoBufferMandatory':
            mutations.append(raw.decode().replace('.actualPick 2)', '.actualPick 5)', 1))
        for mutation in mutations:
            require(mutation != raw.decode() and actual != reconstruct(mutation),
                    'source mutation control accepted')
        count += len(qualified)
    print(f'Controller ports passed: {len(MODULES)} modules, {count} public theorems; '
          'exact reconstruction and contract/proof/filter/policy mutation rejection')


if __name__ == '__main__':
    main()
