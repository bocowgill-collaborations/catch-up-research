#!/usr/bin/env python3
"""Reconstruct four archived ports exactly; Lean separately checks their proofs."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
MODULES = (
    'AdjacentHoleExchangeObstruction', 'FirstPairDescentObstruction',
    'ShiftedReplyCycle', 'TurnReserveInitialization',
)
IMPORTS = {
    'catch_up.CanAvoidLossClassifier': 'CatchUp.Classifier',
    'catch_up.CompletedTurn': 'CatchUp.CompletedTurn',
    'catch_up.CompletedMargin': 'CatchUp.Earlier.CompletedMargin',
    'catch_up.PairDeletionReduction': 'CatchUp.PairDeletion',
    'catch_up.FirstPairDescentObstruction': 'CatchUp.FirstPairDescentObstruction',
    'FormalConjecturesUtil': 'Mathlib.Algebra.BigOperators.Group.Finset.Basic\n'
                            'import Mathlib.Order.Interval.Finset.Nat\n'
                            'import Mathlib.Tactic',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def reconstruct(text):
    # Restrict adaptation to import lines and indexing attributes. Preserve every
    # mathematical declaration, proof body and original docstring verbatim.
    text = re.sub(r'^import ([^\n]+)$',
                  lambda m: 'import ' + IMPORTS.get(m[1], m[1]), text, flags=re.M)
    return re.sub(r'^@\[category (?:test|API), AMS 91\]\n', '', text, flags=re.M).encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-ports', action='store_true',
                        help='mechanically regenerate only the four port files')
    args = parser.parse_args()
    if args.write_ports:
        for name in MODULES:
            raw = (ROOT / f'archive/catch_up/{name}.lean.txt').read_text()
            (ROOT / f'CatchUp/{name}.lean').write_bytes(reconstruct(raw))
        print('Generated four source-preserving atlas ports')
        return
    manifest = json.loads((ROOT / 'verification/atlas-ports.json').read_text())
    legacy = json.loads((ROOT / 'verification/legacy-sources.json').read_text())
    records = {r['id']: r for r in legacy['records']}
    rows = manifest['sources']
    require([r['module'] for r in rows] == list(MODULES), 'atlas scope changed')
    count = 0
    for row in rows:
        name = row['module']
        require(row['original_input'] == f'archive/catch_up/{name}.lean.txt' and
                row['path'] == f'CatchUp/{name}.lean', 'wrong atlas path')
        raw = (ROOT / row['original_input']).read_bytes()
        record = records[row['source_id']]
        require(digest(raw) == row['original_sha256'] == record['original_sha256'],
                'original fingerprint changed')
        require(record['existing_path'] == row['original_input'] and
                record['original_path'] == row['original_path'] and
                record['git_blob'] == row['git_blob'] and
                row['source_commit'] in record['observed_commits'], 'wrong provenance')
        actual = (ROOT / row['path']).read_bytes()
        require(actual == reconstruct(raw.decode()), 'undisclosed declaration/proof change')
        require(digest(actual) == row['sha256'] and len(actual) == row['bytes'],
                'port fingerprint changed')
        names = re.findall(r'^theorem\s+([^\s(:]+)', actual.decode(), re.M)
        require(names == row['public_theorem_names'], 'theorem inventory changed')
        require(row['namespace'].startswith('CatchUp.'), 'wrong namespace')
        for name in names:
            require(f"#print axioms {row['namespace']}.{name}" in
                    (ROOT / 'AxiomAudit.lean').read_text(), 'missing named axiom endpoint')
        # Reject both a changed theorem contract and a changed proof body.
        for changed in (re.sub(r'^theorem\s+', 'theorem corrupt_',
                               raw.decode(), count=1, flags=re.M),
                        raw.decode().replace('decide +kernel', 'sorry', 1)):
            require(changed != raw.decode() and actual != reconstruct(changed),
                    'source mutation control accepted')
        count += len(names)
    print(f'Atlas ports passed: {len(rows)} modules, {count} public theorems; '
          'exact reconstruction and contract/proof mutation rejection')


if __name__ == '__main__':
    main()
