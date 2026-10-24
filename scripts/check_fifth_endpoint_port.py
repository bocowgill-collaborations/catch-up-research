#!/usr/bin/env python3
"""Check the source-preserving fifth-endpoint port, not its Lean validity.

Lean builds and transitive axiom audits are separate mandatory checks. No archived
command or computational search is executed by this provenance checker.
"""
import hashlib
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def reconstruct(kind, text):
    if kind == 'exact-sum-residual-interface':
        header = text.split('import ', 1)[0]
        start = text.index('/-- An exact-deficit block proves nonloss')
        end = text.index('/-- A two-counter specialization', start)
        return (header + 'import CatchUp.ExactSumLossObstruction\n\n/-!\n'
                '# Exact-deficit residual exclusion\n\n'
                'A positive exact-deficit block proves nonloss if every residual opening above a chosen\n'
                'member of the block is nonlosing. This reusable interface applies the existing exact-sum\n'
                'loss obstruction and checks every potentially forced larger opening.\n'
                '-/\n\nnamespace CatchUp\n\n' + text[start:end] + 'end CatchUp\n').encode()
    require(kind == 'fifth-endpoint', 'unrecognized port transformation')
    text = text.replace('import catch_up.LowerRayFourthEndpoint',
                        'import CatchUp.ExactSumResiduals\nimport CatchUp.Earlier.DeficitWinningBound')
    text = re.sub(r'^@\[category API, AMS 91\]\n', '', text, flags=re.M)
    text = text.replace('The proof uses ExactSumLossObstruction through LowerRayFourthEndpoint\n'
                        'and does not assume the Catch-Up conjecture.',
                        'The proof uses the exact-sum residual-exclusion interface and the verified lower-ray\n'
                        'winning-opening bound. It does not assume parity, a smaller-instance draw, or the\n'
                        'Catch-Up conjecture.')
    text = text.replace('def upperQuadrupleResidual (m : ℕ)',
                        '/-- The lower interval with a two-counter gap and four consecutive upper counters. -/\n'
                        'def upperQuadrupleResidual (m : ℕ)')
    return text.encode()


def same_bytes(actual, expected):
    require(actual == expected, 'port differs from its disclosed source transformations')


def main():
    manifest = json.loads((ROOT / 'verification/fifth-endpoint-port.json').read_text())
    legacy = json.loads((ROOT / 'verification/legacy-sources.json').read_text())
    sources = {r['id']: r for r in legacy['records']}
    names = []
    for row in manifest['sources']:
        raw = (ROOT / row['original_input']).read_bytes()
        source = sources[row['source_id']]
        original_hash = hashlib.sha256(raw).hexdigest()
        require(original_hash == row['original_sha256'] == source['original_sha256'], 'original hash changed')
        require(row['git_blob'] == source['git_blob'] and
                row['source_commit'] in source['observed_commits'], 'incorrect original Git provenance')
        require(row['original_path'] == source['original_path'] and
                row['source_branch'] in source['branch_tips'], 'incorrect original path/branch')
        require(row['original_input'] == source.get('existing_path', source.get('export_path')),
                'port input is not the inventoried original')
        actual = (ROOT / row['path']).read_bytes()
        require(hashlib.sha256(actual).hexdigest() == row['sha256'] and len(actual) == row['bytes'],
                'ported source fingerprint changed')
        expected = reconstruct(row['kind'], raw.decode())
        same_bytes(actual, expected)
        # Mutate a theorem name in the original input, then exercise the real
        # reconstruction/comparison path rather than a stand-alone comparator.
        mutated = raw.decode().replace('theorem ', 'theorem mutation_', 1)
        try:
            same_bytes(actual, reconstruct(row['kind'], mutated))
        except ValueError:
            pass
        else:
            raise ValueError('source-mutation control accepted')
        require(not re.search(r'\b(?:sorry|sorryAx|native_decide|ofReduceBool|trustCompiler)\b', actual.decode()),
                'forbidden proof shortcut in port')
        names += re.findall(r'^theorem\s+([^\s(:]+)', actual.decode(), re.M)
    require(names == manifest['public_theorem_names'], 'theorem inventory changed')
    require(set(manifest['sources'][i]['path'] for i in range(len(manifest['sources']))) ==
            {'CatchUp/ExactSumResiduals.lean', 'CatchUp/LowerRayFifthEndpoint.lean'}, 'port scope changed')
    print('Fifth-endpoint source port passed: 2 modules, 6 public theorems; '
          'original hashes, exact transformations and source-mutation rejection')


if __name__ == '__main__':
    main()
