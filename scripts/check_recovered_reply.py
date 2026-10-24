#!/usr/bin/env python3
"""Check immutable recovery inputs; optionally replay terms and compare source.

Static provenance checks are part of collection CI. --lean additionally requires
the pinned mathematics package to be built; it runs two isolated Lean environments.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def fingerprint(data, row):
    require(len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256'],
            'Recovery fingerprint mismatch: ' + row['path'])


def check_static():
    manifest = json.loads((ROOT / 'verification/reply-maximum-companion.json').read_text())
    rows = manifest['artifacts'] + manifest['source_files']
    require(len(rows) == 5 and len({r['path'] for r in rows}) == 5, 'Recovery inventory changed')
    for row in rows:
        data = (ROOT / row['path']).read_bytes()
        fingerprint(data, row)
        try:
            fingerprint(data + b'corruption-control', row)
        except ValueError:
            pass
        else:
            raise ValueError('Corrupted recovery input accepted')
        require(not re.search(rb'[/]Users/|[/]private/|[/]home/|gh[opusr]_[A-Za-z0-9]{20,}|'
                              rb'BEGIN (?:RSA |OPENSSH )?PRIVATE KEY', data),
                'Private path or credential in ' + row['path'])
    metadata = json.loads((ROOT / manifest['artifacts'][1]['path']).read_text())
    require(set(metadata['decls']) == set(manifest['public_declarations']) | {
        '_private.catch_up.ReplyMaximumCompanion.0.CatchUp.Outcome.best_eq_win_iff',
        '_private.catch_up.ReplyMaximumCompanion.0.CatchUp.Position.value_eq_win_of_winning_move'},
        'Source-level cached declaration metadata changed')
    require(len(manifest['cached_declarations']) == len(set(manifest['cached_declarations'])) == 10,
            'Cached declaration inventory changed')
    source = (ROOT / 'CatchUp/ReplyMaximumCompanion.lean').read_text()
    require(re.findall(r'^theorem\s+([^\s(:]+)', source, re.M) ==
            [n.removeprefix('CatchUp.') for n in manifest['public_declarations'][2:]],
            'Reconstructed theorem inventory changed')
    receipt = json.loads((ROOT / 'verification/reply-maximum-companion-checks.json').read_text())
    require(receipt['status'] == 'PASS_WITH_BASELINE_WARNING_EXCEPTION', 'Unfinished recovery receipt')
    for row in receipt['checks'] + receipt['audit_logs']:
        data = (ROOT / row['log']).read_bytes()
        require(hashlib.sha256(data).hexdigest() == row['public_output_sha256'] and
                len(data) == row['public_output_bytes'], 'Recovery receipt log changed')
    require([row['label'] for row in receipt['checks'] if row['exit_code'] != 0] ==
            ['cryptid-build'], 'Unexpected verification failure')
    # This receipt records the original recovery run, not a permanent freeze of
    # shared aggregators, CI or this checker. The manifest still pins all three
    # current Lean sources above. Cross-check their historical hashes as well.
    lean_inputs = {row['path']: row['sha256'] for row in manifest['source_files']}
    for row in receipt['source_fingerprints']:
        require(re.fullmatch('[0-9a-f]{64}', row['sha256']), 'Invalid historical source hash')
        if row['path'] in lean_inputs:
            require(row['sha256'] == lean_inputs[row['path']],
                    'Recovered Lean source differs from the original recovery run')
    print('Reply-companion provenance passed: 2 retained artifacts, 3 source/check files; '
          'fingerprints, metadata, privacy and corruption controls')
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', action='store_true')
    args = parser.parse_args()
    manifest = check_static()
    if not args.lean:
        return
    from check_axioms import validate
    dest = ROOT / 'verification/local/reply-maximum-companion'
    dest.mkdir(parents=True, exist_ok=True)
    for kind, filename in [('replay', 'Replay'), ('comparison', 'Compare')]:
        command = ['lake', 'env', 'lean', '-DwarningAsError=true',
                   'verification/' + filename + 'ReplyMaximumCompanion.lean']
        proc = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=180)
        output = proc.stdout + proc.stderr
        (dest / (kind + '.log')).write_text(output)
        require(proc.returncode == 0, output)
        if kind == 'replay':
            names = re.findall(r'^KERNEL_REPLAYED (\S+)$', output, re.M)
            require(len(names) == 10 and set(names) == set(manifest['cached_declarations']),
                    'Incomplete or unexpected cached replay')
            require('Invalid-proof control rejected' in output and
                    'KERNEL_REPLAY_COMPLETE 10 declarations' in output, 'Incomplete replay controls')
            validate(output, set(manifest['public_declarations'][2:]))
        else:
            require(re.findall(r'^SOURCE_SIGNATURE_MATCH (\S+)$', output, re.M) ==
                    manifest['public_declarations'], 'Incomplete source comparison')
            require('SOURCE_COMPARISON_COMPLETE 4 signatures and 2 definition bodies' in output,
                    'Incomplete source comparison')
        print(output, end='')
    print('Recovered reply companion passed: original terms kernel-replayed; '
          'source signatures/definitions match; permitted transitive axioms only')


if __name__ == '__main__':
    main()
