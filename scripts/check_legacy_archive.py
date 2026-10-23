#!/usr/bin/env python3
"""Validate the historical import; never execute archived instructions or searches."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def artifact(path, expected, size):
    p = Path(path)
    require(not p.is_absolute() and '..' not in p.parts, 'unsafe archive path')
    data = (ROOT / p).read_bytes()
    require(digest(data) == expected, 'archive hash mismatch: ' + str(p))
    require(len(data) == size, 'archive byte count mismatch: ' + str(p))
    return data


def relevant(p):
    return ((p.startswith('CATCHUP') and p.endswith('.md')) or
            p.startswith(('research/', 'scripts/catch_up/', 'scripts/catch_up_search/')) or
            p in ('scripts/catch_up_compare.lean', 'scripts/catch_up_four.lean',
                  'FormalConjectures/Paper/CatchUpConjecture.lean',
                  'FormalConjectures/GameTheory/CatchUpConjecture.lean'))


def check(source_repository=None):
    manifest = json.loads((ROOT / 'verification/legacy-sources.json').read_text())
    rows = manifest['records']
    by_id = {r['id']: r for r in rows}
    require(len(by_id) == len(rows), 'duplicate source IDs')
    require(len({(r['original_path'], r['git_blob']) for r in rows}) == len(rows), 'duplicate source versions')
    commits = manifest['commits_inspected']
    require(len(set(commits)) == len(commits), 'duplicate source commits')
    require(all(re.fullmatch('[0-9a-f]{40}', c) for c in commits), 'bad source commit')
    prior = json.loads((ROOT / 'archive/inventory.json').read_text())['paths']
    prior_by_hash = {r['original_sha256']: r for r in prior}
    exported = []
    for r in rows:
        require(re.fullmatch('[0-9a-f]{40}', r['git_blob']), 'bad Git blob')
        require(re.fullmatch('[0-9a-f]{64}', r['original_sha256']), 'bad original hash')
        require(r['observed_commits'] and set(r['observed_commits']) <= set(commits), 'missing source context')
        require(set(r['branch_tips']) <= set(manifest['branches']), 'unlisted source branch')
        disposition = r['disposition']
        if disposition == 'exported historical record':
            data = artifact(r['export_path'], r['export_sha256'], r['export_bytes'])
            require(r['evidence'] and r['adaptations'], 'unlabeled historical source')
            exported.append(r['export_path'])
            path = Path(r['export_path'])
            if path.suffix == '.json':
                json.loads(data)
            if path.suffix == '.jsonl':
                for line in data.splitlines():
                    if line.strip():
                        json.loads(line)
            if path.suffix == '.md':
                require(data.startswith(b'> **Historical campaign record.'), 'missing banner')
        elif disposition == 'already represented byte-for-byte':
            artifact(r['existing_path'], r['original_sha256'], r['bytes_original'])
        elif disposition == 'covered by prior historical inventory':
            require(r['original_sha256'] in prior_by_hash and r['reason'], 'unjustified prior coverage')
        else:
            require(False, 'unrecognized disposition: ' + disposition)
    for row in manifest['handoffs'] + [manifest['run_record'], manifest['notebook_index']]:
        artifact(row['path'], row['sha256'], row['bytes'])
    multi = {r['original_path'] for r in rows if sum(s['original_path'] == r['original_path'] for s in rows) > 1}
    require(multi == {r['original_path'] for r in manifest['version_comparison']}, 'missing version comparisons')
    for change in manifest['version_comparison']:
        expected = {r['id'] for r in rows if r['original_path'] == change['original_path']}
        require(expected == {r['source_id'] for r in change['versions']}, 'missing old version')
    notebook = json.loads((ROOT / manifest['notebook_index']['path']).read_text())['entries']
    require(len({r['id'] for r in notebook}) == len(notebook), 'duplicate notebook IDs')
    for row in notebook:
        require(row['source_id'] in by_id, 'missing notebook provenance')
        lines = (ROOT / row['path']).read_text().splitlines()
        require(lines[row['line'] - 1].lstrip('# ') == row['title'], 'notebook locator changed')
        body = '\n'.join(lines[row['line']:row['end_line']]).strip()
        require(digest(body.encode()) == row['body_sha256'], 'notebook section changed')
    findings = json.loads((ROOT / 'results/legacy-findings.json').read_text())['findings']
    require(len({r['id'] for r in findings}) == len(findings), 'duplicate finding IDs')
    guide = (ROOT / 'results/legacy-findings.md').read_text()
    for row in findings:
        for key in ('claim', 'evidence', 'scope', 'role', 'relationship', 'limitations', 'next_step', 'reproduction'):
            require(row[key], 'unlabeled finding: ' + row['id'] + '/' + key)
        require(row['records'] and row['source_paths'], 'finding without source')
        require(set(row['source_ids']) <= set(by_id), 'finding without source pin')
        require(row['id'] in guide, 'finding missing from readable guide')
        for path in row['records'] + row['current_modules']:
            require((ROOT / path).is_file(), 'missing finding artifact: ' + path)
    for row in manifest['missing_artifacts']:
        require(row['source_id'] in by_id and row['availability'], 'unlabeled missing artifact')
        require(row['reported_sha256'] is None or re.fullmatch('[0-9a-f]{64}', row['reported_sha256']), 'bad reported hash')
    actual = {'refs': len(manifest['branches']), 'commits': len(commits),
              'unique_paths': len({r['original_path'] for r in rows}), 'path_blob_pairs': len(rows),
              'new_source_versions': len(exported), 'handoffs': len(manifest['handoffs']),
              'historical_run_records': 1, 'notebook_entries': len(notebook),
              'missing_artifact_references': len(manifest['missing_artifacts']), 'findings': len(findings)}
    require(actual == manifest['counts'], 'stale archive counts')
    receipt = json.loads((ROOT / 'verification/legacy-import.json').read_text())
    require(receipt['counts'] == actual, 'stale import receipt counts')
    require(receipt['source_manifest_sha256'] == digest((ROOT / 'verification/legacy-sources.json').read_bytes()),
            'receipt names a different source manifest')
    require(receipt['finding_ledger_sha256'] == digest((ROOT / 'results/legacy-findings.json').read_bytes()),
            'receipt names a different finding ledger')
    for name, expected in receipt['receipts'].items():
        require(digest((ROOT / 'verification/receipts' / name).read_bytes()) == expected,
                'changed verification receipt: ' + name)
    tracked = set(exported + [r['path'] for r in manifest['handoffs']] +
                  [manifest['run_record']['path'], manifest['notebook_index']['path'], 'archive/campaigns/README.md'])
    files = {str(p.relative_to(ROOT)) for p in (ROOT / 'archive/campaigns').rglob('*') if p.is_file()}
    require(files == tracked, 'unmanifested or missing archive files')
    forbidden = r'[/]Users/|[/]private/(?:tmp|var)/|gh[opusr]_[A-Za-z0-9]{20,}|usage.*\d+%|\d+%.*remaining'
    for path in tracked:
        require(not re.search(forbidden, (ROOT / path).read_text(), re.I), 'private detail: ' + path)
        require(not path.endswith('.lean'), 'historical source enters Lean build')
    # The same predicates must reject a damaged fingerprint and a private-path fixture.
    try:
        artifact(manifest['run_record']['path'], '0' * 64, manifest['run_record']['bytes'])
    except ValueError:
        pass
    else:
        raise ValueError('corruption control accepted')
    require(bool(re.search(forbidden, '/' + 'Users/example/private')), 'privacy control failed')
    if source_repository:
        def git(*args):
            return subprocess.check_output(['git', '-C', str(source_repository), *args], timeout=60)
        for row in rows:
            raw = git('cat-file', 'blob', row['git_blob'])
            require(digest(raw) == row['original_sha256'] and len(raw) == row['bytes_original'], 'original source hash mismatch')
        observed = set()
        for commit in commits:
            for line in git('ls-tree', '-r', commit).decode().splitlines():
                meta, path = line.split('\t', 1)
                if relevant(path):
                    observed.add((path, meta.split()[2]))
        require(observed == {(r['original_path'], r['git_blob']) for r in rows}, 'incomplete original history coverage')
        print('Original Git source audit passed: all inspected trees and original hashes')
    print('Legacy archive passed: ' + ', '.join(str(v) + ' ' + k for k, v in actual.items()))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-repository', type=Path)
    check(parser.parse_args().source_repository)
