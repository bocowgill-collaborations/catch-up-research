#!/usr/bin/env python3
"""Validate research-note/data coverage and exported hashes; never launch a search."""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]

def same_hash(data,expected):
    assert hashlib.sha256(data).hexdigest()==expected

def main():
    manifest=json.loads((ROOT/'verification/research-collection.json').read_text())
    reports=manifest['reports'];observations=manifest['observations']
    inventory=manifest['report_inventory']
    assert reports and observations
    for rows in (reports,observations):
        assert len({r['id'] for r in rows})==len(rows)
        assert len({r['path'] for r in rows})==len(rows)
        assert len({r['origin_path'] for r in rows})==len(rows)
    for r in reports+observations:
        data=(ROOT/r['path']).read_bytes()
        same_hash(data,r['sha256'])
        assert len(data)==r['bytes']
        assert r['evidence'] and r['adaptations'] and len(r['original_sha256'])==64
    for r in reports:
        text=(ROOT/r['path']).read_text()
        assert text.startswith('> **Historical research note')
        assert 'current route guide' in text
        for module in r['current_modules']:assert (ROOT/'CatchUp'/f'{module}.lean').is_file()
    for r in observations:json.loads((ROOT/r['path']).read_text())
    assert len({r['path'] for r in inventory})==len(inventory)
    assert {r['published'] for r in inventory if r['published']}=={r['path'] for r in reports}
    assert all(r['disposition'] and len(r['sha256'])==64 for r in inventory)
    note_files={str(p.relative_to(ROOT)) for p in (ROOT/'archive/research-notes').glob('*.md') if p.name!='README.md'}
    data_files={str(p.relative_to(ROOT)) for p in (ROOT/'computation/observations').glob('*.json')}
    assert note_files=={r['path'] for r in reports}
    assert data_files=={r['path'] for r in observations}
    index=(ROOT/'archive/research-notes/README.md').read_text()
    obs_index=(ROOT/'computation/observations/README.md').read_text()
    for r in reports:assert f"({Path(r['path']).name})" in index
    for r in observations:assert f"({Path(r['path']).name})" in obs_index
    try:same_hash(b'corrupted',hashlib.sha256(b'correct').hexdigest())
    except AssertionError:pass
    else:raise AssertionError('corruption control accepted')
    print(f'Research archive passed: {len(reports)} notes, {len(observations)} observations; hashes, coverage and corruption control')

if __name__=='__main__':main()
