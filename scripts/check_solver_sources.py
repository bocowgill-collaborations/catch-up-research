#!/usr/bin/env python3
"""Check solver-export provenance, dependency closure and frozen input coverage."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def digest_matches(data, expected):
    return hashlib.sha256(data).hexdigest() == expected


def main():
    m = json.loads((ROOT/'verification/solver-sources.json').read_text())
    rows = m['sources'] + m['adapters']
    assert len({r['path'] for r in rows}) == len(rows)
    actual = set()
    for folder in ['computation/experiments', 'computation/solvers']:
        actual.update(str(p.relative_to(ROOT)) for p in (ROOT/folder).rglob('*')
                      if p.is_file() and p.suffix != '.md' and '__pycache__' not in p.parts)
    assert actual == {r['path'] for r in rows if r['path'].startswith('computation/')}
    for r in rows:
        path = ROOT/r['path']
        assert ROOT in path.resolve().parents
        data = path.read_bytes()
        assert digest_matches(data, r['sha256']), r['path']
        assert len(data) == r['bytes']
        if 'original_sha256' in r:
            assert r['adaptations'] and r['origin_path']
            if r['adaptations'].startswith('None;'):
                assert r['sha256'] == r['original_sha256']
            else:
                assert r['path'].endswith('consecutive/probe.cpp')
                restored = data.replace(b'../seven_pairs/slots.hpp', b'../../../../seven_pairs/slots.hpp')
                assert digest_matches(restored, r['original_sha256'])
        if path.suffix in ('.cpp', '.hpp'):
            for include in re.findall(r'^#include "([^"]+)"', data.decode(), re.M):
                dependency = (path.parent/include).resolve()
                assert dependency.is_file() and ROOT in dependency.parents, include
                assert str(dependency.relative_to(ROOT)) in {r['path'] for r in rows}
    # Frozen lists and scope sizes are measured from supplied files, not inferred from outcomes.
    exp = ROOT/'computation/experiments'
    root_shapes = (exp/'seven_pairs/root_inputs.txt').read_text().splitlines()
    residuals = (exp/'seven_pairs/round_inputs.txt').read_text().splitlines()
    orphans = (exp/'four_orphan/inputs.txt').read_text().splitlines()
    assert len(root_shapes) == len(set(root_shapes)) == 594
    assert len(residuals) == 142
    assert len(orphans) == len(set(orphans))
    assert all(len(s.split()) == 7 for s in root_shapes)
    assert all(len(s.split()) in (3, 5) for s in residuals)
    assert all(len(s.split()) == 4 for s in orphans)
    assert m['coverage']['not_yet_ported']
    assert not digest_matches(b'changed', hashlib.sha256(b'original').hexdigest())
    print('Solver source checks passed: %s preserved inputs/sources, %s adapters; '
          '%s seven-pair, %s residual, %s orphan supports; hashes and include closure' %
          (len(m['sources']), len(m['adapters']), len(root_shapes), len(residuals), len(orphans)))


if __name__ == '__main__':
    main()
