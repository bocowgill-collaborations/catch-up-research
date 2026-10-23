#!/usr/bin/env python3
"""Publication provenance, dependency and privacy checks; starts no solver."""
import ast
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[1]


def public_text(text):
    forbidden=r'[/]Users/|[/]private/var/|[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}|gh[opusr]_[A-Za-z0-9]{20,}|BEGIN (?:RSA |OPENSSH )?PRIVATE KEY'
    return re.search(forbidden,text) is None


def main():
    m=json.loads((ROOT/'verification/campaign-sources.json').read_text())
    old=json.loads((ROOT/'verification/solver-sources.json').read_text())
    rows=m['sources']+m['adapters']; paths={r['path'] for r in rows}
    allpaths=paths|{r['path'] for r in old['sources']+old['adapters']}
    assert len(paths)==len(rows)
    source=(ROOT/'computation/experiments/campaign/resume_01/shadow-smt/search.py').read_text()
    encoding=next(n for n in ast.parse(source).body if isinstance(n,ast.ClassDef) and n.name=='Encoding')
    assert hashlib.sha256(ast.dump(encoding,include_attributes=False).encode()).hexdigest()==m['encoding_class_ast_sha256']
    actual={str(p.relative_to(ROOT)) for p in (ROOT/'computation/experiments/campaign').rglob('*')
            if p.is_file() and p.name!='README.md' and '__pycache__' not in p.parts}
    assert actual=={r['path'] for r in m['sources']}
    for r in rows:
        p=ROOT/r['path'];assert ROOT in p.resolve().parents
        b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==r['sha256'],r['path']
        assert len(b)==r['bytes'] and public_text(b.decode()),r['path']
        assert not any(s in p.parts for s in ['private_vonstengel_audit_2026_10_23','automations'])
        if p.suffix=='.py':ast.parse(b.decode(),filename=r['path'])
        if p.suffix=='.json':json.loads(b)
        if p.suffix in ('.cpp','.hpp'):
            for include in re.findall(r'^#include "([^"]+)"',b.decode(),re.M):
                dep=(p.parent/include).resolve()
                assert dep.is_file() and str(dep.relative_to(ROOT)) in allpaths,include
    for closure in m['closures']:
        assert closure['entrypoints'] and closure['inputs']
        assert all(p in allpaths for p in closure['entrypoints']+closure['inputs'])
    for q in m['smt_queries']:
        assert q['historical_result'] in ('sat','unsat','unknown')
        if q['frozen_path']:
            b=(ROOT/q['frozen_path']).read_bytes()
            assert hashlib.sha256(b).hexdigest()==q['original_sha256'] and len(b)==q['bytes']
    exp=ROOT/'computation/experiments/campaign'
    search=exp/'search'
    seeds=json.loads((search/'root_anchor_jointloss_mutation_seeds.json').read_text())['actual_explicit_list']
    lines=(search/'root_anchor_jointloss_mutation_seeds.txt').read_text().splitlines()
    pending=(search/'root_anchor_jointloss_mutation_remaining_seeds.txt').read_text().splitlines()
    assert len(seeds)==len(lines)==18741 and pending==lines[11149:]
    for r,line in zip(seeds,lines):
        fields=list(map(int,line.split()))
        assert fields[0]==r['id'] and fields[7]==len(r['T']) and fields[8:]==r['T']
    checkpoint=json.loads((search/'root_anchor_jointloss_mutation_checkpoint.json').read_text())
    assert (checkpoint['planned'],checkpoint['completed'],checkpoint['unprocessed'])==(18741,11149,7592)
    adaptive=exp/'resume_01/two-guard-adaptive-mutation'
    plan=json.loads((adaptive/'seeds.json').read_text())['ordered_queries']
    checkpoint=json.loads((adaptive/'checkpoint.json').read_text())
    assert len(plan)==len((adaptive/'input.txt').read_text().splitlines())==199
    assert checkpoint['completed']==40 and checkpoint['unprocessed_ids']==list(range(41,200))
    assert len(m['inventory'])==len({r['origin_path'] for r in m['inventory']})
    assert all(r['disposition'] for r in m['inventory'])
    assert m['privacy_exclusions']
    assert not public_text('person'+'@'+'example.org')
    assert not public_text('/'+'Users/person/private.txt')
    assert not public_text('-----BEGIN'+' OPENSSH PRIVATE KEY-----')
    print('Campaign source checks passed: %s preserved sources/data, %s adapters, %s query recipes; '
          'dependencies, frozen prefixes, privacy controls and hashes' %
          (len(m['sources']),len(m['adapters']),len(m['smt_queries'])))


if __name__=='__main__':main()
