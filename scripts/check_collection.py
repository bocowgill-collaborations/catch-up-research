#!/usr/bin/env python3
"""Check collection coverage and the small solver independently of Lean installation."""
from pathlib import Path
import importlib.util
import json
import re
import subprocess
import sys
import time
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

def rejected(action,error):
    try:action()
    except error:return
    raise AssertionError('expected rejection')

def main():
    begin=time.monotonic()
    catalog=json.loads((ROOT/'results/catalog.json').read_text())['modules']
    actual={str(p.relative_to(ROOT)) for p in (ROOT/'CatchUp').rglob('*.lean')}
    assert len(catalog)==len({e['path'] for e in catalog})
    assert {e['path'] for e in catalog}==actual
    guide=(ROOT/'results/modules.md').read_text()
    for entry in catalog:
        assert entry['summary'] and entry['evidence'] and entry['group']
        source=(ROOT/entry['path']).read_text()
        assert re.findall(r'^theorem\s+([^\s(:]+)',source,re.M)==entry['public_theorem_names']
        assert f"(../{entry['path']})" in guide
    ports=json.loads((ROOT/'verification/earlier-sources.json').read_text())
    for item in ports['sources']:
        raw=(ROOT/item['original_input']).read_bytes()
        assert __import__('hashlib').sha256(raw).hexdigest()==item['original_source_sha256']
        adapted=raw.decode()
        for old,new in sorted(ports['module_reference_map'].items(),key=lambda pair:-len(pair[0])):
            adapted=re.sub(r'(?<![\w.])'+re.escape(old)+r'(?![\w.])',new,adapted)
        def ordinary_attributes(match):
            attrs=[a.strip() for a in match[1].split(',') if not a.strip().startswith(('category ','AMS '))]
            return '@['+', '.join(attrs)+']\n' if attrs else ''
        adapted=re.sub(r'^@\[([^\n]*)\]\n',ordinary_attributes,adapted,flags=re.M)
        if item['module']=='CatchUp.Earlier.TopFourClassification':
            adapted=adapted.replace('import CatchUp.Reference\n','import CatchUp.Reference\nimport CatchUp.PairClassification\n')
            adapted=re.sub(r'\bvalue_pair_exact\b','earlier_value_pair_exact',adapted)
        assert adapted==(ROOT/item['path']).read_text(),item['path']
    archive=json.loads((ROOT/'archive/inventory.json').read_text())['paths']
    for entry in archive:
        if 'archive_path' in entry:
            data=(ROOT/entry['archive_path']).read_bytes()
            assert __import__('hashlib').sha256(data).hexdigest()==entry['original_sha256']
            assert len(data)==entry['bytes']
    sources=json.loads((ROOT/'docs/sources.json').read_text())['sources']
    assert len({e['id'] for e in sources})==len(sources)
    for source in sources:
        assert source['url'].startswith('https://') and source['evidence']
        if 'commit' in source:assert re.fullmatch('[0-9a-f]{40}',source['commit'])
    solver=load('collection_explore',ROOT/'computation/explore.py')
    absolute=load('collection_reference',ROOT/'computation/check_semantics.py').absolute
    count=0
    # All small irregular subsets and deficits; absolute scores provide an independent recurrence.
    for mask in range(64):
        counters=tuple(i+1 for i in range(6) if mask&(1<<i))
        obj=solver.Solver(counters)
        for d in range(13):
            assert obj.value(obj.full,d)==absolute(counters,0,d),(counters,d)
            report=obj.report(d)
            rows=report['picks']
            assert len(rows)==(len(counters) if counters and sum(counters)>=d else 0)
            for row in rows:
                x=row['pick'];remaining=tuple(y for y in counters if y!=x)
                child=absolute(remaining,0,abs(d-x))
                assert row['turn']==('continue' if x<d else 'swap')
                assert row['child_outcome']==solver.NAMES[child]
                assert row['pick_outcome']==solver.NAMES[child if x<d else -child]
            count+=1
    for counters in [(2,4,7),(1,5,9),(4,7,13)]:
        obj=solver.Solver(counters)
        for d in range(sum(counters)+3):
            assert obj.value(obj.full,d)==absolute(counters,0,d)
            count+=1
    fixtures=json.loads((ROOT/'computation/examples.json').read_text())
    for row in fixtures['initial_intervals']:
        n=row['N'];obj=solver.Solver(range(1,n+1))
        result=obj.report()
        expected=absolute(tuple(range(1,n+1)),0,0,True)
        assert result['outcome']==row['outcome']==solver.NAMES[expected]
        winners=[x['pick'] for x in result['picks'] if x['pick_outcome']=='win']
        assert winners==row['winning_openings']
        assert len(winners)<=1
    for row in fixtures['positions']:
        result=solver.Solver(row['remaining']).report(row['deficit'])
        expected=absolute(tuple(row['remaining']),0,row['deficit'])
        assert result['outcome']==row['outcome']==solver.NAMES[expected]
        if 'pick_outcomes' in row:
            assert {str(x['pick']):x['pick_outcome'] for x in result['picks']}==row['pick_outcomes']
    # Same-player continuation is a necessary sign distinction: an always-swap mutation fails here.
    keep=solver.Solver((2,4,7)).report(3)['picks'][0]
    assert keep['turn']=='continue' and keep['pick_outcome']=='win'
    assert solver.NAMES[-absolute((4,7),0,1)]!=keep['pick_outcome']
    for counters in [(1,1),(0,1),(-1,2)]:
        rejected(lambda:solver.Solver(counters),ValueError)
    rejected(lambda:solver.Solver((1,),seconds=float('nan')),ValueError)
    rejected(lambda:solver.Solver((1,)).report(-1),ValueError)
    limited=solver.Solver((1,2,3,4),max_states=1)
    rejected(limited.report,solver.SearchLimit)
    expired=solver.Solver((1,2));expired.deadline=time.monotonic()-1
    rejected(expired.report,solver.SearchLimit)
    # Resource exhaustion must have a failure status and no mathematical outcome.
    child=subprocess.run([sys.executable,'computation/explore.py','--initial','4','--max-states','1'],cwd=ROOT,text=True,capture_output=True,timeout=10)
    incomplete=json.loads(child.stdout)
    assert child.returncode==2 and incomplete['status']=='incomplete' and 'outcome' not in incomplete
    # Existing source fidelity, copied-file hashes, documentation links and hygiene checks.
    subprocess.run([sys.executable,'scripts/check_legacy_archive.py'],cwd=ROOT,check=True,timeout=60)
    subprocess.run([sys.executable,'scripts/check_fifth_endpoint_port.py'],cwd=ROOT,check=True,timeout=60)
    subprocess.run([sys.executable,'scripts/check_legacy_examples.py'],cwd=ROOT,check=True,timeout=60)
    subprocess.run([sys.executable,'scripts/check_research_archive.py'],cwd=ROOT,check=True,timeout=60)
    subprocess.run([sys.executable,'scripts/check_solver_sources.py'],cwd=ROOT,check=True,timeout=60)
    subprocess.run([sys.executable,'scripts/check_campaign_sources.py'],cwd=ROOT,check=True,timeout=60)
    subprocess.run([sys.executable,'scripts/verify_export.py'],cwd=ROOT,check=True,timeout=60)
    print(f'Collection checks passed: {len(catalog)} indexed modules, {count} noninitial comparisons, {len(fixtures["initial_intervals"])} roots, every listed reply and limit/sign controls ({time.monotonic()-begin:.2f}s)')

if __name__=='__main__':main()
