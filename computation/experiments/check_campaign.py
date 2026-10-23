#!/usr/bin/env python3
"""Small independent publication checks: no full mutation, shrink or SMT extension run."""
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import run_campaign as campaign
import run
from check import agrees, reject, require
from verify import absolute


def check_dag(data):
    """Experimental independent replay of the small frozen 19-node loss witness."""
    previous={}
    for n in data['nodes']:
        s=n['support'];d=n['deficit']
        require(n['id']==len(previous)+1 and s==sorted(set(s)), 'invalid DAG label/order')
        require(n['card']==len(s) and n['terminal']==(not s or sum(s)<d), 'terminal mismatch')
        require(n['value'] in (-1,1), 'unexpected DAG payoff')
        if n['kind']=='leaf':
            require(not n['edges'] and (len(s)<=7 or n['terminal']), 'invalid leaf')
            require(absolute(tuple(s),0,d)==n['value'], 'false leaf')
        else:
            if n['value']==-1:
                require(n['kind']=='loss' and sorted(e['pick'] for e in n['edges'])==s,
                        'missing opponent branch')
            else:
                require(n['kind']=='win' and len(n['edges'])==1, 'missing winning choice')
            for e in n['edges']:
                require(e['child'] in previous and e['pick'] in s, 'illegal or circular edge')
                child=previous[e['child']];x=e['pick']
                require(child['support']==[y for y in s if y!=x] and child['deficit']==abs(x-d),
                        'wrong child state')
                require(e['switches']==(x>=d) and e['child_value']==child['value'], 'wrong perspective')
                require(n['value']==(-child['value'] if x>=d else child['value']), 'wrong edge value')
        previous[n['id']]=n
    require(len(data['roots'])==1, 'missing root')
    r=data['roots'][0];n=previous[r['node']]
    require(r['value']==n['value']==-1 and n['deficit']==1 and
            n['support']==[4,7,19,36,37,50,57,60,99], 'wrong root')


def main():
    with tempfile.TemporaryDirectory(prefix='catchup-campaign-') as tmp:
        out=Path(tmp);binary=out/'positions';run.build(HERE/'consecutive/probe.cpp',binary)
        # Exercise output-before-input backpressure independently of the C++ game code.
        payload='x'*262144
        raw=run.bounded([sys.executable,'-c',
                        'import sys; sys.stdout.write("y"*262144); sys.stdout.flush(); '
                        'print(len(sys.stdin.read()))'],cwd=out,seconds=3,memory_mib=256,stdin=payload)
        require(raw.endswith('262144\n') and raw.startswith('y'*262144), 'batch I/O lost data or blocked')
        counts={}
        for profile in ['mutation-joint','mutation-two','shrink-joint','shrink-alternating']:
            rows,scope=campaign.selected_positions(profile)
            result=run.positions(binary,rows,out/(profile+'.jsonl'),10,256)
            for row in result:agrees(row)
            if profile=='mutation-joint':
                require(all(r['value']==-1 for r in result if r['original_id']==11149),
                        'saved double loss not reproduced')
            elif profile=='mutation-two':
                require(result[-1]['original_id']==40 and result[-1]['value']==-1,
                        'saved minimum-two loss not reproduced')
            elif profile=='shrink-joint':
                require(result[0]['value']==result[1]['value']==-1,'fixed original witness is not a double loss')
                require(all(result[i]['value']>=0 or result[i+1]['value']>=0
                            for i in range(2,len(result),2)), 'one-deletion neighbor is a double loss')
            else:
                require(result[0]['value']==-1 and all(r['value']>=0 for r in result[1:]),
                        'saved local coordinate fixed point not reproduced')
            counts[profile]=len(rows)
        # Reproduce original native drivers on a few frozen rows only, not their whole batches.
        source=campaign.CAMPAIGN/'search/root_anchor_jointloss_mutation_probe.cpp'
        run.build(source,out/'mutation')
        lines=(source.parent/'root_anchor_jointloss_mutation_seeds.txt').read_text().splitlines()
        smoke=out/'mutation.input.txt';smoke.write_text(lines[11148]+'\n')
        raw=run.bounded([str(out/'mutation'),str(smoke)],cwd=out,seconds=10,memory_mib=256)
        require('STOP_FIRST_DOUBLELOSS completed 1 ' in raw, 'original mutation witness missing')
        for line in raw.splitlines():
            if not line.startswith('STATE '):continue
            fields=line.split();fields=dict(zip(fields[1::2],fields[2::2]))
            support=list(map(int,fields['remaining'].rstrip(',').split(',')))
            moves={x:int(v) for x,v in (s.split(':') for s in fields['moves'].rstrip(',').split(','))}
            agrees(dict(support=support,deficit=int(fields['deficit']),value=int(fields['value']),moves=moves))
        source=campaign.CAMPAIGN/'resume_01/two-guard-adaptive-mutation/probe.cpp'
        run.build(source,out/'adaptive')
        lines=(source.parent/'input.txt').read_text().splitlines()
        raw=run.bounded([str(out/'adaptive')],cwd=out,seconds=10,memory_mib=256,
                        stdin=lines[0]+'\n'+lines[39]+'\n')
        records=list(map(json.loads,raw.splitlines()))
        require([r['id'] for r in records]==[1,40] and records[-1]['value']==-1,
                'adaptive stopped-prefix witness mismatch')
        # Same finalized nine-counter DAG; no root or support search.
        dag=json.loads((campaign.CAMPAIGN/'search/root_alternating_gap_shrink_certificate7.json').read_text())
        check_dag(dag)
        bad=copy.deepcopy(dag);bad['nodes'][-1]['edges'].pop()
        reject(lambda:check_dag(bad),AssertionError)
        bad=copy.deepcopy(dag);bad['nodes'][-1]['edges'][0]['child']=bad['nodes'][-1]['id']
        reject(lambda:check_dag(bad),AssertionError)
        # Reconstruct and solve only tiny historical arities; compare exact input hashes.
        recipes=campaign.recipes()
        for family,k in [('shadow-smt',0),('two-guard-smt',2)]:
            r=next(r for r in recipes if r['family']==family and r['tail_cardinality']==k and
                   not r['name'].endswith('_shadow_only'))
            target=out/family;target.mkdir()
            require(campaign.solve_smt(campaign.query(r),target,5,256)['solver_result']=='unsat',
                    'small historical SMT result mismatch')
        # Every original golden root, shifted score and fixed-player second-mover sign.
        b=campaign.load_encoding();e=b.Encoding(3000);conditions=[]
        validation=json.loads((campaign.CAMPAIGN/'resume_01/shadow-smt/validation.json').read_text())
        for i,fixture in enumerate(validation['golden_cases']):
            s=tuple(fixture['labels']);d=fixture['deficit'];v=absolute(s,0,d)
            require(v==fixture['expected']==absolute(s,17,17+d), 'golden/score-shift mismatch')
            root=e.root('g%s'%i,s,d)
            conditions += ['(= %s %s)'%(root,b.number(v)),
                           '(= g%s_0_0_1 %s)'%(i,b.number(-absolute(s,d,0)))]
        for label,text,expected in [
                ('goldens',e.query(conditions),'sat'),
                ('no-mismatch',e.query(['(not (and %s))'%' '.join(conditions)]),'unsat'),
                ('wrong-outcome',e.query(['(= g2_0_0_0 (- 1))']),'unsat')]:
            target=out/label;target.mkdir()
            require(campaign.solve_smt(text,target,5,256)['solver_result']==expected, 'SMT golden control')
        s,d,good,wrong=validation['broken_alternation_example']
        bad=b.Encoding(3000);root=bad.root('bad',s,d,True)
        for label,value,expected in [('bad-good',good,'unsat'),('bad-wrong',wrong,'sat')]:
            target=out/label;target.mkdir()
            require(campaign.solve_smt(bad.query(['(= %s %s)'%(root,b.number(value))]),target,5,256)
                    ['solver_result']==expected, 'always-alternate mutation not detected')
        # Unknown, solver errors and timeouts must never become a mathematical result.
        original_z3=os.environ.get('Z3')
        try:
            fake=out/'fake-z3';os.environ['Z3']=str(fake)
            for i,body in enumerate(['print("unknown")','print("unsat\\n(error \\\"bad\\\")")',
                                     'print("unsat"); raise SystemExit(3)',
                                     'import time; time.sleep(2)']):
                fake.write_text('#!'+sys.executable+'\n'+body+'\n');fake.chmod(0o700)
                target=out/('invalid-smt-%s'%i);target.mkdir()
                reject(lambda:campaign.solve_smt('(check-sat)',target,0.05 if i==3 else 2,256),
                       run.Incomplete)
        finally:
            if original_z3 is None:os.environ.pop('Z3',None)
            else:os.environ['Z3']=original_z3
        # Portable original layout: regenerate inputs only and replay a nine-leaf DAG audit.
        work=out/'legacy';work.mkdir();campaign.prepare(work)
        search=work/'campaign/search'
        for script,filename in [('root_anchor_jointloss_mutation_seeds.py','root_anchor_jointloss_mutation_seeds.txt'),
                                ('root_alternating_gap_generate.py','root_alternating_gap_seeds.txt')]:
            run.bounded([sys.executable,str(search/script)],cwd=work,seconds=10,memory_mib=512)
            require((search/filename).read_bytes()==(campaign.CAMPAIGN/'search'/filename).read_bytes(),
                    'original seed generator changed the frozen input list')
        script=work/'campaign/resume_01/two-guard-adaptive-mutation/run.py'
        # This original file combines planning and search. Execute only its planning prefix.
        prefix=script.read_text().split("c=subprocess.run(",1)[0]
        planner=script.with_name('plan_only.py');planner.write_text(prefix)
        run.bounded([sys.executable,str(planner)],cwd=work,seconds=5,memory_mib=256)
        require((script.parent/'input.txt').read_bytes()==
                (campaign.CAMPAIGN/'resume_01/two-guard-adaptive-mutation/input.txt').read_bytes(),
                'adaptive mutation generator changed frozen inputs')
        audit=search/'root_alternating_gap_shrink_certificate7_check.py'
        raw=run.bounded([sys.executable,str(audit)],cwd=work,seconds=10,memory_mib=256)
        require('COMPLETE_CERTIFICATE_AUDIT 19 nodes 9 literal_leaves 18 edges' in raw,
                'original small DAG audit failed')
        # Compile remaining original shrinking/export drivers; do not execute their full searches.
        for i,name in enumerate(['root_anchor_jointloss_shrink_probe.cpp',
                                 'root_alternating_gap_shrink_probe.cpp',
                                 'root_alternating_gap_shrink_certificate7.cpp']):
            run.build(search/name,out/('compile-only-%s'%i))
        print('Campaign smoke checks passed: %s fixed positions, every reported first pick, '
              'original mutation witnesses, 16 SMT goldens and both mover signs, '
              '19-node DAG, seeds, incomplete-result and corruption controls; no large batch' % sum(counts.values()))


if __name__=='__main__':main()
