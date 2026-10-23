#!/usr/bin/env python3
"""At most twenty explicit transformations of known losing geometries."""
from pathlib import Path
import importlib.util,subprocess,json,time,hashlib,resource
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('reuse',HERE/'search.py')
reuse=importlib.util.module_from_spec(spec);spec.loader.exec_module(reuse)
absolute=reuse.base.absolute
start=time.monotonic()
complete=[1,2,3,7,14,23,37,68,101,111,123]
six=[2,5,6,9,11,13]
cycle=[9,16,17,18,26,28,31,37]
rows=[]
def add(s,origin,change,source):
    s=sorted(s)
    assert s==sorted(set(s)) and s[0]==2 and sum(s)%2==1 and len(s)<=14
    rows.append(dict(id=len(rows)+1,support=s,origin=origin,transformation=change,source_support=source,
                     assumed_outcome_preservation=False))
add(complete[1:],'prior complete even root LOSS','delete counter1; parity already odd',complete)
for x in six[1:]:
    for delta in (-1,1):
        y=x+delta
        if y>=3 and y not in six:
            add([y if a==x else a for a in six],'prior six-label even root LOSS',f'change {x} to {y}; preserve2',six)
for delta in (-1,1):
    add([2]+cycle[:-1]+[cycle[-1]+delta],'prior shifted-cycle even root LOSS',f'insert2 and change37 to{37+delta}',cycle)
tails=[('old doubleLOSS',[18,33,35,36,52,56,62,74,100]),
       ('old rounded alternating E1LOSS',[19,36,37,52,57,62,101]),
       ('old compressed alternating E1LOSS',[19,36,37,50,57,60,99])]
for origin,t in tails:
    add([2,3,4]+t,origin,'C8 first7 endpoint {2,3,4} union tail', [4,7]+t)
assert len(rows)<=20
(HERE/'controls_seeds.json').write_text(json.dumps(rows,indent=2)+'\n')
inputs=''.join(str(a['id'])+' '+str(len(a['support']))+' '+' '.join(map(str,a['support']))+'\n' for a in rows)
(HERE/'controls_input.txt').write_text(inputs)
compiled=subprocess.run(['clang++','-O2','-std=c++17',str(HERE/'controls.cpp'),'-o',str(HERE/'controls')],capture_output=True,text=True,timeout=30)
(HERE/'controls_compile.out').write_text(compiled.stdout+compiled.stderr);assert compiled.returncode==0
run=subprocess.run([str(HERE/'controls')],input=inputs,capture_output=True,text=True,timeout=30)
(HERE/'controls_native.out').write_text(run.stdout+run.stderr);assert run.returncode==0
out=[json.loads(l) for l in run.stdout.splitlines()]
for record in out:
    seed=rows[record['id']-1];s=tuple(seed['support']);absolute.cache_clear()
    v=absolute(s,0,1)
    moves={str(x):-absolute(tuple(y for y in s if y!=x),1,x) for x in s}
    assert v==record['value'] and moves==record['moves'] and max(moves.values())==v
    record.update(seed,literal_value=v,literal_all_moves=moves,literal_pass=True)
    if v==-1:break
result={'planned_cases':len(rows),'completed_cases':len(out),'results':out,
        'unprocessed_ids':[r['id'] for r in rows[len(out):]],'stop_on_first_loss':True,
        'seconds':time.monotonic()-start,'max_self_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'max_child_rss_bytes':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
        'frozen_ExactSlots_sha256':hashlib.sha256((HERE.parents[2]/'seven_pairs/slots.hpp').read_bytes()).hexdigest(),
        'literal_source_sha256':hashlib.sha256((HERE.parents[2]/'verify.py').read_bytes()).hexdigest(),
        'scope':'Explicit transformed supports only; no assumed quotient/preservation; no Lean result'}
(HERE/'controls_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'completed':len(out),'outcomes':[r['value'] for r in out],'seconds':result['seconds']}),flush=True)
