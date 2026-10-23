#!/usr/bin/env python3
"""One fixed support's prescribed parity-preserving mutations; no retuning."""
from pathlib import Path
import collections,hashlib,itertools,json,resource,subprocess,sys,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
sys.dont_write_bytecode=True;sys.path.insert(0,str(ROOT));from verify import absolute
start=time.monotonic();base=[2,4,7,13,15,19,36,37,50,57,60,99]
source=HERE.parent/'shadow-proof/adaptive_fixed.jsonl'
old=next(json.loads(l) for l in source.read_text().splitlines() if json.loads(l)['name']=='actualR1')
assert old['support']==base and old['value']==0 and [int(x) for x,v in old['moves'].items() if v>=0]==[13]
items={};rejected=[]
def add(edits,kind):
    changes=dict(edits);support=sorted(changes.get(x,x) for x in base)
    origin=dict(kind=kind,edits=[dict(before=x,after=y) for x,y in edits])
    if len(set(support))!=12 or support[0]!=2 or any(x<3 for x in support[1:]) or support==base:
        rejected.append(dict(origin,reason='duplicate labels, invalid minimum, or unchanged support'));return
    assert sum(support)%2==1
    items.setdefault(tuple(support),[]).append(origin)
for x in base[1:]:
    for delta in (-2,2):add([(x,x+delta)],'one_label_plus_or_minus_two')
for x,y in itertools.combinations(base[1:],2):
    for dx,dy in itertools.product((-1,1),repeat=2):add([(x,x+dx),(y,y+dy)],'two_labels_plus_or_minus_one')
# First remove the previously unique defense13; then prioritize single edits;
# final tie-break is the exact support, fixed before any evaluation.
ordered=sorted(items,key=lambda s:(13 in s,min(len(p['edits']) for p in items[s]),s))
assert len(ordered)<=500
rows=[dict(id=i,support=list(s),provenance=items[s],preserves_old_defense13=13 in s,
           assumed_outcome_preservation=False) for i,s in enumerate(ordered,1)]
controlids=sorted(set([1,1+len(rows)//2,len(rows)]))
seeds=dict(base_support=base,base_source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
           base_unique_safe_pick=13,ordered_queries=rows,rejected_mutations=rejected,
           order='13 absent first, then smallest edit arity, then exact support lexicographic',
           predetermined_literal_control_ids=controlids)
(HERE/'seeds.json').write_text(json.dumps(seeds,indent=2)+'\n')
inputs=''.join(str(r['id'])+' 12 '+' '.join(map(str,r['support']))+'\n' for r in rows)
(HERE/'input.txt').write_text(inputs)
checkpoint=dict(phase='saved_planned_inputs',planned=len(rows),completed=0,unprocessed_ids=[r['id'] for r in rows],active_jobs=[])
(HERE/'checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
c=subprocess.run(['clang++','-O2','-std=c++17',str(HERE/'probe.cpp'),'-o',str(HERE/'probe')],capture_output=True,text=True,timeout=30)
(HERE/'compile.out').write_text(c.stdout+c.stderr);assert c.returncode==0
def limit():resource.setrlimit(resource.RLIMIT_CPU,(15,16))
checkpoint.update(phase='native_probe_running',native_command=[str(HERE/'probe')],cpu_limit_seconds=15,wall_limit_seconds=30)
(HERE/'checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
with (HERE/'probe.out').open('w') as output:
    p=subprocess.run([str(HERE/'probe')],input=inputs,text=True,stdout=output,stderr=subprocess.PIPE,timeout=30,preexec_fn=limit)
(HERE/'probe.stderr').write_text(p.stderr)
records=[];caps=[]
for line in (HERE/'probe.out').read_text().splitlines():
    r=json.loads(line)
    if 'id' not in r:caps.append(r);continue
    assert r['id']==len(records)+1;r.update(rows[r['id']-1]);r['safe_choices']=[int(x) for x,v in r['moves'].items() if v>=0]
    assert len(r['moves'])==12 and max(r['moves'].values())==r['value'];records.append(r)
losses=[r for r in records if r['value']==-1];assert len(losses)<=1 and (not losses or losses[0]['id']==records[-1]['id'])
checkpoint.update(phase='native_complete_literal_pending',completed=len(records),exit_code=p.returncode,
                  unprocessed_ids=[r['id'] for r in rows[len(records):]],active_jobs=[])
(HERE/'checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
chosen=losses or [r for r in records if r['id'] in controlids];literal=[]
for r in chosen:
    s=tuple(r['support']);absolute.cache_clear();v=absolute(s,0,1)
    moves={str(x):-absolute(tuple(y for y in s if y!=x),1,x) for x in s}
    assert v==r['value'] and moves==r['moves'];literal.append(dict(id=r['id'],value=v,all_moves=moves,pass_=True))
result=dict(scope='One fixed-support mutation neighborhood; no general theorem or outcome-preserving quotient',
            planned=len(rows),completed=len(records),outcome_counts=dict(collections.Counter(r['value'] for r in records)),
            records=records,first_loss=losses[0] if losses else None,literal=literal,
            caps=caps,exit_code=p.returncode,unprocessed=rows[len(records):],
            old13_absent=sum(13 not in r['support'] for r in records),
            old13_present_and_loses=sum(r['moves'].get('13')==-1 for r in records),
            unique_safe_pick_counts=dict(collections.Counter(r['safe_choices'][0] for r in records if len(r['safe_choices'])==1)),
            seconds=time.monotonic()-start,max_child_rss_bytes=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
            ExactSlots_sha256=hashlib.sha256((ROOT/'seven_pairs/slots.hpp').read_bytes()).hexdigest(),
            literal_source_sha256=hashlib.sha256((ROOT/'verify.py').read_bytes()).hexdigest(),active_jobs=[])
(HERE/'results.json').write_text(json.dumps(result,indent=2)+'\n')
checkpoint.update(phase='complete' if len(records)==len(rows) else 'first_loss' if losses else 'resource_stop',
                  literal_completed_ids=[r['id'] for r in literal],active_jobs=[])
(HERE/'checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['planned','completed','outcome_counts','first_loss','seconds','old13_absent','old13_present_and_loses','unique_safe_pick_counts']}),flush=True)
