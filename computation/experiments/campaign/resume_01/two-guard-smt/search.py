#!/usr/bin/env python3
"""Bounded falsification of min R=2, odd sum R => V(R,1) is not LOSS.

Reuse the reviewed exact ownership Encoding class unchanged; no Lean proof.
"""
from pathlib import Path
import importlib.util
import hashlib
import json
import re
import time

HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'shadow-smt/search.py'
spec=importlib.util.spec_from_file_location('reviewed_shadow_encoding',SOURCE)
base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
base.HERE=HERE  # Route only this invocation's new outputs; no source edits.

def main():
    start=time.monotonic()
    records=[]
    for k in (2,3,4,5):
        remaining=300-(time.monotonic()-start)
        if remaining<65:
            break
        e=base.Encoding(60000)
        labels=[f'u{i}' for i in range(k)]
        e.lines += [f'(declare-const {x} Int)' for x in labels]
        e.lines.append('(declare-const half Int)')
        conditions=[f'(>= {x} 3)' for x in labels]
        conditions += [f'(< {a} {b})' for a,b in zip(labels,labels[1:])]
        conditions += [f'(= {base.linear(0,{x:1 for x in labels})} (+ (* 2 half) 1))']
        root=e.root('R',[2]+labels,1)
        conditions.append(f'(= {root} (- 1))')
        name=f'query_k{k}'
        r,out=base.run(name,e.query(conditions),65)
        r.update(tail_cardinality=k,support_cardinality=k+1,ownership_states=e.states,
                 choice_edges=e.edges,claim='min R=2, odd sum R, deficit1 LOSS',
                 labels_unbounded=True,lean_certified=False)
        if r['result']=='sat':
            budget=min(65,300-(time.monotonic()-start))
            if budget>0:
                model,out=base.run(name+'_model',e.query(conditions,labels+[root]),budget)
                if model['result']=='sat' and model['exit_code']==0:
                    tail=[int(re.search(r'\('+x+r'\s+([0-9]+)\)',out)[1]) for x in labels]
                    support=tuple([2]+tail)
                    assert tail==sorted(set(tail)) and min(tail)>=3 and sum(tail)%2==1
                    base.absolute.cache_clear()
                    value=base.absolute(support,0,1)
                    moves={x:-base.absolute(tuple(y for y in support if y!=x),1,x) for x in support}
                    assert value==-1 and max(moves.values())==-1
                    r.update(witness_tail=tail,literal_support=support,literal_value=value,
                             literal_every_first_pick=moves,literal_replay='PASS')
        (HERE/(name+'.json')).write_text(json.dumps(r,indent=2)+'\n')
        records.append(r)
        summary={'target':'minR=2 and Even(sumR+1) implies V(R,1) NONLOSS',
                 'results':records,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                 'reviewed_encoding_source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                 'elapsed_seconds':time.monotonic()-start,'scope':'SMT evidence only; no Lean bridge',
                 'unprocessed_tail_cardinalities':[j for j in (2,3,4,5) if j not in [z['tail_cardinality'] for z in records]],
                 'active_jobs':[]}
        (HERE/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
        if r['result']=='sat':
            break

if __name__=='__main__':main()
