#!/usr/bin/env python3
"""One separately authorized seven-counter two-guard query, no larger arity."""
import importlib.util,json,re,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('reuse',HERE/'search.py')
reuse=importlib.util.module_from_spec(spec);spec.loader.exec_module(reuse)
b=reuse.base
e=b.Encoding(60000);us=[f'u{i}' for i in range(6)]
e.lines += [f'(declare-const {x} Int)' for x in us]+['(declare-const half Int)']
conds=[f'(>= {x} 3)' for x in us]+[f'(< {a} {c})' for a,c in zip(us,us[1:])]
conds += [f'(= {b.linear(0,{x:1 for x in us})} (+ (* 2 half) 1))']
root=e.root('R',[2]+us,1);conds += [f'(= {root} (- 1))']
r,out=b.run('extension_k6',e.query(conds),65)
r.update(tail_cardinality=6,support_cardinality=7,ownership_states=e.states,
         choice_edges=e.edges,claim='min R=2, odd sum R, deficit1 LOSS',labels_unbounded=True,lean_certified=False)
if r['result']=='sat':
    mr,out=b.run('extension_k6_model',e.query(conds,us+[root]),65)
    if mr['result']=='sat' and mr['exit_code']==0:
        tail=[int(re.search(r'\('+x+r'\s+([0-9]+)\)',out)[1]) for x in us]
        support=tuple([2]+tail);assert tail==sorted(set(tail)) and min(tail)>=3 and sum(tail)%2==1
        value=b.absolute(support,0,1)
        moves={x:-b.absolute(tuple(y for y in support if y!=x),1,x) for x in support}
        assert value==-1 and max(moves.values())==-1
        r.update(witness_tail=tail,literal_support=support,literal_value=value,literal_every_first_pick=moves)
(HERE/'extension_k6.json').write_text(json.dumps(r,indent=2)+'\n')
