#!/usr/bin/env python3
"""Existing cutoff7 DAG schema for the fixed G1 counterexample; no Lean edits."""
from pathlib import Path
import copy,hashlib,json,resource,sys,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3]
sys.dont_write_bytecode=True;sys.path.insert(0,str(ROOT));from verify import absolute
start=time.monotonic();nodes=[];roots=[];summary=None
def pairs(line):
    f=line.split();return {k:v for k,v in zip(f[1::2],f[2::2])}
for line in (HERE/'extract.log').read_text().splitlines():
    a=pairs(line)
    if line.startswith('NODE '):
        support=[] if a['remaining']=='empty' else list(map(int,a['remaining'].rstrip(',').split(',')))
        nodes.append(dict(id=int(a['id']),deficit=int(a['deficit']),value=int(a['value']),
                          card=int(a['card']),kind=a['kind'],terminal=bool(int(a['terminal'])),
                          support=support,remaining=support,edges=[]))
    elif line.startswith('EDGE '):
        nodes[int(a['parent'])-1]['edges'].append(dict(parent=int(a['parent']),pick=int(a['pick']),
          child=int(a['child']),child_value=int(a['child_value']),switches=bool(int(a['switches']))))
    elif line.startswith('ROOT '):roots.append(dict(label=a['label'],node=int(a['node']),value=int(a['value'])))
    elif line.startswith('CERTIFICATE_DATA_COMPLETE '):summary=a
assert summary is not None
alias_support=[]
theorem=None
data=dict(cutoff=7,nodes=nodes,roots=roots)
def validate(obj):
    previous={}
    assert [n['id'] for n in obj['nodes']]==list(range(1,len(obj['nodes'])+1))
    for n in obj['nodes']:
        s=n['support'];d=n['deficit']
        assert s==n['remaining']==sorted(set(s)) and all(x>0 for x in s)
        assert len(s)==n['card'] and d>=0 and n['value'] in (-1,1)
        assert n['terminal']==(not s or sum(s)<d)
        if n['kind']=='alias':
            raise AssertionError('No imported alias used in baseline')
        elif n['kind']=='leaf':
            assert not n['edges'] and (len(s)<=7 or n['terminal'])
        else:
            assert len(s)>7 and not n['terminal']
            if n['kind']=='loss':assert n['value']==-1 and [e['pick'] for e in n['edges']]==s
            else:assert n['kind']=='win' and n['value']==1 and len(n['edges'])==1
            for e in n['edges']:
                assert e['parent']==n['id'] and e['child']<n['id']
                c=previous[e['child']];x=e['pick'];assert x in s
                assert c['support']==[y for y in s if y!=x] and c['deficit']==abs(x-d)
                assert e['child_value']==c['value'] and e['switches']==(x>=d)
                assert n['value']==(-c['value'] if x>=d else c['value'])
        previous[n['id']]=n
    assert len(obj['roots'])==1
    r=obj['roots'][0];n=previous[r['node']]
    assert r['value']==n['value']==-1 and n['support']==[2,4,7,13,15,19,35,36,50,57,60,99] and n['deficit']==1
    return previous
by=validate(data);negative=[]
mutations=[
 ('missing_loss_branch',lambda o:o['nodes'][-1]['edges'].pop()),
 ('illegal_winning_move',lambda o:next(n for n in o['nodes'] if n['kind']=='win')['edges'][0].update(pick=999)),
 ('circular_child',lambda o:o['nodes'][-1]['edges'][0].update(child=o['nodes'][-1]['id'])),
 ('wrong_child_state',lambda o:o['nodes'][o['nodes'][-1]['edges'][0]['child']-1].update(deficit=999)),
 ('wrong_root_value',lambda o:o['roots'][0].update(value=1))]
for label,mutate in mutations:
    bad=copy.deepcopy(data);mutate(bad)
    try:validate(bad)
    except (AssertionError,KeyError):negative.append(label)
    else:raise AssertionError('corruption accepted: '+label)
leafcount=0;aliascount=0;maxcache=0
for n in nodes:
    if n['kind']=='alias':
        aliascount+=1;n['lean_alias']=theorem
        n['alias_source']='CatchUp/AlternatingTailObstruction.lean'
        n['alias_source_sha256']=hashlib.sha256((ROOT/n['alias_source']).read_bytes()).hexdigest()
    elif n['kind']=='leaf':
        absolute.cache_clear();v=absolute(tuple(n['support']),0,n['deficit'])
        assert v==n['value'];n.update(literal_leaf_value=v,literal_leaf_pass=True)
        leafcount+=1;maxcache=max(maxcache,absolute.cache_info().currsize)
root=by[roots[0]['node']];s=tuple(root['support']);d=root['deficit'];absolute.cache_clear()
rv=absolute(s,0,d);moves={str(x):(absolute(tuple(y for y in s if y!=x),x,d) if x<d else -absolute(tuple(y for y in s if y!=x),d,x)) for x in s}
assert rv==-1 and all(v==-1 for v in moves.values())
edgecount=sum(len(n['edges']) for n in nodes)
assert len(nodes)==int(summary['nodes']) and leafcount==int(summary['leaves']) and aliascount==int(summary['aliases']) and edgecount==int(summary['edges'])
data.update(scope='Only fixed G1 LOSS; new leaves cutoff7; no imported alias' ,
            node_count=len(nodes),leaf_count=leafcount,alias_count=aliascount,edge_count=edgecount,
            same_player_edges=sum(not e['switches'] for n in nodes for e in n['edges']),
            all_leaf_values_independently_literal=True,all_edges_arithmetic_and_perspective_checked=True,
            literal_root_value=rv,literal_all_root_moves=moves,negative_controls_rejected=negative,
            kernel_certification_claimed=False,max_literal_cached_states=maxcache,
            seconds=time.monotonic()-start,max_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            source_log_sha256=hashlib.sha256((HERE/'extract.log').read_bytes()).hexdigest(),
            literal_source_sha256=hashlib.sha256((ROOT/'verify.py').read_bytes()).hexdigest())
(HERE/'certificate.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({k:data[k] for k in ['node_count','leaf_count','alias_count','edge_count','same_player_edges','seconds','max_rss_bytes','negative_controls_rejected']}),flush=True)
