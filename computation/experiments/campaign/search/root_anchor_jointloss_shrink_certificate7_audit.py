"""Audit cutoff-seven data separately, leaving the cutoff-eight export unchanged."""
from pathlib import Path
import hashlib,json,resource,sys,time
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from verify import absolute
P=Path(__file__).resolve().parent;start=time.monotonic()
def parse(s):
 f=s.split();return {k:(v if k in ['label','remaining','kind'] else int(v)) for k,v in zip(f[1::2],f[2::2])}
def labels(s):return () if s=='empty' else tuple(map(int,s.rstrip(',').split(',')))
lines=(P/'root_anchor_jointloss_shrink_certificate7_dump.log').read_text().splitlines();nodes=[parse(s) for s in lines if s.startswith('NODE ')];edges=[parse(s) for s in lines if s.startswith('EDGE ')];roots=[parse(s) for s in lines if s.startswith('ROOT ')];assert len(nodes)==290 and len(edges)==308
by={a['id']:a for a in nodes};leaves=[]
for a in nodes:
 S=labels(a['remaining']);a['remaining']=S;assert len(S)==a['card'] and a['terminal']==int(not S or sum(S)<a['deficit']);a['edges']=[e for e in edges if e['parent']==a['id']]
 for e in a['edges']:
  c=by[e['child']];R=labels(c['remaining']) if isinstance(c['remaining'],str) else c['remaining'];x=e['pick'];assert e['child']<a['id'] and R==tuple(y for y in S if y!=x) and c['deficit']==abs(x-a['deficit']) and c['value']==e['child_value'] and e['switches']==int(x>=a['deficit']);assert (-c['value'] if e['switches'] else c['value'])==a['value']
 if a['kind']=='leaf':
  assert a['card']<=7 and not a['edges'] and absolute(S,0,a['deficit'])==a['value'];a['literal_cached_states']=absolute.cache_info().currsize;a['independent_literal_leaf_pass']=True;absolute.cache_clear();leaves.append(a)
 elif a['kind']=='win':assert a['value']==1 and len(a['edges'])==1
 else:assert a['kind']=='loss' and a['value']==-1 and {e['pick'] for e in a['edges']}==set(S)
assert len(leaves)==145
for r in roots:assert by[r['node']]['value']==r['value']
hard=max(leaves,key=lambda a:a['literal_cached_states']);result={'kind':'Certificate DATA only, separate kernel proof gate; fixed witness and same E1/E3/C8 roots','cutoff':7,'roots':roots,'nodes':nodes,'unique_nodes':290,'leaves':145,'edges':308,'edge_fidelity_audit_pass':True,'all_145_leaves_independent_literal_pass':True,'hardest_literal_leaf':hard,'source_sha256':hashlib.sha256((P/'root_anchor_jointloss_shrink_certificate7.cpp').read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'max_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss};(P/'root_anchor_jointloss_shrink_certificate7.json').write_text(json.dumps(result,indent=2)+'\n');print('CUTOFF7_DATA_AUDIT_COMPLETE nodes290 leaves145 edges308 hardest',hard['id'],hard['remaining'],hard['deficit'],hard['value'],'cached',hard['literal_cached_states'],'seconds',result['seconds'],'rss',result['max_rss_bytes'],flush=True)
