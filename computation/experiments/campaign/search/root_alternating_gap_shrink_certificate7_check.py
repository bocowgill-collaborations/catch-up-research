"""Parse SAME-root data; audit every edge and literally evaluate all leaves."""
from pathlib import Path
import hashlib,json,resource,sys,time
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from verify import absolute
P=Path(__file__).resolve().parent;start=time.monotonic();nodes=[];roots=[];summary=None
def pairs(line):
 f=line.split();return {k:v for k,v in zip(f[1::2],f[2::2])}
for line in (P/'root_alternating_gap_shrink_certificate7.log').read_text().splitlines():
 if line.startswith('NODE '):
  a=pairs(line);S=[] if a['remaining']=='empty' else list(map(int,a['remaining'].rstrip(',').split(',')))
  nodes.append({'id':int(a['id']),'deficit':int(a['deficit']),'value':int(a['value']),'card':int(a['card']),'kind':a['kind'],'terminal':bool(int(a['terminal'])),'support':S,'edges':[]})
 elif line.startswith('EDGE '):
  a=pairs(line);nodes[int(a['parent'])-1]['edges'].append({'pick':int(a['pick']),'child':int(a['child']),'child_value':int(a['child_value']),'switches':bool(int(a['switches']))})
 elif line.startswith('ROOT '):
  a=pairs(line);roots.append({'label':a['label'],'node':int(a['node']),'value':int(a['value'])})
 elif line.startswith('CERTIFICATE_DATA_COMPLETE '):summary=pairs(line)
assert summary is not None
assert [n['id'] for n in nodes]==list(range(1,len(nodes)+1))
assert len(nodes)==int(summary['nodes'])==19 and len(roots)==1
leafcount=0;edgecount=0;maxcache=0
for n in nodes:
 S=n['support'];d=n['deficit'];assert S==sorted(set(S)) and len(S)==n['card']
 assert n['terminal']==(not S or sum(S)<d)
 if n['kind']=='leaf':
  assert not n['edges'] and (len(S)<=7 or n['terminal'])
  absolute.cache_clear();v=absolute(tuple(S),0,d);maxcache=max(maxcache,absolute.cache_info().currsize);assert v==n['value']
  n.update({'literal_leaf_value':v,'literal_leaf_pass':True});leafcount+=1;absolute.cache_clear()
  print('LITERAL_LEAF_PASS',n['id'],'value',v,'deficit',d,'support',S,flush=True)
 else:
  assert len(S)>7 and n['edges']
  if n['value']==-1:assert n['kind']=='loss' and sorted(e['pick'] for e in n['edges'])==S
  else:assert n['kind']=='win' and n['value']==1 and len(n['edges'])==1
  for e in n['edges']:
   assert e['child']<n['id'] and e['pick'] in S
   child=nodes[e['child']-1];x=e['pick']
   assert child['support']==[z for z in S if z!=x] and child['deficit']==abs(x-d)
   assert e['child_value']==child['value'] and e['switches']==(x>=d)
   mv=-child['value'] if e['switches'] else child['value']
   assert mv==n['value'];e['move_value']=mv;e['edge_arithmetic_and_perspective_pass']=True;edgecount+=1
assert leafcount==int(summary['leaves'])==9 and edgecount==int(summary['edges'])==18
root=roots[0];rn=nodes[root['node']-1]
result=json.loads((P/'root_alternating_gap_shrink_results.json').read_text());final=next(a for a in result['final_contexts'] if a['kind']=='final_E1')
assert root['label']=='E1' and root['value']==rn['value']==-1 and rn['support']==final['support'] and rn['deficit']==final['deficit']==1 and final['literal_all_picks_pass']
out={'scope':'Only finalized E1 root; no support search or certificate for optional contexts','cutoff':7,'nodes':nodes,'roots':roots,'node_count':len(nodes),'leaf_count':leafcount,'edge_count':edgecount,'all_leaf_values_independently_literal':True,'all_edges_arithmetic_and_perspective_checked':True,'same_player_edges':sum(not e['switches'] for n in nodes for e in n['edges']),'source_log_sha256':hashlib.sha256((P/'root_alternating_gap_shrink_certificate7.log').read_bytes()).hexdigest(),'literal_source_sha256':hashlib.sha256((P.parents[1]/'verify.py').read_bytes()).hexdigest(),'kernel_certification_claimed':False,'max_literal_cached_states':maxcache,'seconds':time.monotonic()-start,'max_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
(P/'root_alternating_gap_shrink_certificate7.json').write_text(json.dumps(out,indent=2)+'\n')
print('COMPLETE_CERTIFICATE_AUDIT',len(nodes),'nodes',leafcount,'literal_leaves',edgecount,'edges','seconds',out['seconds'],'rss',out['max_rss_bytes'],flush=True)
