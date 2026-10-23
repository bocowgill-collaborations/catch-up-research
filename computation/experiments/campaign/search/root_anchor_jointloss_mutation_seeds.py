"""Fixed radius-two, parity-preserving mutations of the eleven saved one-sided losses."""
from pathlib import Path
import collections, hashlib, json, time
P=Path(__file__).resolve().parent;start=time.monotonic();source=P/'root_anchor_doubleloss_results.json';old=json.loads(source.read_text());base=[a for a in old['all_cases'] if a['E1']==-1 or a['E3']==-1];assert len(base)==11
nodes=[];seen={}
def add(T,parent,root,depth,operation,control=None):
 T=tuple(sorted(T))
 if T in seen:return None
 assert len(T)==len(set(T)) and sum(T)%2==0 and len(T)<=12 and (not T or min(T)>=9)
 if depth:assert not T or max(T)<=128
 a={'id':len(nodes)+1,'T':T,'parent_node_id':parent,'root_source_diagnostic_id':root,'depth':depth,'operation':operation,'is_control':depth==0,'expected_E1':control['E1'] if control else None,'expected_E3':control['E3'] if control else None}
 nodes.append(a);seen[T]=a['id'];return a
for a in base:add(a['T'],0,a['id'],0,'saved_one_sided_loss_control',a)
active=[a for a in nodes if not a['T'] or max(a['T'])<=128]
def neighbors(T):
 def valid(V):return len(V)==len(set(V)) and len(V)<=12 and (not V or 9<=min(V)<=max(V)<=128) and sum(V)%2==0
 for i,x in enumerate(T):
  for delta in [-2,2]:
   V=T[:i]+(x+delta,)+T[i+1:]
   if valid(V):yield tuple(sorted(V)),f'counter_{x}_plus_{delta}'
 for i in range(len(T)):
  for j in range(i+1,len(T)):
   for di,dj in [(-1,-1),(-1,1),(1,-1),(1,1)]:
    V=list(T);V[i]+=di;V[j]+=dj
    if valid(V):yield tuple(sorted(V)),f'two_counters_{T[i]}_{di}_{T[j]}_{dj}'
 for i,x in enumerate(T):
  if x%2==0:yield T[:i]+T[i+1:],f'delete_even_{x}'
 if len(T)<12:
  for x in range(10,129,2):
   if x not in T:yield tuple(sorted(T+(x,))),f'add_even_{x}'
for a in active:
 for T,op in neighbors(tuple(a['T'])):add(T,a['id'],a['root_source_diagnostic_id'],1,op)
levelone=[a for a in nodes if a['depth']==1]
for a in levelone:
 for T,op in neighbors(tuple(a['T'])):add(T,a['id'],a['root_source_diagnostic_id'],2,op)
for a in nodes:
 if a['depth']:
  parent=nodes[a['parent_node_id']-1];assert a['depth']==parent['depth']+1 and parent['root_source_diagnostic_id']==a['root_source_diagnostic_id']
receipt={'purpose':'ONE fixed local radius-two discriminator for simultaneous LOSS of E={4,7}unionT at1and3','source_results_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'seed_controls':11,'short_seed_controls_mutated':len(active),'long_seed_controls_only':11-len(active),'deduplication':'identical actual T only; no symmetry/translation compression','planned_states':len(nodes),'depth_counts':dict(collections.Counter(a['depth'] for a in nodes)),'mutation_counter_limit':128,'tail_limit':12,'actual_max_mutated_tail_cardinality':max(len(a['T']) for a in nodes if a['depth']),'actual_explicit_list':nodes,'seconds':time.monotonic()-start}
(P/'root_anchor_jointloss_mutation_seeds.json').write_text(json.dumps(receipt,indent=2)+'\n');(P/'root_anchor_jointloss_mutation_seeds.txt').write_text(''.join(' '.join(map(str,[a['id'],a['parent_node_id'],a['root_source_diagnostic_id'],a['depth'],int(a['is_control']),a['expected_E1'] if a['is_control'] else 2,a['expected_E3'] if a['is_control'] else 2,len(a['T']),*a['T']]))+'\n' for a in nodes))
print('FIXED_MUTATION_LIST_COMPLETE',receipt['planned_states'],'depths',receipt['depth_counts'],'active',len(active),'long_controls',11-len(active),'max_new_tail',receipt['actual_max_mutated_tail_cardinality'],'seconds',receipt['seconds'],flush=True)
