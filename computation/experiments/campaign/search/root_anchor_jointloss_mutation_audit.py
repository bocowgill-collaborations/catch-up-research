"""Preserve the exact stopped mutation prefix, its provenance, and literal witness."""
from pathlib import Path
import collections,hashlib,json,resource,time
P=Path(__file__).resolve().parent;start=time.monotonic();seeds=json.loads((P/'root_anchor_jointloss_mutation_seeds.json').read_text());nodes=seeds['actual_explicit_list'];by={a['id']:a for a in nodes}
def parse(s):
 f=s.split();return {k:(v if k in ['E','label','remaining','moves'] else int(v)) for k,v in zip(f[1::2],f[2::2])}
lines=(P/'root_anchor_jointloss_mutation_probe.log').read_text().splitlines();status=next(s for s in lines if s.startswith('STOP_FIRST_DOUBLELOSS '));cases=[parse(s) for s in lines if s.startswith('CASE ')];assert len(cases)==11149 and [a['id'] for a in cases]==list(range(1,11150))
for a in cases:
 n=by[a['id']];T=tuple(n['T']);E=tuple(map(int,a['E'].rstrip(',').split(',')));assert E==tuple(sorted((4,7)+T)) and a['parent']==n['parent_node_id'] and a['root_source']==n['root_source_diagnostic_id'] and a['depth']==n['depth']
 assert sum(T)%2==0 and len(T)==len(set(T)) and (not T or min(T)>=9)
 if n['depth']:assert (not T or max(T)<=128) and len(T)<=10
 else:assert a['E1']==n['expected_E1'] and a['E3']==n['expected_E3']
 a.update({'T':T,'E':E,'operation':n['operation']})
successful=[a for a in cases if a['E1']==a['E3']==-1];assert len(successful)==1 and successful[0]['id']==11149;w=successful[0];assert w['T']==(18,33,35,36,52,56,62,74,100)
path=[];n=by[w['id']]
while True:
 path.append(n)
 if not n['parent_node_id']:break
 n=by[n['parent_node_id']]
path.reverse();assert [a['depth'] for a in path]==[0,1,2]
literalpath=P/'root_anchor_jointloss_mutation_literal.json';literal=json.loads(literalpath.read_text());assert literal['complete'];L={a['label']:a for a in literal['all_state_records']};assert tuple(L['E1']['remaining'])==w['E'] and L['E1']['value']==L['E3']['value']==-1 and L['C8']['value']==1
remaining=nodes[len(cases):];inputlines=(P/'root_anchor_jointloss_mutation_seeds.txt').read_text().splitlines();(P/'root_anchor_jointloss_mutation_remaining_seeds.txt').write_text('\n'.join(inputlines[len(cases):])+'\n');assert len(remaining)==7592
checkpoint={'planned':18741,'completed':11149,'unprocessed':7592,'resource_limited':False,'stop_reason':'first_literal_verified_doubleLOSS','last_completed_id':11149,'next_unprocessed_id':11150,'not_a_global_minimum':True};(P/'root_anchor_jointloss_mutation_checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
joint=collections.Counter((a['E1'],a['E3']) for a in cases);result={'kind':'ONE stopped deterministic local mutation discriminator; broad auxiliary counterexample, not B/rootC counterexample','fixed_neighborhood':'at most2 specified parity-preserving operations from4short one-sided-loss seeds;7long seeds are controls only','planned_states':18741,'generated_depth_counts':seeds['depth_counts'],'completed_states':11149,'completed_depth_counts':dict(collections.Counter(a['depth'] for a in cases)),'all_completed_cases':cases,'unprocessed_states':7592,'unprocessed_ids':[a['id'] for a in remaining],'checkpoint':checkpoint,'joint_values':[{'E1':k[0],'E3':k[1],'count':v} for k,v in sorted(joint.items())],'double_loss_witness':w,'witness_source_path':path,'independent_literal_witness':{'complete':True,'source':str(literalpath),'source_sha256':hashlib.sha256(literalpath.read_bytes()).hexdigest(),'all_state_records':literal['all_state_records']},'named_R1_control':L['NAMED_R1'],'scope_caveat':'E1andE3LOSS refute the stronger generic two-anchor auxiliary. ActualC8isWIN, so this is not a Banchor/C8LOSS-conditional/Q_N/C counterexample. Remaining7592cases were not queried; no automatic continuation.','seconds':time.monotonic()-start,'max_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss};(P/'root_anchor_jointloss_mutation_results.json').write_text(json.dumps(result,indent=2)+'\n');print('MUTATION_STOPPED_PREFIX_AUDIT_COMPLETE completed11149 unprocessed7592 path',[(a['id'],a['operation'],a['T']) for a in path],'seconds',result['seconds'],'rss',result['max_rss_bytes'],flush=True)
