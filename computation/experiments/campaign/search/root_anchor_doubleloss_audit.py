"""Complete source-list audit and literal first-pick replay of nonvacuous diagnostics."""
from pathlib import Path
import collections, hashlib, json, resource, sys, time
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from verify import absolute
P=Path(__file__).resolve().parent;start=time.monotonic();seeds=json.loads((P/'root_anchor_doubleloss_seeds.json').read_text());seedby={a['id']:a for a in seeds['actual_list']}
def parse(s):
 f=s.split();return {k:(v if k in ['E','remaining','moves','label'] else int(v)) for k,v in zip(f[1::2],f[2::2])}
def labels(s):return tuple(map(int,s.rstrip(',').split(',')))
def move_map(s):return {int(z.split(':')[0]):int(z.split(':')[1]) for z in s.rstrip(',').split(',')}
lines=(P/'root_anchor_doubleloss_probe.log').read_text().splitlines();assert any(s.startswith('COMPLETE_NO_DOUBLELOSS ') for s in lines)
cases=[parse(s) for s in lines if s.startswith('CASE ')];states=[parse(s) for s in lines if s.startswith('STATE ')];assert len(cases)==257
for a in cases:
 q=seedby[a['id']];T=tuple(q['T']);E=tuple(sorted((4,7)+T));assert labels(a['E'])==E and a['source_id']==q['original_seed_id'] and a['saved_C8']==q['saved_C8_value'] and not (a['E1']==a['E3']==-1)
 assert sum(T)%2==0 and min(T)>=9 and len(E)<=12;a.update({'T':T,'E':E,'C8_source':q['C8_source']})
assert [a['id'] for a in cases]==list(range(1,258))
selected=[a for a in cases if a['E1']==-1 or a['E3']==-1];assert len(selected)==11
literal_queries=literal_picks=max_cache=0
def check_state(S,d,expected,expected_moves=None):
 global literal_queries,literal_picks,max_cache
 if time.monotonic()-start>22:raise TimeoutError('INCOMPLETE22s diagnostic replay cap')
 S=tuple(S);value=absolute(S,0,d);assert value==expected;literal_queries+=1
 moves={x:(absolute(tuple(y for y in S if y!=x),x,d) if x<d else -absolute(tuple(y for y in S if y!=x),d,x)) for x in S}
 assert max(moves.values())==value
 if expected_moves is not None:assert moves==expected_moves
 literal_picks+=len(moves);max_cache=max(max_cache,absolute.cache_info().currsize);absolute.cache_clear();return {'remaining':S,'deficit':d,'value':value,'all_first_pick_values':moves,'literal_replay_pass':True}
for a in selected:
 a['literal_E1']=check_state(a['E'],1,a['E1']);a['literal_E3']=check_state(a['E'],3,a['E3']);print('LITERAL_NONVACUOUS_DIAGNOSTIC_PASS',a['id'],'E1',a['E1'],'E3',a['E3'],flush=True)
control=cases[0];assert control['is_control']==1 and tuple(control['T'])==(9,10,12,15) and control['E1']==-1 and control['E3']==1
contexts=[]
for s in states:
 assert s['id']==1;S=labels(s['remaining']);expected=move_map(s['moves']);entry=check_state(S,s['deficit'],s['value'],expected);entry['label']=s['label'];contexts.append(entry)
assert {a['label']:a['value'] for a in contexts}=={'C8':1,'C2':1,'Cerase2_4':0}
control['literal_contexts']=contexts
unprocessed=[];(P/'root_anchor_doubleloss_remaining_seeds.txt').write_text('')
checkpoint={'planned':257,'completed':257,'named_prior_controls':1,'saved_B_tails':256,'unprocessed_ids':unprocessed,'stop_reason':'all_complete_no_doubleloss','resource_limited':False};(P/'root_anchor_doubleloss_checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
joint=collections.Counter((a['E1'],a['E3']) for a in cases)
result={'kind':'ONE bounded two-anchor auxiliary discriminator; complete saved256 B tails plus explicitly authorized named prior control','planned':257,'completed':257,'saved_B_tail_cases':256,'extra_named_control_cases':1,'named_control_already_in_saved256':False,'named_control_already_in_original_exhaustive_B_domain':True,'all_cases':cases,'double_loss_found':False,'E1_loss_count':sum(a['E1']==-1 for a in cases),'E3_loss_count':sum(a['E3']==-1 for a in cases),'joint_values':[{'E1':k[0],'E3':k[1],'count':v} for k,v in sorted(joint.items())],'all_saved_C8_nonloss':all(a['saved_C8']>=0 for a in cases),'named_control_contexts':contexts,'literal_scope':{'all_11_cases_with_either_loss_replayed':True,'direct_queries':literal_queries,'all_first_picks_replayed':literal_picks,'all_257_pairs_literally_replayed':False,'max_cached_states':max_cache,'source_sha256':hashlib.sha256((P.parents[1]/'verify.py').read_bytes()).hexdigest()},'source_seed_receipt_sha256':hashlib.sha256((P/'root_anchor_doubleloss_seeds.json').read_bytes()).hexdigest(),'checkpoint':checkpoint,'seconds':time.monotonic()-start,'max_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'scope_caveat':'No uniform two-anchor auxiliary theorem follows. NamedE1LOSS is a counterexample to unconditionalE1nonloss, while itsE3 andC8 areWIN; it is not a Banchor/Q_N/C counterexample. No further tail batch was started.'}
(P/'root_anchor_doubleloss_results.json').write_text(json.dumps(result,indent=2)+'\n');print('DOUBLELOSS_AUDIT_COMPLETE joint',result['joint_values'],'literal_queries',literal_queries,'first_picks',literal_picks,'seconds',result['seconds'],'rss',result['max_rss_bytes'],flush=True)
