"""Complete-list audit and fixed literal controls from the same saved unpaired batch."""
from pathlib import Path
import collections, hashlib, json, resource, sys, time
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from verify import absolute
P=Path(__file__).resolve().parent;start=time.monotonic();seeds=json.loads((P/'root_anchor_unpaired_seeds.json').read_text());seedby={a['id']:a for a in seeds['actual_explicit_list']}
def parse(s):
 f=s.split();return {k:(v if k in ['family','U','remaining','moves','label'] else int(v)) for k,v in zip(f[1::2],f[2::2])}
def paired(T):return len(T)%2==0 and all(T[i+1]==T[i]+1 for i in range(0,len(T),2))
lines=(P/'root_anchor_unpaired_probe.log').read_text().splitlines();cases=[parse(s) for s in lines if s.startswith('CASE ')];losses=[parse(s) for s in lines if s.startswith('ANCHOR_LOSS ')];status=[s for s in lines if s.startswith(('STOP_ANCHOR_LOSS ','STOP_PROBE_8S_CAP ','COMPLETE_PLANNED_BATCH '))];assert len(status)==1
assert status[0].startswith('COMPLETE_PLANNED_BATCH ') and len(cases)==512 and not losses
assert {a['id'] for a in cases}==set(range(1,513))
for a in cases:
 seed=seedby[a['id']];T=tuple(seed['T']);anchor=(2,3,4) if a['family']=='A' else (2,3,4,7);U=tuple(sorted(anchor+T));assert a['family']==seed['family'] and tuple(map(int,a['U'].rstrip(',').split(',')))==U and len(U)==a['support_size']<=14
 assert len(T)==len(set(T)) and min(T)>=(8 if a['family']=='A' else 9) and max(T)<=1000 and sum(T)%2==0 and not paired(T) and (sum(U)+a['shadow_def'])%2==0
 assert a['shadow_value']>=0;a.update({'T':T,'U':U,'tail_kind':seed['kind'],'provenance':seed['provenance'],'tail_cardinality':len(T)})
remaining=[];(P/'root_anchor_unpaired_remaining_seeds.txt').write_text('')
checkpoint={'planned':512,'completed':512,'all_completed_ids':[a['id'] for a in cases],'unprocessed_ids':remaining,'next_start_id':None,'stop_reason':'complete_planned_batch_no_loss','resource_limited':False,'resume_cli_template':'root_anchor_unpaired_probe root_anchor_unpaired_seeds.txt FIRST_ID; no automatic resume is authorized'}
(P/'root_anchor_unpaired_checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')

# These controls were fixed by the prior-geometry tags, not selected by outcomes.
controls=[a for a in cases if a['tail_kind']=='prior_six_root_loss_embedded' or (a['tail_kind']=='prior_shifted_cycle_root_loss_embedded' and tuple(a['T'])==(9,16,17,18,26,28,31,37))]
assert len(controls)==4
literal_queries=0;max_cache=0;source_controls=[]
def query(S,d,first=False):
 global literal_queries,max_cache
 if time.monotonic()-start>20:raise TimeoutError('literal-control20s budget')
 value=absolute(tuple(S),0,d,first);literal_queries+=1;max_cache=max(max_cache,absolute.cache_info().currsize);return value
for name,S in [('reported_complete_even_root',(1,2,3,7,14,23,37,68,101,111,123)),('reported_six_even_root',(2,5,6,9,11,13)),('reported_shifted_cycle_even_root',(9,16,17,18,26,28,31,37))]:
 value=query(S,0,True);moves={x:-absolute(tuple(y for y in S if y!=x),0,x) for x in S};assert value==max(moves.values())
 source_controls.append({'name':name,'remaining':S,'deficit':0,'root_value':value,'all_opening_values':moves,'reported_root_loss_matches_literal':value==-1});absolute.cache_clear();print('SOURCE_GEOMETRY_LITERAL_CONTROL',name,'root',value,flush=True)
for a in controls:
 U=a['U'];d=a['shadow_def'];value=query(U,d);assert value==a['shadow_value'];moves={x:(absolute(tuple(y for y in U if y!=x),x,d) if x<d else -absolute(tuple(y for y in U if y!=x),d,x)) for x in U};assert max(moves.values())==value
 a['literal_shadow_control_pass']=True;a['literal_shadow_moves']=moves;records=[{'remaining':U,'deficit':d,'value':value}];absolute.cache_clear()
 td=3 if a['family']=='A' else 2;records.append({'remaining':U,'deficit':td,'value':query(U,td)});absolute.cache_clear()
 if a['family']=='B':
  E=tuple(x for x in U if x!=2);records.append({'remaining':E,'deficit':4,'value':query(E,4)});absolute.cache_clear()
 a['literal_control_queries']=records;print('EMBEDDED_ANCHOR_LITERAL_CONTROL',a['id'],a['family'],'shadow',value,flush=True)
summaries=[]
for family in ['A','B']:
 q=[a for a in cases if a['family']==family];summaries.append({'family':family,'planned':256,'completed':len(q),'loss':sum(a['shadow_value']==-1 for a in q),'draw':sum(a['shadow_value']==0 for a in q),'win':sum(a['shadow_value']==1 for a in q),'tail_cardinality_counts':dict(collections.Counter(a['tail_cardinality'] for a in q)),'tail_kind_counts':dict(collections.Counter(a['tail_kind'] for a in q))})
result={'kind':'ONE deterministic unpaired arbitrary-even-tail anchor discriminator; complete finite evidence only','frontier_note_sha256_at_seed_creation':seeds['frontier_note_sha256'],'planned_cases':512,'completed_cases':512,'skipped_cases':0,'unprocessed_cases':0,'resource_limited':False,'anchor_loss_found':False,'all_completed_cases':cases,'family_summaries':summaries,'conditional_reflection_nonvacuous_cases':0,'primary_conditional_targets_queried':0,'literal_scope':{'all_512_primary_values_replayed':False,'four_predetermined_embedded_anchor_controls':True,'source_geometry_root_controls':source_controls,'total_direct_literal_queries':literal_queries,'max_cached_states':max_cache,'source_sha256':hashlib.sha256((P.parents[1]/'verify.py').read_bytes()).hexdigest()},'checkpoint':checkpoint,'seconds':time.monotonic()-start,'max_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'scope_caveat':'No uniform anchor or reflection theorem, and no actual interval-rootQ_N/C conclusion, follows. No additional tail batch was started.'}
(P/'root_anchor_unpaired_results.json').write_text(json.dumps(result,indent=2)+'\n');print('UNPAIRED_AUDIT_COMPLETE',json.dumps(summaries,sort_keys=True),'literal_queries',literal_queries,'seconds',result['seconds'],'rss',result['max_rss_bytes'],flush=True)
