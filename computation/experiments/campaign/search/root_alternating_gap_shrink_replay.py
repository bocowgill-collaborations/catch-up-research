"""Independent literal replay and complete accounting of fixed witness shrink."""
from pathlib import Path
import collections, hashlib, json, resource, sys, time
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from verify import absolute
P=Path(__file__).resolve().parent;start=time.monotonic()
seed=json.loads((P/'root_alternating_gap_shrink_seeds.json').read_text())
rows=[json.loads(z) for z in (P/'root_alternating_gap_shrink_probe.log').read_text().splitlines()]
deletions=[a for a in rows if a['kind']=='deletion'];trials=[a for a in rows if a['kind']=='numeric_trial']
checkpoint=next(a for a in rows if a['kind']=='checkpoint')
selected=next(a for a in rows if a['kind']=='selected_deletion_loss')
frozen=next(a for a in rows if a['kind']=='frozen_best')
final=[a for a in rows if a['kind'].startswith('final_')]
by={a['mask']:a for a in deletions}
assert len(deletions)==16 and list(by)==seed['ordered_admissible_masks']
assert len(by)==len(set(by)) and checkpoint['phase1_unprocessed']==0
for a in seed['records']:
 if a['admissible']:
  q=by[a['deletion_mask']];assert a['T']==q['T'];a['query_status']='queried';a['native_value']=q['value']
 else:assert a['query_status']=='predicate_skip'
losses=[a for a in deletions if a['value']==-1]
key=lambda a:(len(a['T']),max(a['T']),sum(a['T']),a['T'])
assert selected['T']==min(losses,key=key)['T']
best=selected['T']
for a in trials:
 assert a['before']==best
 C=best.copy();C[a['coordinate_zero_based']]-=2;assert C==a['candidate']
 valid=bool(C) and C[0]>=9 and C==sorted(set(C)) and all(x%2==(1 if i%2==0 else 0) for i,x in enumerate(C)) and sum(C)%2==0
 assert valid==a['admissible']==a['queried']
 assert a['accepted']==(valid and a['value']==-1)
 if a['accepted']:best=C
 assert best==a['current_best']
assert best==frozen['T']
if checkpoint['one_step_fixed_point']:
 last=[a for a in trials if a['sweep']==checkpoint['sweeps']]
 assert len(last)==len(best) and all(not a['accepted'] and a['before']==best for a in last)
assert len([a for a in trials if a['queried']])==checkpoint['phase2_queries']
assert sum(a['accepted'] for a in trials)==checkpoint['accepted_numeric_trials']
complete=False;roots=0;picks=0;maxcache=0
def save():
 r={'scope':'Fixed T0 deletion and deterministic coordinate -2 compression only; no global minimum claim','source_T0':seed['T0'],'deletion_records':seed['records'],'deletion_outcome_counts':dict(collections.Counter(a['value'] for a in deletions)),'selected_deletion_loss':selected,'all_numeric_trials':trials,'frozen_best':frozen,'native_checkpoint':checkpoint,'final_contexts':final,'literal_complete':complete,'literal_roots':roots,'literal_first_pick_values':picks,'max_literal_cached_states':maxcache,'literal_source_sha256':hashlib.sha256((P.parents[1]/'verify.py').read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'max_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
 (P/'root_alternating_gap_shrink_results.json').write_text(json.dumps(r,indent=2)+'\n');return r
for a in final:
 if time.monotonic()-start>25:save();print('LITERAL_CAP_PARTIAL',roots,picks,flush=True);raise SystemExit(3)
 S=tuple(a['support']);d=a['deficit'];absolute.cache_clear();v=absolute(S,0,d);assert v==a['value'];maxcache=max(maxcache,absolute.cache_info().currsize)
 move={}
 for x in S:
  C=tuple(z for z in S if z!=x);move[str(x)]=absolute(C,x,d) if x<d else -absolute(C,d,x);maxcache=max(maxcache,absolute.cache_info().currsize)
 assert move==a['moves'] and max(move.values())==v
 a.update({'literal_root_value':v,'literal_first_pick_values':move,'literal_all_picks_pass':True,'safe_choices':[int(x) for x,z in move.items() if z>=0]});roots+=1;picks+=len(S);absolute.cache_clear();save();print('LITERAL_PASS',a['kind'],'value',v,'moves',json.dumps(move),'safe',a['safe_choices'],flush=True)
complete=True;r=save();print('COMPLETE_LITERAL',roots,picks,'seconds',r['seconds'],'rss',r['max_rss_bytes'],flush=True)
