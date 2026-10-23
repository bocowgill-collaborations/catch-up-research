"""Independent literal-score verification of the stopped mutation witness and named control."""
from pathlib import Path
import hashlib,json,resource,sys,time
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from verify import absolute
P=Path(__file__).resolve().parent;start=time.monotonic()
def parse(s):
 f=s.split();return {k:(v if k in ['label','remaining','moves'] else int(v)) for k,v in zip(f[1::2],f[2::2])}
def labels(s):return tuple(map(int,s.rstrip(',').split(',')))
def moves(s):return {int(z.split(':')[0]):int(z.split(':')[1]) for z in s.rstrip(',').split(',')}
states=[parse(s) for s in (P/'root_anchor_jointloss_mutation_probe.log').read_text().splitlines() if s.startswith('STATE ')];assert len(states)==6
records=[];maxcache=0;picks=0
def save(complete):
 r={'kind':'Independent literal-score replay of mutation witness; separate<=30s check','complete':complete,'all_state_records':records,'queries_completed':len(records),'first_picks_completed':picks,'max_cached_states':maxcache,'seconds':time.monotonic()-start,'max_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'literal_source_sha256':hashlib.sha256((P.parents[1]/'verify.py').read_bytes()).hexdigest()};(P/'root_anchor_jointloss_mutation_literal.json').write_text(json.dumps(r,indent=2)+'\n');return r
for a in states:
 if time.monotonic()-start>26:save(False);raise TimeoutError('INCOMPLETE26s literal guard')
 S=labels(a['remaining']);d=a['deficit'];expected=moves(a['moves']);actual=absolute(S,0,d);assert actual==a['value'];actual_moves={}
 for x in S:
  after=tuple(y for y in S if y!=x);actual_moves[x]=absolute(after,x,d) if x<d else -absolute(after,d,x)
 assert actual_moves==expected and max(actual_moves.values())==actual
 picks+=len(actual_moves);maxcache=max(maxcache,absolute.cache_info().currsize);records.append({'id':a['id'],'label':a['label'],'remaining':S,'deficit':d,'value':actual,'all_first_pick_values':actual_moves,'literal_replay_pass':True});absolute.cache_clear();save(False);print('LITERAL_WITNESS_STATE_PASS',a['label'],'value',actual,'picks',len(actual_moves),flush=True)
by={r['label']:r for r in records};assert by['E1']['value']==by['E3']['value']==-1 and by['C8']['value']==1 and by['C2']['value']==1 and by['Cerase2_4']['value']==-1 and by['NAMED_R1']['value']==0
r=save(True);print('MUTATION_WITNESS_LITERAL_COMPLETE','queries',len(records),'first_picks',picks,'seconds',r['seconds'],'rss',r['max_rss_bytes'],flush=True)
