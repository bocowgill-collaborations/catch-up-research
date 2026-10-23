"""Audit the fixed-support shrink, reuse its identical literal witness, check proof data."""
from pathlib import Path
import collections,hashlib,json,resource,sys,time
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from verify import absolute
P=Path(__file__).resolve().parent;start=time.monotonic();T=(18,33,35,36,52,56,62,74,100)
def parse(s):
 f=s.split();return {k:(v if k in ['E','label','remaining','moves','kind'] else int(v)) for k,v in zip(f[1::2],f[2::2])}
def labels(s):return () if s=='empty' else tuple(map(int,s.rstrip(',').split(',')))
def moves(s):return {int(z.split(':')[0]):int(z.split(':')[1]) for z in s.rstrip(',').split(',')}
lines=(P/'root_anchor_jointloss_shrink_probe.log').read_text().splitlines();assert any(s.startswith('COMPLETE_FIXED_SUPPORT_SHRINK ') for s in lines)
cases=[parse(s) for s in lines if s.startswith('CASE ')];odd=[parse(s) for s in lines if s.startswith('ODD_SKIPPED ')];states=[parse(s) for s in lines if s.startswith('STATE ')]
assert len(cases)==len(odd)==256 and {a['mask'] for a in cases+odd}==set(range(512))
for a in cases+odd:
 tail=tuple(x for i,x in enumerate(T) if a['mask']&(1<<i));assert sum(tail)==a['tail_sum'];a['T']=tail
 if 'E1' in a:assert sum(tail)%2==0 and labels(a['E'])==tuple(sorted((4,7)+tail))
 else:assert sum(tail)%2==1
witnesses=[a for a in cases if a['E1']==a['E3']==-1];assert len(witnesses)==1
best=min(witnesses,key=lambda a:(len(a['T']),max(a['T'],default=0),sum(a['T']),a['T']));assert best['T']==T and best['mask']==511
literalpath=P/'root_anchor_jointloss_mutation_literal.json';literal=json.loads(literalpath.read_text());assert literal['complete'];literalby={a['label']:a for a in literal['all_state_records']}
for a in states:
 q=literalby[a['label']];assert labels(a['remaining'])==tuple(q['remaining']) and a['deficit']==q['deficit'] and a['value']==q['value'] and moves(a['moves'])=={int(k):v for k,v in q['all_first_pick_values'].items()}

dump=(P/'root_anchor_jointloss_shrink_certificate_dump.log').read_text().splitlines();nodes=[parse(s) for s in dump if s.startswith('NODE ')];edges=[parse(s) for s in dump if s.startswith('EDGE ')];roots=[parse(s) for s in dump if s.startswith('ROOT ')];assert len(nodes)==145 and len(edges)==152
by={a['id']:a for a in nodes};leaf_cache_counts=[]
for a in nodes:
 S=labels(a['remaining']);a['remaining']=S;assert len(S)==a['card'] and a['terminal']==int(not S or sum(S)<a['deficit']);out=[e for e in edges if e['parent']==a['id']];a['edges']=out
 for e in out:
  child=by[e['child']];C=labels(child['remaining']) if isinstance(child['remaining'],str) else child['remaining'];x=e['pick'];assert e['child']<a['id'] and x in S and C==tuple(y for y in S if y!=x) and child['deficit']==abs(x-a['deficit']) and child['value']==e['child_value'] and e['switches']==int(x>=a['deficit'])
  assert (-child['value'] if e['switches'] else child['value'])==a['value']
 if a['kind']=='leaf':
  assert a['card']<=8 and not out;value=absolute(S,0,a['deficit']);assert value==a['value'];count=absolute.cache_info().currsize;a['independent_literal_leaf_pass']=True;a['literal_cached_states']=count;leaf_cache_counts.append((count,a['id']));absolute.cache_clear()
 elif a['kind']=='win':assert a['value']==1 and len(out)==1
 else:assert a['kind']=='loss' and a['value']==-1 and {e['pick'] for e in out}==set(S)
for r in roots:assert by[r['node']]['value']==r['value']
hardest=by[max(leaf_cache_counts)[1]];cert={'kind':'Certificate DATA only; kernel proof is a separate gate','cutoff':8,'roots':roots,'nodes':nodes,'unique_nodes':145,'leaves':86,'edges':152,'edge_fidelity_audit_pass':True,'all_86_leaves_independent_literal_pass':True,'hardest_literal_leaf':hardest,'source_sha256':hashlib.sha256((P/'root_anchor_jointloss_shrink_certificate.cpp').read_bytes()).hexdigest()};(P/'root_anchor_jointloss_shrink_certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
result={'kind':'Complete deletion shrink inside ONE fixed nine-counter support; no global minimum claim','fixed_original_T':T,'all_512_subsets_accounted':True,'all_256_even_subset_queries':cases,'all_256_odd_skipped':odd,'all_successful_doubleloss_subsets':witnesses,'minimum_within_fixed_support':best,'objective':'tailcard,maxlabel,tailsum,lexT','unique_doubleloss_subset_is_full_support':True,'minimal_witness_independent_literal':{'reused_complete_identical_witness':True,'source':str(literalpath),'source_sha256':hashlib.sha256(literalpath.read_bytes()).hexdigest(),'five_state_records':[literalby[a['label']] for a in states]},'certificate_data':{'file':str(P/'root_anchor_jointloss_shrink_certificate.json'),'nodes':145,'leaves':86,'edges':152,'all_leaves_at_most8':True,'all_86_leaves_independent_literal_pass':True,'hardest_leaf':hardest},'seconds':time.monotonic()-start,'max_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss};(P/'root_anchor_jointloss_shrink_results.json').write_text(json.dumps(result,indent=2)+'\n')
print('SHRINK_CERTIFICATE_AUDIT_COMPLETE','unique_witness_mask',best['mask'],'nodes',len(nodes),'leaves',len(leaf_cache_counts),'hardest_leaf',hardest['id'],hardest['remaining'],hardest['deficit'],hardest['value'],'cache_states',hardest['literal_cached_states'],'seconds',result['seconds'],'rss',result['max_rss_bytes'],flush=True)
