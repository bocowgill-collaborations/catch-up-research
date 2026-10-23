"""One predetermined unpaired-tail discriminator; saved explicit list is authoritative."""
from pathlib import Path
import collections, hashlib, json, random, time
P=Path(__file__).resolve().parent;start=time.monotonic()
complete=(1,2,3,7,14,23,37,68,101,111,123)
six=(2,5,6,9,11,13);cycle=(9,16,17,18,26,28,31,37)
hand=[(8,),(10,),(1000,),(8,1000),(9,999),(9,11,20),(8,19,21),(37,41,1000),(8,19,21,40,1000),(9,11,28,40,101,303,1000),(8,20,50,130,340,900),(10,12,16,32,128,512,998),(8,9,10,11,30),(9,10,11,12,14),(8,9,10,11,12,14),(19,20,21,22,24,101,303)]
def paired(T):return len(T)%2==0 and all(T[i+1]==T[i]+1 for i in range(0,len(T),2))
def even_adjust(T,lo):
 T=tuple(sorted(set(T)))
 if sum(T)%2==0:return T
 for i in range(len(T)-1,-1,-1):
  for delta in [-1,1,-3,3]:
   y=T[i]+delta
   if lo<=y<=1000 and y not in T:return tuple(sorted(T[:i]+(y,)+T[i+1:]))
 raise RuntimeError('parity correction unavailable')
rows=[]
for family,lo,maxr in [('A',8,11),('B',9,10)]:
 items={};rng=random.Random(20261022+(family=='B'))
 def add(T,kind,provenance=None):
  T=tuple(sorted(T))
  assert len(set(T))==len(T) and 1<=len(T)<=maxr and lo<=min(T)<=max(T)<=1000 and sum(T)%2==0 and not paired(T)
  items.setdefault(T,{'family':family,'T':T,'kind':kind,'provenance':provenance})
 for T in hand:
  if family=='B' and min(T)<9:
   y=10
   while y in T:y+=2
   T=tuple(y if x==8 else x for x in T)
  add(T,'explicit_cluster_or_scattered')
 add(tuple(x+(6 if family=='A' else 8) for x in six),'prior_six_root_loss_embedded','bb10b824:CATCHUP_CAMPAIGN_20260808_2206_ET.md:1329-1333; shifted, no preservation assumption')
 source=complete if family=='A' else tuple(x for x in complete if x!=2)
 add(tuple(x+8 for x in source),'prior_complete_root_loss_embedded','bb10b824:CATCHUP_CAMPAIGN_20260808_2206_ET.md:2205-2217; B deletes even counter2; then shift8; no preservation assumption')
 add(tuple(2*x+(6 if family=='A' else 8) for x in source),'prior_complete_root_loss_scaled_embedded','same source; scaling and translation only generate a new tested support')
 for shift,scale in [(0,1),(2,1),(10,1),(100,1),(500,1),(0,2),(0,5),(0,20)]:
  add(tuple(scale*x+shift for x in cycle),'prior_shifted_cycle_root_loss_embedded','bb10b824:CATCHUP_SHIFTED_CYCLE_REPORT_20260928_1021_ET.md:99-120; direct/shifted/scaled new support, no anchor outcome preservation')
 attempt=0
 while len(items)<256:
  r=1+(attempt%maxr);mode=(attempt//maxr)%4;attempt+=1
  if mode==0:T=rng.sample(range(lo,1001),r)
  elif mode==1:
   bank=sorted(set([lo,lo+2,19,21,37,41,99,101,127,257,509,997,1000]));T=rng.sample(bank,r)
  elif mode==2:
   centre=rng.randrange(lo,980);cluster=list(range(centre,min(1001,centre+r+6)));T=rng.sample(cluster,r)
   if r>1:T[-1]=lo if lo not in T[:-1] else 1000
  else:
   T=[lo+rng.randrange(1,12)]+[min(1000,lo+int((i+1)**3*1000/(r+1)**3)+rng.randrange(0,5)) for i in range(r-1)]
  T=even_adjust(T,lo)
  if len(T)!=r or paired(T):continue
  add(T,['uniform_unpaired','multiscale_unpaired','cluster_and_outlier','nonlinear_separated'][mode])
 rows.extend(items.values())
rows.sort(key=lambda a:(len(a['T']),max(a['T']),sum(a['T']),a['T'],a['family']))
for i,a in enumerate(rows,1):a['id']=i;a['tail_sum']=sum(a['T']);a['cardinality']=len(a['T']);a['unpaired']=True
assert len(rows)==512
receipt={'purpose':'ONE bounded discriminator for generic direct anchor NONLOSS, unpaired tails; stop on firstLOSS','random_seed_A':20261022,'random_seed_B':20261023,'planned_cases':512,'planned_per_family':256,'order':'tailcard,maxlabel,tailsum,lexT,family; first loss diagnostic is not a universal smallest counterexample','max_label':1000,'actual_explicit_list':rows,'family_cardinality_counts':{f:dict(collections.Counter(a['cardinality'] for a in rows if a['family']==f)) for f in ['A','B']},'frontier_note_sha256':hashlib.sha256((P.parent/'frontier/root-upper-reentry.md').read_bytes()).hexdigest(),'seconds':time.monotonic()-start}
(P/'root_anchor_unpaired_seeds.json').write_text(json.dumps(receipt,indent=2)+'\n')
(P/'root_anchor_unpaired_seeds.txt').write_text(''.join(str(a['id'])+' '+a['family']+' '+str(len(a['T']))+' '+' '.join(map(str,a['T']))+'\n' for a in rows))
print('SAVED_ONE_EXPLICIT_UNPAIRED_BATCH',len(rows),'cardinalities',receipt['family_cardinality_counts'],'seconds',receipt['seconds'],flush=True)
