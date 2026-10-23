from itertools import combinations
from pathlib import Path
import random,json
P=Path(__file__).resolve().parent
root=[tuple(map(int,x.split())) for x in (P/'diagnostic_inputs.txt').read_text().splitlines()]
root += [(4,*r) for r in combinations([x for x in range(6,30,2) if x!=8],6)]
rng=random.Random(20261025)
root += [(4,*sorted(rng.sample([x for x in range(6,162,2) if x!=8],6))) for _ in range(128)]
root=list(dict.fromkeys(root))
(P/'root_inputs.txt').write_text(''.join(' '.join(map(str,r))+'\n' for r in root))
base=list(combinations([x for x in range(6,26,2) if x!=8],3))
lift=[(6,10,12,20,40),(6,10,20,40,80),*list(combinations([x for x in range(6,24,2) if x!=8],5))]
(P/'round_inputs.txt').write_text(''.join(' '.join(map(str,r))+'\n' for r in base+lift))
print(json.dumps({'seven_root_shapes':len(root),'base_three_pair_residuals':len(base),'lifted_five_pair_residuals':len(lift)}))
