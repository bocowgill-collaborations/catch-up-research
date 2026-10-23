#!/usr/bin/env python3
import itertools as it
import random
from pathlib import Path
P=Path(__file__).resolve().parent
rng=random.Random(20261028)
pool=(10,14,16,18,20,22,24,26,28,30,40,60)
B=set(it.combinations(pool,4))
for _ in range(128):
    B.add(tuple(sorted(rng.sample([10]+list(range(14,162,2)),4))))
B.update([(10,20,40,80),(10,14,20,40),(10,16,20,40),
          (10,20,40,160),(14,20,40,80)])
(P/'inputs.txt').write_text(''.join(' '.join(map(str,b))+'\n' for b in sorted(B)))
print('COMPLETE supports',len(B))
