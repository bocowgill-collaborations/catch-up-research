#!/usr/bin/env python3
"""One parent-specified fifteenth control; no preservation assumption."""
from pathlib import Path
import importlib.util,json,subprocess,time
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('reuse',HERE/'search.py')
reuse=importlib.util.module_from_spec(spec);spec.loader.exec_module(reuse)
absolute=reuse.base.absolute
start=time.monotonic();old=[1,2,3,7,14,23,37,68,101,111,123]
s=tuple(sorted([2*x for x in old]+[3]));assert s[0]==2 and sum(s)%2==1
line='15 '+str(len(s))+' '+' '.join(map(str,s))+'\n'
(HERE/'scaled_control_input.txt').write_text(line)
p=subprocess.run([str(HERE/'controls')],input=line,capture_output=True,text=True,timeout=30)
(HERE/'scaled_control_native.out').write_text(p.stdout+p.stderr);assert p.returncode==0
r=json.loads(p.stdout);v=absolute(s,0,1)
moves={str(x):-absolute(tuple(y for y in s if y!=x),1,x) for x in s}
assert v==r['value'] and moves==r['moves'] and max(moves.values())==v
r.update(source_support=old,support=s,transformation='multiply every original label by2, then insert3',
         assumed_outcome_preservation=False,literal_value=v,literal_all_moves=moves,literal_pass=True,
         seconds=time.monotonic()-start,scope='one explicitly specified transformed state, no uniform or Lean result')
(HERE/'scaled_control_results.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r),flush=True)
