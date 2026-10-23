#!/usr/bin/env python3
"""Reuse the campaign's small exhaustive absolute-score comparison against Lean output.

The Python calculation is an independent experiment, not a Lean proof premise.
"""
from pathlib import Path
from functools import lru_cache
import json, subprocess, time
ROOT=Path(__file__).resolve().parents[1]

@lru_cache(None)
def absolute(remaining, me, opponent, first=False):
    if not remaining:return (me>opponent)-(me<opponent)
    if me+sum(remaining)<opponent:return -1
    options=[]
    for i,x in enumerate(remaining):
        after=remaining[:i]+remaining[i+1:]
        if first or me+x>=opponent:options.append(-absolute(after,opponent,me+x))
        else:options.append(absolute(after,me+x,opponent))
    return max(options)

def main():
    start=time.monotonic()
    result=subprocess.run(['lake','env','lean','--run','computation/Regression.lean'],cwd=ROOT,text=True,capture_output=True,timeout=180)
    if result.returncode:raise RuntimeError(result.stdout+result.stderr)
    states=roots=0
    for line in result.stdout.splitlines():
        kind,*fields=line.split(',')
        if kind=='state':
            mask,d,actual=map(int,fields)
            remaining=tuple(i+1 for i in range(6) if mask&(1<<i))
            assert absolute(remaining,0,d)==actual==absolute(remaining,7,7+d),(remaining,d,actual)
            states+=1
        elif kind=='root':
            n,actual=map(int,fields)
            assert absolute(tuple(range(1,n+1)),0,0,True)==actual,(n,actual)
            roots+=1
        else:raise AssertionError(line)
    assert (states,roots)==(832,10),(states,roots)
    assert absolute((1,2),0,3)==0  # remaining total equals deficit
    assert absolute((1,2),0,4)==-1 # remaining total is too small
    assert absolute((),0,0)==0 and absolute((),0,1)==-1
    dest=ROOT/'verification/local';dest.mkdir(parents=True,exist_ok=True)
    (dest/'semantics.json').write_text(json.dumps({'status':'PASS','states':states,'roots':roots,'seconds':time.monotonic()-start},indent=2)+'\n')
    print('Semantics passed: 832 noninitial states, 10 roots and boundary controls')

if __name__=='__main__':main()
