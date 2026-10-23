#!/usr/bin/env python3
"""Small exact Catch-Up explorer; experimental computation, not a proof certificate.

Reuses the normalized recurrence of the existing first-pair research solver.
Supports distinct positive counters; maximizes ternary outcomes, not score margin.
Every legal pick is evaluated. An unfinished search exits with status 2.
"""
from __future__ import annotations
import argparse
import json
import math
import time

NAMES={-1:'loss',0:'draw',1:'win'}

class SearchLimit(RuntimeError):
    pass

class Solver:
    def __init__(self, counters, seconds=10.0, max_states=200_000):
        self.counters=tuple(sorted(counters))
        if any(type(x) is not int or x<=0 for x in self.counters):
            raise ValueError('Counters must be positive integers')
        if len(set(self.counters))!=len(self.counters):
            raise ValueError('Counters must be distinct; multisets are a different input model')
        if not math.isfinite(seconds) or seconds<=0 or max_states<1:
            raise ValueError('Resource limits must be positive')
        self.started=time.monotonic()
        self.deadline=self.started+seconds
        self.max_states=max_states
        self.visits=0
        self.memo={}
        self.totals={0:0}
        self.full=(1<<len(self.counters))-1

    def budget(self):
        if time.monotonic()>=self.deadline:
            raise SearchLimit('time limit reached')
        if self.visits>=self.max_states:
            raise SearchLimit('state limit reached')

    def picks(self, mask):
        while mask:
            bit=mask&-mask
            yield bit,self.counters[bit.bit_length()-1]
            mask-=bit

    def total(self,mask):
        if mask not in self.totals:
            bit=mask&-mask
            self.totals[mask]=self.counters[bit.bit_length()-1]+self.total(mask^bit)
        return self.totals[mask]

    def value(self,mask,deficit):
        key=(mask,deficit)
        if key in self.memo:return self.memo[key]
        self.budget()
        self.visits+=1
        if not mask:answer=0 if deficit==0 else -1
        elif self.total(mask)<deficit:answer=-1
        else:
            answer=-1
            for bit,x in self.picks(mask):
                child=self.value(mask^bit,abs(deficit-x))
                candidate=child if x<deficit else -child
                answer=max(answer,candidate)
        self.memo[key]=answer  # exact entries only; exceptions never install an outcome
        return answer

    def report(self,deficit=None):
        if deficit is not None and (type(deficit) is not int or deficit<0):
            raise ValueError('Deficit must be a nonnegative integer')
        initial=deficit is None
        if initial:
            rows=[]
            for bit,x in self.picks(self.full):
                child=self.value(self.full^bit,x)
                rows.append({'pick':x,'turn':'swap','child_deficit':x,
                             'child_outcome':NAMES[child],'pick_outcome':NAMES[-child]})
            value=max((-self.value(self.full^bit,x) for bit,x in self.picks(self.full)),default=0)
        else:
            value=self.value(self.full,deficit)
            rows=[]
            if self.full and self.total(self.full)>=deficit:
                for bit,x in self.picks(self.full):
                    child=self.value(self.full^bit,abs(deficit-x))
                    rows.append({'pick':x,'turn':'continue' if x<deficit else 'swap',
                                 'child_deficit':abs(deficit-x),'child_outcome':NAMES[child],
                                 'pick_outcome':NAMES[child if x<deficit else -child]})
        return {'status':'exact','perspective':'player one' if initial else 'acting player',
                'remaining':list(self.counters),'deficit':0 if initial else deficit,
                'opening':initial,'outcome':NAMES[value],'picks':rows,
                'states':self.visits,'seconds':time.monotonic()-self.started,
                'assurance':'untrusted exact computation; not Lean-certified by this script'}

def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--initial',type=int,metavar='N')
    group.add_argument('--remaining',type=int,nargs='*',metavar='X')
    parser.add_argument('--deficit',type=int)
    parser.add_argument('--seconds',type=float,default=10.0)
    parser.add_argument('--max-states',type=int,default=200_000)
    args=parser.parse_args(argv)
    if args.initial is not None:
        if args.initial<0:parser.error('N must be nonnegative')
        if args.initial>20:parser.error('This small explorer accepts N <= 20; use a research solver for larger roots')
        if args.deficit is not None:parser.error('--initial already specifies the forced single opening')
        counters=range(1,args.initial+1)
    else:
        if args.deficit is None:parser.error('--remaining requires --deficit')
        counters=args.remaining
        if len(counters)>20:parser.error('This small explorer accepts at most 20 counters')
    try:
        solver=Solver(counters,args.seconds,args.max_states)
        report=solver.report(args.deficit)
    except ValueError as error:parser.error(str(error))
    except SearchLimit as error:
        print(json.dumps({'status':'incomplete','reason':str(error),'states':solver.visits}))
        return 2
    print(json.dumps(report,indent=2))
    return 0

if __name__=='__main__':raise SystemExit(main())
