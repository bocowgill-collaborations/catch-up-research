#!/usr/bin/env python3
"""Bounded reproduction of archived mutation, shrinking and SMT experiments.

Default smoke profiles query a few already selected positions, not a new search.
Use prepare for an isolated legacy layout; use emit-smt to generate without solving.
"""
import argparse
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
CAMPAIGN = HERE/'campaign'
sys.path.insert(0, str(HERE))
import run


def load_encoding():
    spec = importlib.util.spec_from_file_location('catchup_archived_encoding',
                   CAMPAIGN/'resume_01/shadow-smt/search.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def recipes():
    return json.loads((ROOT/'verification/campaign-sources.json').read_text())['smt_queries']


def query(recipe):
    """Reconstruct the original input byte-for-byte using the retained Encoding."""
    b = load_encoding(); e = b.Encoding(recipe['timeout_ms'])
    k = recipe['tail_cardinality']
    if recipe['family'] == 'shadow-smt':
        ts = ['t%s' % i for i in range(k)]
        e.lines += ['(declare-const %s Int)' % t for t in ts]
        c = ['(>= %s 9)' % t for t in ts]
        c += ['(< %s %s)' % (a,z) for a,z in zip(ts,ts[1:])]
        e.lines.append('(declare-const half Int)')
        c.append('(= %s (* 2 half))' % b.linear(0,dict.fromkeys(ts,1)))
        shadow = e.root('C',[2,3,4,7]+ts,8)
        only = recipe['name'].endswith('_shadow_only')
        core = None if k == 5 and only else e.root('E',[4,7]+ts,1)
        c.append('(= %s (- 1))' % shadow)
        if not only: c.append('(= %s (- 1))' % core)
    else:
        ts = ['u%s' % i for i in range(k)]
        e.lines += ['(declare-const %s Int)' % t for t in ts]+['(declare-const half Int)']
        c = ['(>= %s 3)' % t for t in ts]
        c += ['(< %s %s)' % (a,z) for a,z in zip(ts,ts[1:])]
        c.append('(= %s (+ (* 2 half) 1))' % b.linear(0,dict.fromkeys(ts,1)))
        root = e.root('R',[2]+ts,1); c.append('(= %s (- 1))' % root)
    text = e.query(c)
    if (hashlib.sha256(text.encode()).hexdigest() != recipe['original_sha256'] or
            len(text.encode()) != recipe['bytes']):
        raise ValueError('regenerated SMT input does not match the original fingerprint')
    return text


def solve_smt(text, output, seconds, memory_mib):
    z3 = os.environ.get('Z3', 'z3')
    if shutil.which(z3) is None:
        raise run.Incomplete('Z3 executable required; put z3 on PATH or set Z3')
    path = output/'query.smt2'; path.write_text(text)
    result = run.bounded([z3, 'memory_max_size=%s' % memory_mib, str(path)],
                         cwd=output, seconds=seconds, memory_mib=memory_mib)
    (output/'solver.out').write_text(result)
    statuses = [s.strip() for s in result.splitlines() if s.strip() in ('sat','unsat','unknown')]
    if len(statuses) != 1 or '(error ' in result or statuses[0] == 'unknown':
        raise run.Incomplete('SMT unknown or malformed solver response; no game outcome')
    return dict(solver_result=statuses[0], query_sha256=hashlib.sha256(text.encode()).hexdigest(),
                solver_version=run.bounded([z3,'--version'],cwd=output,seconds=2,memory_mib=memory_mib).strip(),
                assurance='SMT evidence only; SAT requires independent model replay; UNSAT is not a Lean proof')


def prepare(output):
    """Copy source/data only. Does not execute a historical script or solver."""
    shutil.copytree(CAMPAIGN, output/'campaign')
    shutil.copytree(HERE/'seven_pairs', output/'seven_pairs',
                    ignore=shutil.ignore_patterns('__pycache__'))
    shutil.copyfile(HERE/'verify.py', output/'verify.py')
    shutil.copyfile(ROOT/'computation/check_semantics.py', output/'check_semantics.py')
    return dict(layout='campaign/, seven_pairs/, verify.py, check_semantics.py',
                executed_searches=0, instruction='Run historical scripts only here, with external resource limits.')


def selected_positions(profile):
    search = CAMPAIGN/'search'
    if profile == 'mutation-joint':
        seed = json.loads((search/'root_anchor_jointloss_mutation_seeds.json').read_text())
        nodes = seed['actual_explicit_list']
        small = [r for r in nodes if len(r['T'])<=4][:2]
        rows = small + [nodes[11148]]  # fixed original witness, not a fresh search
        specs = [dict(id=i+1, support=[4,7]+r['T'], deficit=d, original_id=r['id'])
                 for i,(r,d) in enumerate((r,d) for r in rows for d in (1,3))]
        return specs, dict(planned_original=18741, completed_original=11149, unprocessed_original=7592)
    if profile == 'mutation-two':
        seed = json.loads((CAMPAIGN/'resume_01/two-guard-adaptive-mutation/seeds.json').read_text())
        specs = [dict(id=i+1,support=seed['ordered_queries'][j-1]['support'],deficit=1,original_id=j)
                 for i,j in enumerate((1,40))]
        return specs, dict(planned_original=199, completed_original=40, unprocessed_original=159)
    if profile == 'shrink-joint':
        t = [18,33,35,36,52,56,62,74,100]
        tails = [t]+[t[:i]+t[i+1:] for i in range(len(t)) if t[i]%2==0]
        specs = [dict(id=i+1,support=[4,7]+r,deficit=d)
                 for i,(r,d) in enumerate((r,d) for r in tails for d in (1,3))]
        return specs, dict(smoke_scope='fixed witness and its even-label one-deletion neighbors only',
                           historical_scope='all 512 subsets, 256 even and 256 odd skips')
    # Replay the finalized alternating witness and its legal one-coordinate -2 neighbors.
    t = [19,36,37,50,57,60,99]; tails=[t]
    for i in range(len(t)):
        v=t.copy();v[i]-=2
        if v[0]>=9 and v==sorted(set(v)): tails.append(v)
    return [dict(id=i+1,support=[4,7]+r,deficit=1) for i,r in enumerate(tails)], dict(
             smoke_scope='final fixed witness and legal coordinate -2 neighbors only',
             historical_scope='16 admissible deletion subsets then greedy coordinate descent; no global minimum')


def historical(profile, output, seconds, memory_mib):
    """Only explicitly requested finite original batches; never called by smoke checks."""
    search=CAMPAIGN/'search'
    if profile=='mutation-joint':
        source=search/'root_anchor_jointloss_mutation_probe.cpp'
        args=[str(search/'root_anchor_jointloss_mutation_seeds.txt')]
    elif profile=='mutation-two':
        source=CAMPAIGN/'resume_01/two-guard-adaptive-mutation/probe.cpp';args=[]
    elif profile=='shrink-joint':
        source=search/'root_anchor_jointloss_shrink_probe.cpp';args=[]
    else:
        source=search/'root_alternating_gap_shrink_probe.cpp'
        args=[str(search/'root_alternating_gap_shrink_admissible.txt')]
    binary=output/'probe';run.build(source,binary)
    stdin=(source.parent/'input.txt').read_text() if profile=='mutation-two' else None
    text=run.bounded([str(binary)]+args,cwd=output,seconds=seconds,memory_mib=memory_mib,stdin=stdin)
    (output/'probe.out').write_text(text)
    if profile=='mutation-joint':
        cases=sum(l.startswith('CASE ') for l in text.splitlines())
        status='stopped_on_witness' if 'STOP_FIRST_DOUBLELOSS ' in text else 'complete'
        if not ('COMPLETE_FIXED_RADIUS_TWO ' in text or 'STOP_FIRST_DOUBLELOSS ' in text):
            raise run.Incomplete('mutation prefix stopped at a resource limit')
        return dict(status=status,completed=cases,planned=18741,unprocessed=18741-cases)
    if profile=='mutation-two':
        values=[json.loads(l) for l in text.splitlines()]
        if any('id' not in v for v in values):raise run.Incomplete('mutation CPU cap')
        found=bool(values and values[-1]['value']==-1)
        if not found and len(values)!=199:raise run.Incomplete('missing mutation rows')
        return dict(status='stopped_on_witness' if found else 'complete',completed=len(values),
                    planned=199,unprocessed=199-len(values))
    if profile=='shrink-joint':
        if 'COMPLETE_FIXED_SUPPORT_SHRINK ' not in text:raise run.Incomplete('incomplete shrink')
        return dict(status='complete',scope='minimum only among subsets of the fixed nine-label witness')
    checkpoint=next(json.loads(l) for l in text.splitlines() if json.loads(l)['kind']=='checkpoint')
    if checkpoint['time_cap'] or not checkpoint['one_step_fixed_point']:
        raise run.Incomplete('shrinking stopped before the fixed local search finished')
    return dict(status='complete',checkpoint=checkpoint,scope='fixed deletions and coordinate -2 moves only')


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('profile',choices=['mutation-joint','mutation-two','shrink-joint',
                                    'shrink-alternating','smt-shadow','smt-two','emit-smt','prepare'])
    p.add_argument('--scope',choices=['smoke','historical'],default='smoke')
    p.add_argument('--k',type=int,help='SMT tail cardinality; default 0 for shadow, 2 for two-guard')
    p.add_argument('--shadow-only',action='store_true')
    p.add_argument('--family',choices=['shadow-smt','two-guard-smt'],default='shadow-smt')
    p.add_argument('--seconds',type=float,default=10)
    p.add_argument('--memory-mib',type=int,default=256)
    p.add_argument('--out',type=Path)
    a=p.parse_args(argv)
    if not math.isfinite(a.seconds) or not 0<a.seconds<=60 or not 32<=a.memory_mib<=1024:
        p.error('seconds must be in (0,60], memory in 32..1024 MiB')
    family='two-guard-smt' if a.profile=='smt-two' else 'shadow-smt' if a.profile=='smt-shadow' else a.family
    k=a.k if a.k is not None else 2 if family=='two-guard-smt' else 0
    recipe=None
    if a.profile.startswith('smt-') or a.profile=='emit-smt':
        if a.profile=='smt-shadow':family='shadow-smt'
        name=('extension_k6' if k==6 else 'query_k%s'%k)+('_shadow_only' if a.shadow_only else '')
        recipe=next((r for r in recipes() if r['family']==family and r['name']==name),None)
        if recipe is None:p.error('no retained recipe for that family/cardinality')
        if a.profile!='emit-smt' and a.scope=='smoke' and k>(2 if family=='two-guard-smt' else 0):
            p.error('larger SMT arities require explicit --scope historical; emit-smt never solves')
    output=(a.out or ROOT/'verification/local/experiments'/('campaign-%s-%s'%(a.profile,time.time_ns()))).resolve()
    output.mkdir(parents=True,exist_ok=False);started=time.monotonic()
    receipt=dict(profile=a.profile,scope=a.scope,status='incomplete',seconds_per_child=a.seconds,
                 memory_mib=a.memory_mib,proof_claim='none; experimental replay only')
    try:
        if a.profile=='prepare':receipt['details']=prepare(output)
        elif recipe:
            text=query(recipe);(output/'query.smt2').write_text(text)
            receipt['recipe']=recipe
            if a.profile=='emit-smt':receipt['details']=dict(executed_solver=False)
            else:receipt['details']=solve_smt(text,output,a.seconds,a.memory_mib)
        elif a.scope=='historical':receipt['details']=historical(a.profile,output,a.seconds,a.memory_mib)
        else:
            rows,scope=selected_positions(a.profile);binary=output/'positions'
            run.build(HERE/'consecutive/probe.cpp',binary)
            receipt['details']=dict(scope=scope,positions=run.positions(binary,rows,output/'positions.jsonl',
                                                    a.seconds,a.memory_mib))
        receipt['status']='complete'
    except (run.Incomplete,subprocess.SubprocessError,OSError,ValueError,StopIteration) as exc:
        receipt['reason']=str(exc)
    receipt['elapsed_seconds']=time.monotonic()-started
    (output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
    return 0 if receipt['status']=='complete' else 2


if __name__=='__main__':sys.exit(main())
