#!/usr/bin/env python3
"""Exact finite ownership-DAG SMT experiment; solver results are not Lean proofs.

Every legal pick is retained. Fixed player 1 maximizes {-1,0,1}, player 2
minimizes. The initial actor is player 1 with scores (0, deficit). A pick
changes actor iff the actor reaches or exceeds the other score. No special
opening occurs: all encoded roots are post-opening normalized positions.

No timeout or unknown result is interpreted as a game outcome.
"""
from __future__ import annotations
import argparse
import functools
import hashlib
import itertools
import json
import resource
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT))
from verify import absolute

import os
Z3 = os.environ.get('Z3', 'z3')

def number(n):
    return str(n) if n >= 0 else f'(- {-n})'

def linear(constant, coefficients):
    terms = [number(constant)] if constant else []
    for v, c in sorted(coefficients.items()):
        if c == 1:
            terms.append(v)
        elif c == -1:
            terms.append(f'(- {v})')
        elif c:
            terms.append(f'(* {number(c)} {v})')
    return '0' if not terms else terms[0] if len(terms) == 1 else '(+ ' + ' '.join(terms) + ')'

def sign(expr):
    return f'(ite (> {expr} 0) 1 (ite (= {expr} 0) 0 (- 1)))'

class Encoding:
    def __init__(self, timeout_ms=120000):
        self.lines = ['; finite ownership-state DAG, complete choices, fixed-player ternary payoff',
                      '(set-logic QF_LIA)', '(set-option :produce-models true)',
                      f'(set-option :timeout {timeout_ms})']
        self.states = self.edges = 0

    def root(self, prefix, labels, deficit, broken_alternation=False):
        n = len(labels)
        full = (1 << n) - 1
        def name(a, b, mover):
            return f'{prefix}_{a}_{b}_{mover}'
        def gap(a, b, extra_index=None, extra_sign=0):
            constant = -deficit
            coeff = {}
            for i, x in enumerate(labels):
                c = int(bool(a & (1 << i))) - int(bool(b & (1 << i)))
                if i == extra_index:
                    c += extra_sign
                if isinstance(x, int):
                    constant += c * x
                else:
                    coeff[x] = coeff.get(x, 0) + c
            return linear(constant, coeff)
        for size in range(n + 1):
            for remaining_indices in itertools.combinations(range(n), size):
                remaining = sum(1 << i for i in remaining_indices)
                assigned = full ^ remaining
                a = assigned
                while True:
                    b = assigned ^ a
                    for mover in (0, 1):
                        current = name(a, b, mover)
                        self.lines.append(f'(declare-const {current} Int)')
                        if not remaining:
                            rhs = sign(gap(a, b))
                        else:
                            choices = []
                            for i in remaining_indices:
                                bit = 1 << i
                                aa, bb = (a | bit, b) if mover == 0 else (a, b | bit)
                                if broken_alternation:
                                    outcome = name(aa, bb, 1 - mover)
                                else:
                                    delta = gap(a, b, i, 1 if mover == 0 else -1)
                                    relation = '>=' if mover == 0 else '<='
                                    outcome = (f'(ite ({relation} {delta} 0) '
                                               f'{name(aa, bb, 1-mover)} {name(aa, bb, mover)})')
                                choices.append(outcome)
                                self.edges += 1
                            # Range {-1,0,1} follows inductively from terminals.
                            preferred = 1 if mover == 0 else -1
                            fallback = -preferred
                            win = '(or ' + ' '.join(f'(= {x} {number(preferred)})' for x in choices) + ')'
                            draw = '(or ' + ' '.join(f'(= {x} 0)' for x in choices) + ')'
                            rhs = f'(ite {win} {number(preferred)} (ite {draw} 0 {number(fallback)}))'
                        self.lines.append(f'(assert (= {current} {rhs}))')
                        self.states += 1
                    if a == 0:
                        break
                    a = (a - 1) & assigned
        return name(0, 0, 0)

    def query(self, constraints, values=()):
        return '\n'.join(self.lines + [f'(assert {c})' for c in constraints] +
                         ['(check-sat)'] +
                         (['(get-value (' + ' '.join(values) + '))'] if values else []) +
                         ['(get-info :all-statistics)', '(exit)', ''])

def run(label, text, limit=125):
    path = HERE / (label + '.smt2')
    path.write_text(text)
    start = time.monotonic()
    timed_out = False
    try:
        p = subprocess.run([Z3, 'memory_max_size=8192', str(path)], text=True, capture_output=True, timeout=limit)
        output = p.stdout + p.stderr
        code = p.returncode
    except subprocess.TimeoutExpired as e:
        timed_out = True
        output = (e.stdout or b'').decode() if isinstance(e.stdout, bytes) else (e.stdout or '')
        output += '\nEXTERNAL_TIMEOUT\n'
        code = None
    (HERE / (label + '.out')).write_text(output)
    statuses = [line.strip() for line in output.splitlines() if line.strip() in ('sat', 'unsat', 'unknown')]
    record = dict(label=label, command=[Z3, 'memory_max_size=8192', str(path)], elapsed_seconds=time.monotonic()-start,
                  exit_code=code, external_timeout=timed_out,
                  result=statuses[0] if statuses else 'external_timeout' if timed_out else 'error',
                  smt2_bytes=path.stat().st_size,
                  smt2_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  output_sha256=hashlib.sha256(output.encode()).hexdigest(),
                  max_child_peak_rss_bytes_so_far=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
    (HERE / (label + '.json')).write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps(record), flush=True)
    return record, output

def validate():
    fixtures = [((), 0), ((), 1), ((1,), 0), ((1,), 1), ((1,), 2),
                ((2,3), 5), ((2,3), 6), ((1,3,4), 3), ((1,3,4), 4),
                ((2,4,7), 5), ((2,3,4,7), 8), ((4,7), 1),
                ((2,3,4,7,10), 8), ((4,7,10), 1),
                ((2,3,4,7,9,11), 8), ((4,7,9,11), 1)]
    encoded = Encoding(30000)
    values = []
    roots = []
    for i, (labels,d) in enumerate(fixtures):
        root = encoded.root(f'g{i}', labels, d)
        exact = absolute(labels, 0, d)
        translated = absolute(labels, 17, 17+d)
        assert translated == exact
        roots.append(root)
        values.append(dict(labels=labels, deficit=d, expected=exact, score_translation=translated))
    agreement = [f'(= {root} {number(v["expected"])})' for root,v in zip(roots,values)]
    mover_two = []
    for i,(labels,d) in enumerate(fixtures):
        exact = -absolute(labels,d,0)
        mover_two.append(dict(labels=labels,deficit=d,expected_fixed_player_one=exact))
        agreement.append(f'(= g{i}_0_0_1 {number(exact)})')
    r,_ = run('validation_goldens_correct', encoded.query(agreement), 35)
    assert r['result'] == 'sat', r
    r,_ = run('validation_goldens_no_mismatch', encoded.query(['(not (and ' + ' '.join(agreement) + '))']), 35)
    assert r['result'] == 'unsat', r
    wrong = encoded.query([f'(= {roots[2]} (- 1))'])
    r,_ = run('validation_injected_false_win', wrong, 35)
    assert r['result'] == 'unsat', r
    # Detect the actual rule bug, not just an arbitrary inconsistent assertion.
    bad = Encoding(30000)
    mismatch = None
    for n in range(1,6):
        if mismatch:
            break
        for labels in itertools.combinations(range(1,7), n):
            if mismatch:
                break
            for d in range(1, sum(labels)+1):
                good = absolute(labels,0,d)
                @functools.lru_cache(None)
                def broken(rem,me,opp):
                    if not rem:
                        return (me>opp)-(me<opp)
                    return max(-broken(rem[:i]+rem[i+1:],opp,me+x) for i,x in enumerate(rem))
                wrong = broken(labels,0,d)
                if wrong != good:
                    mismatch = (labels,d,good,wrong)
                    break
    assert mismatch
    labels,d,good,wrong = mismatch
    badroot = bad.root('bad',labels,d,True)
    r,_ = run('validation_broken_alternation', bad.query([f'(= {badroot} {number(good)})']),35)
    assert r['result']=='unsat',r
    r,_ = run('validation_broken_alternation_actual', bad.query([f'(= {badroot} {number(wrong)})']),35)
    assert r['result']=='sat',r
    result = dict(status='PASS', golden_cases=values, encoding_states=encoded.states,
                  encoding_edges=encoded.edges, broken_alternation_example=mismatch,
                  mover_two_cases=mover_two,
                  literal_source_sha256=hashlib.sha256((ROOT/'verify.py').read_bytes()).hexdigest(),
                  trust_boundary='Finite diagnostic validation; no Lean soundness theorem')
    (HERE/'validation.json').write_text(json.dumps(result,indent=2)+'\n')

def search(k, timeout_ms, shadow_only=False):
    assert 0 <= k <= 4 or (k == 5 and shadow_only)
    e = Encoding(timeout_ms)
    ts = [f't{i}' for i in range(k)]
    e.lines += [f'(declare-const {t} Int)' for t in ts]
    constraints = [f'(>= {t} 9)' for t in ts]
    constraints += [f'(< {a} {b})' for a,b in zip(ts,ts[1:])]
    total = linear(0,{t:1 for t in ts})
    # LIA equality with an auxiliary integer avoids a nonlinear/modulo theory.
    e.lines.append('(declare-const half Int)')
    constraints.append(f'(= {total} (* 2 half))')
    c = e.root('C',[2,3,4,7]+ts,8)
    core = None if (k == 5 and shadow_only) else e.root('E',[4,7]+ts,1)
    constraints += [f'(= {c} (- 1))']
    if not shadow_only:
        constraints += [f'(= {core} (- 1))']
    label=f'query_k{k}' + ('_shadow_only' if shadow_only else '')
    text = e.query(constraints)
    record, output = run(label,text,timeout_ms/1000+5)
    record.update(tail_cardinality=k, ownership_states=e.states, choice_edges=e.edges,
                  labels_unbounded=True, claim='C8 LOSS' if shadow_only else 'C8 LOSS and E1 LOSS', lean_certified=False)
    if record['result']=='sat':
        import re
        model_record, output = run(label+'_model', e.query(constraints, ts+[c]+([core] if core else [])),
                                   timeout_ms/1000+5)
        if model_record['result'] != 'sat' or model_record['exit_code'] != 0:
            record['model_replay_status'] = model_record['result']
            (HERE/(label+'.json')).write_text(json.dumps(record,indent=2)+'\n')
            return record
        tail = [int(re.search(r'\('+t+r'\s+([0-9]+)\)',output)[1]) for t in ts]
        assert tail == sorted(set(tail)) and all(t>=9 for t in tail) and sum(tail)%2==0
        contexts = []
        for prefix,labels,d in [('C',tuple([2,3,4,7]+tail),8),('E',tuple([4,7]+tail),1)]:
            absolute.cache_clear()
            value = absolute(labels,0,d)
            moves = {x:(absolute(tuple(y for y in labels if y!=x),x,d) if x<d else
                          -absolute(tuple(y for y in labels if y!=x),d,x)) for x in labels}
            assert (value == -1 or (shadow_only and prefix=='E')) and max(moves.values())==value
            contexts.append(dict(name=prefix,labels=labels,deficit=d,value=value,all_moves=moves))
        record.update(witness_tail=tail,literal_replay=contexts)
    (HERE/(label+'.json')).write_text(json.dumps(record,indent=2)+'\n')
    return record

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('mode',choices=['validate','search'])
    p.add_argument('--k',type=int,default=0);p.add_argument('--timeout-ms',type=int,default=120000)
    p.add_argument('--shadow-only',action='store_true')
    args=p.parse_args()
    assert 1 <= args.timeout_ms <= 120000
    if args.mode=='validate':validate()
    else:
        assert json.loads((HERE/'validation.json').read_text())['status']=='PASS'
        search(args.k,args.timeout_ms,args.shadow_only)
