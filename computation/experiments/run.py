#!/usr/bin/env python3
"""Portable, bounded entry points for retained research drivers. No Lean claims.

Run from any directory. Defaults run small diagnostics, never resume a search.
Only --scope historical selects the explicitly listed original batches.
"""
import argparse
import json
import math
import os
from pathlib import Path
import resource
import shlex
import shutil
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


class Incomplete(RuntimeError):
    pass


def bounded(command, *, cwd, seconds, memory_mib, stdin=None):
    """Kill and reap the direct child on wall timeout; all drivers are synchronous.

    Linux: virtual-address cap. macOS: no hard memory cap is claimed.
    CPU and wall limits apply on both. Compiler subprocesses use a separate cap.
    """
    def limits():
        cpu = max(1, math.ceil(seconds))
        resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu + 1))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        if sys.platform.startswith('linux'):
            resource.setrlimit(resource.RLIMIT_AS, (memory_mib * 1024**2,) * 2)
    try:
        # Batch inputs are already finite strings. A file avoids blocking writes to
        # stdin while the solver is blocked flushing its reply pipe (seen on macOS).
        with tempfile.TemporaryFile(mode='w+', encoding='utf-8') as batch:
            if stdin is not None:
                batch.write(stdin)
                batch.seek(0)
            result = subprocess.run(command, cwd=cwd,
                                    stdin=batch if stdin is not None else subprocess.DEVNULL,
                                    text=True, capture_output=True, timeout=seconds, preexec_fn=limits)
    except subprocess.TimeoutExpired as exc:
        raise Incomplete('wall timeout; no complete experiment result') from exc
    if result.returncode:
        raise Incomplete('child failed or hit a limit (exit %s): %s' %
                         (result.returncode, result.stderr[-1000:]))
    return result.stdout


def build(source, output):
    compiler = shlex.split(os.environ.get('CXX', 'c++'))
    if not compiler or shutil.which(compiler[0]) is None:
        raise Incomplete('a C++ compiler is required (set CXX if necessary)')
    standard = 'c++20' if source.name == 'catch_up_search.cpp' else 'c++17'
    cmd = compiler + ['-O2', '-std=' + standard, '-pthread', '-include', 'cstdlib',
                      str(source), '-o', str(output)]
    result = subprocess.run(cmd, text=True, capture_output=True, timeout=30)
    output.with_suffix('.compile.txt').write_text(result.stdout + result.stderr)
    if result.returncode:
        raise Incomplete('compilation failed; inspect the compile log')


def positions(binary, rows, output, seconds, memory_mib):
    """Validated protocol for the retained consecutive-tail evaluator (1..15 slots)."""
    for r in rows:
        s, d = r['support'], r['deficit']
        if not (1 <= len(s) <= 15 and len(s) == len(set(s)) and
                all(type(x) is int and 0 < x <= 10000 for x in s) and
                type(d) is int and 0 <= d <= 10000):
            raise ValueError('invalid or unsupported explicit-slot position')
    text = ''.join('%s %s %s %s\n' % (r['id'], len(r['support']), r['deficit'],
                    ' '.join(map(str, r['support']))) for r in rows)
    output.with_suffix('.input.txt').write_text(text)
    raw = bounded([str(binary)], cwd=output.parent, seconds=seconds,
                  memory_mib=memory_mib, stdin=text)
    output.write_text(raw)
    values = [json.loads(line) for line in raw.splitlines()]
    if len(values) != len(rows):
        raise Incomplete('missing evaluator rows')
    for r, v in zip(rows, values):
        if (v.get('id') != r['id'] or v.get('deficit') != r['deficit'] or
                set(v.get('moves', {})) != set(map(str, r['support'])) or
                v.get('value') not in (-1, 0, 1) or
                any(x not in (-1, 0, 1) for x in v['moves'].values()) or
                max(v['moves'].values()) != v['value']):
            raise Incomplete('inconsistent evaluator row')
        v.update(r)
    return values


def turns(remaining, deficit, prefix=()):
    """All ordered completed turns when catching is possible, with no early stopping."""
    if not remaining:
        return
    if sum(remaining) < deficit:
        raise ValueError('no catch-up turn: the rules allocate all remaining counters')
    for x in remaining:
        tail = tuple(y for y in remaining if y != x)
        if x >= deficit or not tail:
            yield prefix + (x,)
        else:
            yield from turns(tail, deficit - x, prefix + (x,))


def consecutive(binary, ns, output, seconds, memory_mib):
    roots = [dict(id=i, N=n, support=[2, 3, 4] + list(range(9, n + 1)), deficit=1)
             for i, n in enumerate(ns, 1)]
    values = positions(binary, roots, output/'roots.jsonl', seconds, memory_mib)
    endpoints = []
    for r, v in zip(roots, values):
        if v['moves']['2'] < 0:
            raise Incomplete('the tested anchor 2 is unsafe')
        remaining = tuple(x for x in r['support'] if x != 2)
        for path in turns(remaining, 1):
            endpoints.append(dict(id=len(endpoints)+1, N=r['N'], opponent_picks=path,
                                  support=[x for x in remaining if x not in path],
                                  deficit=sum(path)-1))
    replies = positions(binary, endpoints, output/'endpoints.jsonl', seconds, memory_mib)
    # Exactly one whole opponent turn after our safe anchor; not a recursive policy proof.
    if any(r['value'] < 0 for r in replies):
        raise Incomplete('defender loses at an endpoint after the chosen anchor')
    failures = [r for r in replies if not any(r['moves'].get(str(y), -1) >= 0
                for y in (r['opponent_picks'][-1]-1, r['opponent_picks'][-1]+1))]
    return dict(Ns=ns, roots=values, opponent_turns=len(replies),
                adjacent_reply_failures=failures)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('experiment', choices=['packed', 'seven-pairs', 'four-orphan',
                                              'near-repair', 'consecutive', 'whole-turn'])
    parser.add_argument('--scope', choices=['smoke', 'historical'], default='smoke')
    parser.add_argument('--n', type=int, default=12, help='packed smoke case, 1..12 only')
    parser.add_argument('--seconds', type=float, default=15,
                        help='wall limit per evaluated subprocess, at most 60')
    parser.add_argument('--memory-mib', type=int, default=256)
    parser.add_argument('--out', type=Path, help='new output directory; never overwrites a run')
    args = parser.parse_args(argv)
    if not math.isfinite(args.seconds) or not 0 < args.seconds <= 60:
        parser.error('--seconds must be in (0,60]')
    if not 32 <= args.memory_mib <= 1024 or not 1 <= args.n <= 12:
        parser.error('memory must be 32..1024 MiB and N must be 1..12')
    if args.experiment == 'packed' and args.scope == 'historical':
        parser.error('large historical packed tables are not part of this runner')
    output = (args.out or ROOT/'verification/local/experiments'/
              ('%s-%s-%s' % (args.experiment, args.scope, time.time_ns()))).resolve()
    output.mkdir(parents=True, exist_ok=False)
    start = time.monotonic()
    receipt = dict(experiment=args.experiment, scope=args.scope, status='incomplete',
                   evidence='untrusted computational replay, not a Lean certificate',
                   seconds_per_child=args.seconds, memory_mib=args.memory_mib,
                   memory_limit_kind='virtual-address cap' if sys.platform.startswith('linux')
                   else 'no OS memory cap; fixed bounded input profiles only',
                   initialization='all builds and data are created in this new output directory')
    try:
        def call(source, name, tail=None, stdin=None):
            binary = output/name
            build(source, binary)
            return bounded([str(binary)] + (tail or []), cwd=output, seconds=args.seconds,
                           memory_mib=args.memory_mib, stdin=stdin)
        if args.experiment == 'packed':
            table = output/'table.bin'
            source = ROOT/'computation/solvers/packed/catch_up_search.cpp'
            raw = call(source, 'packed', ['--solve', str(args.n), '--verify', '--threads', '1',
                                         '--save', str(table)])
            (output/'solve.txt').write_text(raw)
            raw = bounded([str(output/'packed'), '--verify-table', str(table), '--threads', '1'],
                          cwd=output, seconds=args.seconds, memory_mib=args.memory_mib)
            (output/'table-check.txt').write_text(raw)
            receipt['N'] = args.n
        elif args.experiment in ('seven-pairs', 'four-orphan'):
            folder = HERE/args.experiment.replace('-', '_')
            if args.experiment == 'seven-pairs':
                jobs = [('probe', 'root_inputs.txt', '4 6 10 12 20 40 42\n'),
                        ('round', 'round_inputs.txt', '6 10 12 20 40\n')]
            else:
                jobs = [('probe', 'inputs.txt', '10 20 40 80\n')]
            for driver, inputs, smoke in jobs:
                frozen = (folder/inputs).read_text() if args.scope == 'historical' else smoke
                target = output/(driver+'.input.txt')
                target.write_text(frozen)
                text = call(folder/(driver+'.cpp'), driver,
                            [str(target), str(output/(driver+'.rows.txt'))])
                if not text.startswith('COMPLETE '):
                    raise Incomplete('driver did not report completion')
                (output/(driver+'.summary.txt')).write_text(text)
        elif args.experiment == 'near-repair' and args.scope == 'historical':
            text = call(HERE/'near_repair/probe.cpp', 'probe', [str(output/'rows.txt')])
            if not text.startswith('COMPLETE '):
                raise Incomplete('driver did not report completion')
            (output/'summary.txt').write_text(text)
        elif args.experiment in ('consecutive', 'near-repair'):
            binary = output/'positions'
            build(HERE/'consecutive/probe.cpp', binary)
            if args.experiment == 'consecutive':
                ns = [11] if args.scope == 'smoke' else [11, 12, 15, 16, 19, 20]
                receipt['checks'] = consecutive(binary, ns, output, args.seconds, args.memory_mib)
            else:
                rows = [dict(id=i, q=q, support=[7,10,11,18,19,20,21,40,41,q], deficit=q-7)
                        for i, q in enumerate([42, 98], 1)]
                receipt['checks'] = positions(binary, rows, output/'positions.jsonl',
                                              args.seconds, args.memory_mib)
        else:
            source = HERE/'whole_turn/test.py'
            shutil.copyfile(source, output/'test.py')
            if args.scope == 'historical':
                command = [sys.executable, str(output/'test.py')]
            else:
                # Only a ten-counter diagnostic; no seven/nine-pair batch is launched.
                command = [sys.executable, '-c',
                           'import test; R=(5,6,7,10,11,13,20,21,40,41); '
                           'assert test.balanced(R,4) is None; '
                           'print("whole-turn diagnostic reproduced")']
            (output/'summary.txt').write_text(bounded(command, cwd=output, seconds=args.seconds,
                                                      memory_mib=args.memory_mib))
        receipt['status'] = 'complete'
    except (Incomplete, subprocess.SubprocessError, OSError, ValueError) as exc:
        receipt['reason'] = str(exc)
    receipt['elapsed_seconds'] = time.monotonic() - start
    (output/'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))
    return 0 if receipt['status'] == 'complete' else 2


if __name__ == '__main__':
    sys.exit(main())
