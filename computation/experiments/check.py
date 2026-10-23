#!/usr/bin/env python3
"""Small bounded publication checks. Never run a full historical search batch."""
import importlib.util
import itertools
import json
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
import run
sys.path.insert(0, str(ROOT/'computation'))
from check_semantics import absolute


def require(test, message):
    if not test:
        raise AssertionError(message)


def agrees(row):
    s, d = tuple(row['support']), row['deficit']
    require(absolute(s, 0, d) == row['value'], 'absolute-score root mismatch')
    for x in s:
        after = tuple(y for y in s if y != x)
        expected = -absolute(after, d, x) if x >= d else absolute(after, x, d)
        require(expected == row['moves'][str(x)], 'absolute-score pick mismatch')


def reject(action, exception):
    try:
        action()
    except exception:
        return
    raise AssertionError('negative control accepted')


def check_round(text):
    """Independent literal replay and exact branch coverage of the one 11-counter case."""
    s = (5,6,7,10,11,12,13,20,21,40,41)
    expected = set(run.turns(s, 8)); seen = set()
    for line in text.splitlines():
        fields = line.split()
        if fields[0] == 'STATE':
            require(int(fields[-1]) == absolute(s, 0, 8), 'round state mismatch')
            continue
        end = fields.index('REPLY'); last = fields.index('GUARANTEE')
        path = tuple(map(int, fields[1:end]))
        require(path in expected and path not in seen, 'illegal or duplicate opponent turn')
        seen.add(path)
        reply = list(map(int, fields[end+1:last]))
        remaining = tuple(x for x in s if x not in path); d = sum(path)-8; worst = 1
        for i, x in enumerate(reply):
            require(x in remaining and (x >= d) == (i == len(reply)-1), 'illegal reply')
            after = tuple(y for y in remaining if y != x)
            v = -absolute(after, d, x) if x >= d else absolute(after, x, d)
            worst = min(worst, v); remaining = after; d = abs(x-d)
        require(reply and int(fields[last+1]) == worst, 'round guarantee mismatch')
    require(seen == expected, 'missing opponent turn from round diagnostic')
    return len(seen)


def check_orphan(text):
    seen = {}; expected = {}; support = None; deficit = None
    for line in text.splitlines():
        f = line.split()
        if f[0] == 'ROOT':
            z, deficit = map(int, f[1:3]); starts = list(map(int, f[3:f.index('VALUE')]))
            support = tuple([z]+[x for b in starts for x in (b, b+1)])
            require(int(f[-1]) == absolute(support, 0, deficit), 'orphan root mismatch')
            key = (z, deficit); seen[key] = set(); expected[key] = set(run.turns(support, deficit))
        else:
            stop = f.index('CHILD'); path = tuple(map(int, f[1:stop]))
            require(path in expected[key] and path not in seen[key], 'illegal or duplicate orphan turn')
            seen[key].add(path)
            r = tuple(x for x in support if x not in path); d = sum(path)-deficit
            require(int(f[stop+1]) == absolute(r, 0, d), 'orphan child mismatch')
            begin = f.index('SAFE_FIRST')+1
            end = f.index('MATE') if 'MATE' in f else len(f)
            actual = set(map(int, f[begin:end]))
            safe = set()
            for x in r:
                after = tuple(y for y in r if y != x)
                v = -absolute(after, d, x) if x >= d else absolute(after, x, d)
                if v >= 0: safe.add(x)
            require(actual == safe, 'missing or incorrect safe orphan reply')
    require(len(seen) == 4 and seen == expected, 'missing orphan root or opponent turn')
    return sum(map(len, seen.values()))


def main():
    with tempfile.TemporaryDirectory(prefix='catchup-solvers-') as tmp:
        out = Path(tmp)
        # Same retained slots implementation, every first pick on all small subsets.
        binary = out/'slots'
        run.build(HERE/'consecutive/probe.cpp', binary)
        rows = []
        for n in range(1, 6):
            for s in itertools.combinations(range(1, 6), n):
                for d in range(sum(s)+2):
                    rows.append(dict(id=len(rows)+1, support=list(s), deficit=d))
        values = run.positions(binary, rows, out/'slots.jsonl', 10, 256)
        for row in values:
            agrees(row)
        corrupt = dict(values[0], value=1-values[0]['value'])
        reject(lambda: agrees(corrupt), AssertionError)
        # Empty support belongs to the public explorer, not this header's supplied-slot API.
        for support, deficit in [([], 0), ([1, 1], 0), ([0], 0), ([1], -1), ([1], 10001)]:
            reject(lambda: run.positions(binary, [dict(id=0, support=support, deficit=deficit)],
                                        out/'bad.jsonl', 1, 256), ValueError)
        reject(lambda: run.bounded([sys.executable, '-c', 'import time; time.sleep(2)'],
                                  cwd=out, seconds=0.02, memory_mib=256), run.Incomplete)
        reject(lambda: run.bounded([sys.executable, '-c', 'raise SystemExit(3)'],
                                  cwd=out, seconds=1, memory_mib=256), run.Incomplete)
        # Compile the retained packed solver and its independent small calibration.
        packed_source = ROOT/'computation/solvers/packed/catch_up_search.cpp'
        packed = out/'packed'
        run.build(packed_source, packed)
        calibration = out/'calibration'
        # build() selects C++20 from the preserved source name; this harness also needs it.
        import os, shlex
        cmd = shlex.split(os.environ.get('CXX', 'c++')) + [
            '-O2', '-std=c++20', '-pthread', str(packed_source.with_name('check_small.cpp')),
            '-o', str(calibration)]
        subprocess.run(cmd, check=True, capture_output=True, timeout=30)
        calibration_text = run.bounded([str(calibration)], cwd=out, seconds=10, memory_mib=256)
        require('Small packed calibration passed' in calibration_text, 'missing calibration')
        for n in range(1, 13):
            text = run.bounded([str(packed), '--solve', str(n), '--verify', '--threads', '1'],
                               cwd=out, seconds=10, memory_mib=256)
            report = dict(line.split('=', 1) for line in text.splitlines() if '=' in line)
            expected = absolute(tuple(range(1, n+1)), 0, 0, True)
            require(report['root_value'] == {-1:'loss', 0:'draw', 1:'win'}[expected],
                    'packed root mismatch')
            require(report['independent_scalar_verification'] == 'pass', 'no scalar check')
            actual = dict(item.split(':') for item in report['opening_values'].split(','))
            for x in range(1, n+1):
                v = -absolute(tuple(y for y in range(1, n+1) if y != x), 0, x)
                require(actual[str(x)] == {-1:'L', 0:'D', 1:'W'}[v], 'packed opening mismatch')
        table = out/'table.bin'
        run.bounded([str(packed), '--solve', '8', '--save', str(table), '--threads', '1'],
                    cwd=out, seconds=10, memory_mib=256)
        run.bounded([str(packed), '--verify-table', str(table), '--threads', '1'],
                    cwd=out, seconds=10, memory_mib=256)
        data = table.read_bytes()
        # Flip a terminal outcome bit without changing the header or file size.
        bad = bytearray(data); bad[24] ^= 1
        table.write_bytes(bad)
        reject(lambda: run.bounded([str(packed), '--verify-table', str(table), '--threads', '1'],
                                  cwd=out, seconds=10, memory_mib=256), run.Incomplete)
        table.write_bytes(data[:12])
        reject(lambda: run.bounded([str(packed), '--verify-table', str(table)],
                                  cwd=out, seconds=10, memory_mib=256), run.Incomplete)
        # Reproduce the complete N=11 opponent reply set and the adjacent-mate failure.
        diagnostic = out/'consecutive'; diagnostic.mkdir()
        result = run.consecutive(binary, [11], diagnostic, 10, 256)
        for name in ('roots.jsonl', 'endpoints.jsonl'):
            specs = [line.split() for line in (diagnostic/Path(name).with_suffix('.input.txt')).read_text().splitlines()]
            for row, fields in zip(map(json.loads, (diagnostic/name).read_text().splitlines()), specs):
                row['support'] = list(map(int, fields[3:])); agrees(row)
        require(result['opponent_turns'] == 5, 'missing N=11 opponent reply')
        require(any(r['opponent_picks'] == (9,) for r in result['adjacent_reply_failures']),
                'known adjacent-mate obstruction missing')
        # Compile and smoke-run the original drivers, retaining all diagnostic branches.
        for experiment in ['seven-pairs', 'four-orphan', 'near-repair', 'whole-turn']:
            target = out/experiment
            child = subprocess.run([sys.executable, str(HERE/'run.py'), experiment,
                                    '--out', str(target)], capture_output=True, text=True, timeout=75)
            require(child.returncode == 0, child.stdout + child.stderr)
            receipt = json.loads((target/'receipt.json').read_text())
            require(receipt['status'] == 'complete' and receipt['scope'] == 'smoke', 'incomplete smoke')
            if experiment == 'near-repair':
                for row in receipt['checks']: agrees(row)
            if experiment == 'seven-pairs':
                raw = (target/'round.rows.txt').read_text()
                round_turns = check_round(raw)
                # This control removes an actual adversarial branch, not just an outcome bit.
                reject(lambda: check_round('\n'.join(raw.splitlines()[:-1])), AssertionError)
                picks = [line.split()[1] for line in (target/'probe.rows.txt').read_text().splitlines()
                         if line.startswith('PICK ')]
                require(set(picks) == set(map(str, (4,5,6,7,10,11,12,13,20,21,40,41,42,43)))
                        and len(picks) == 14, 'missing seven-pair first pick')
            if experiment == 'four-orphan':
                raw = (target/'probe.rows.txt').read_text()
                orphan_turns = check_orphan(raw)
                reject(lambda: check_orphan('\n'.join(raw.splitlines()[:-1])), AssertionError)
        # Compile the historical near-repair whole-turn-set driver but do not run its batch.
        run.build(HERE/'near_repair/probe.cpp', out/'near-repair-historical')
        # Regenerate seed lists in isolation and compare bytes; this starts no solver.
        for folder, generator, inputs in [
                ('seven_pairs', 'candidates.py', ['root_inputs.txt', 'round_inputs.txt']),
                ('four_orphan', 'inputs.py', ['inputs.txt'])]:
            target = out/(folder+'-seeds'); target.mkdir()
            (target/generator).write_bytes((HERE/folder/generator).read_bytes())
            if folder == 'seven_pairs':
                (target/'diagnostic_inputs.txt').write_bytes((HERE/folder/'diagnostic_inputs.txt').read_bytes())
            subprocess.run([sys.executable, str(target/generator)], check=True,
                           capture_output=True, timeout=5)
            for name in inputs:
                require((target/name).read_bytes() == (HERE/folder/name).read_bytes(),
                        'seed generator does not reproduce frozen input')
        print(calibration_text.strip())
        print('Solver smoke checks passed: %s slot positions and every first pick; roots N=1..12; '
              'all 5 N=11, %s round and %s orphan opponent turns; seeds, corruptions and limits' %
              (len(rows), round_turns, orphan_turns))


if __name__ == '__main__':
    main()
