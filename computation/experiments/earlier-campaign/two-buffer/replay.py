#!/usr/bin/env python3
"""Replay the saved policy independently, without importing its synthesis solver.

Tuple supports, absolute scores, and ordered permanent ownership histories come
from the earlier audited replay. Shadow reply sets use its independent ternary
absolute-score recurrence, not the new completed-margin recurrence.
"""

import argparse
import copy
import json
from pathlib import Path
import sys
from reference import State, absolute_value

sys.dont_write_bytecode = True
if not __debug__:
    raise SystemExit("Run without Python optimization: replay checks use assertions")


def snapshot_matches(st, record):
    assert list(st.remaining) == record['remaining']
    assert list(st.scores) == record['scores'] and st.mover == record['mover']
    assert sorted(x for x,owner,_ in st.owners if owner == 0) == record['owned_p0']
    assert sorted(x for x,owner,_ in st.owners if owner == 1) == record['owned_p1']


def verify(cert):
    assert cert['format'] == 'catchup-atomic-two-buffer-v1'
    assert cert['protected_player'] == 0 and cert['root'] == 0
    nodes = cert['nodes']
    assert all(n['id'] == i for i,n in enumerate(nodes))
    reached = set()
    endings = []
    branch_eleven = []
    branches = []
    def visit(i,u,v,trace,up,vp):
        assert 0 <= i < len(nodes)
        n = nodes[i]
        reached.add(i)
        snapshot_matches(u,n['U']); snapshot_matches(v,n['V'])
        width = [len(set(u.remaining)-set(v.remaining)),len(set(v.remaining)-set(u.remaining))]
        ledger = u.scores[0]-u.scores[1]-v.scores[0]+v.scores[1]
        assert width == n['buffer'] and max(width) <= 2 and ledger == n['ledger']
        assert absolute_value(v.remaining,*v.scores,v.mover) == 1
        if u.terminal() and v.terminal():
            um,uo = u.complete(); vm,vo = v.complete()
            assert [um,vm] == n['terminal_margins'] and um >= vm-2
            assert 'action' not in n and 'edges' not in n
            entry = {'U_picks':up,'V_picks':vp,'margins':[um,vm],
                     'U_ownership':uo,'V_ownership':vo,'events':trace}
            endings.append(entry)
            if len(up) > 1:
                branches.append(up[1])
            if up[:2] == [2,11]:
                branch_eleven.append(entry)
            return
        assert 'terminal_margins' not in n
        side,pick = n['action']['side'],n['action']['pick']
        assert side in ('U','V')
        st = u if side == 'U' else v
        assert not st.terminal()
        controlled = (side == 'U' and st.mover == 0) or (side == 'V' and st.mover == 1)
        if controlled:
            assert pick in st.remaining
            expected = [pick]
        else:
            assert pick is None
            expected = list(st.remaining)
            if side == 'V':
                expected = [x for x in expected if
                    absolute_value(st.pick(x).remaining,*st.pick(x).scores,st.pick(x).mover) == 1]
        assert expected and sorted(e['pick'] for e in n['edges']) == sorted(expected)
        for edge in n['edges']:
            x = edge['pick']
            nu,nv = (u.pick(x),v) if side == 'U' else (u,v.pick(x))
            assert len(nu.remaining)+len(nv.remaining) < len(u.remaining)+len(v.remaining)
            delta = (1 if st.mover == 0 else -1)*x*(1 if side == 'U' else -1)
            next_ledger = nu.scores[0]-nu.scores[1]-nv.scores[0]+nv.scores[1]
            assert next_ledger == ledger+delta
            event = {'side':side,'pick':x,'owner':st.mover,'ledger':next_ledger}
            visit(edge['child'],nu,nv,trace+[event],up+[x] if side == 'U' else up,
                  vp+[x] if side == 'V' else vp)
    visit(0,State((2,5,6,9,10,11),(0,1),0),State((2,5,6,7,10,11),(0,1),0),[],[],[])
    assert reached == set(range(len(nodes)))
    assert sorted(set(branches)) == [5,6,9,10,11]
    return {'policy_nodes':len(nodes),'terminal_histories':len(endings),
            'terminal_pairs':sorted(set(tuple(x['margins']) for x in endings)),
            'actual_second_picks':sorted(set(branches)),
            'branch_2_11':branch_eleven,'all_terminal_histories':endings}


def mutation_tests(cert):
    tests = []
    bad = copy.deepcopy(cert)
    bad['nodes'][0]['action']['pick'] = 5
    tests.append(bad)
    bad = copy.deepcopy(cert)
    target = next(n for n in bad['nodes'] if len(n.get('edges',[])) > 1)
    target['edges'].pop()
    tests.append(bad)
    bad = copy.deepcopy(cert)
    target = next(n for n in bad['nodes'] if 'terminal_margins' in n)
    target['terminal_margins'][0] += 2
    tests.append(bad)
    bad = copy.deepcopy(cert)
    bad['nodes'][1]['U']['owned_p0'] = []
    tests.append(bad)
    for bad in tests:
        try:
            verify(bad)
        except AssertionError:
            continue
        raise AssertionError('Mutation was not detected')
    return len(tests)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?',
                        default=Path(__file__).with_name('policy.json'))
    parser.add_argument('--full',action='store_true')
    args = parser.parse_args()
    with open(args.certificate) as stream:
        cert = json.load(stream)
    result = verify(cert)
    result['mutations_rejected'] = mutation_tests(cert)
    if not args.full:
        result.pop('all_terminal_histories')
    print(json.dumps(result,sort_keys=True,indent=2))


if __name__ == '__main__':
    main()
