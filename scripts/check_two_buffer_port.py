#!/usr/bin/env python3
"""Reconstruct the Lean port and compare its table to the retained JSON policy.

These are source/data checks, not substitutes for Lean's kernel or axiom audit.
"""
import copy
import hashlib
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
INPUTS = {
    'protocol': 'archive/catch_up/TwoBufferProtocol.lean.txt',
    'mandatory': 'archive/catch_up/TwoBufferMandatory.lean.txt',
    'roots': 'archive/catch_up/AdjacentHoleExchangeObstruction.lean.txt',
}
EXPORTS = {
    'protocol': 'CatchUp/TwoBufferProtocol.lean',
    'mandatory': 'CatchUp/TwoBufferMandatory.lean',
}
POLICY = 'computation/experiments/earlier-campaign/two-buffer/policy.json'


def require(test, message):
    if not test:
        raise ValueError(message)


def reconstruct(inputs):
    protocol = inputs['protocol'].replace(
        'import catch_up.ScoreDebtRepairCertificates',
        'import CatchUp.Earlier.ScoreDebtTerminalRepair\nimport CatchUp.Classifier')
    mandatory = inputs['mandatory'].replace(
        'import catch_up.TwoBufferProtocol', 'import CatchUp.TwoBufferProtocol')
    mandatory = mandatory.replace(
        '/-- Table lookup with an invalid default, so unlisted nonterminal states fail the checker. -/',
        '/-- Table lookup; default zero is illegal in every reached nonterminal actual state. -/')
    witness = inputs['roots']
    start = witness.index('/-- The left position at the admissible instance')
    end = witness.index('/-- The left position draws.', start)
    roots = ('namespace CatchUp.AdjacentHoleExchange\n\n' + witness[start:end] +
             'end CatchUp.AdjacentHoleExchange\n\n')
    mandatory = mandatory.replace('namespace CatchUp.TwoBuffer\n',
                                  roots + 'namespace CatchUp.TwoBuffer\n', 1)
    return {key: re.sub(r'^@\[category (?:API|test), AMS 91\]\n', '', value,
                        flags=re.M).encode()
            for key, value in [('protocol', protocol), ('mandatory', mandatory)]}


def lean_state(state):
    scores = state['scores']
    mover = state['mover']
    require(mover in (0, 1) and len(scores) == 2, 'invalid fixed-player state')
    require(scores[mover] <= scores[1 - mover], 'mover is not trailing or tied')
    counters = state['remaining']
    require(counters == sorted(set(counters)), 'noncanonical remaining support')
    require(all(type(x) is int and x > 0 for x in counters), 'invalid counter')
    return ('⟨⟨{' + ', '.join(map(str, counters)) + '}, ' +
            str(abs(scores[0] - scores[1])) + '⟩, .p' + str(mover + 1) + '⟩')


def policy_table(document):
    require(document['format'] == 'catchup-atomic-two-buffer-v1', 'unknown policy format')
    require(document['protected_player'] == 0 and document['root'] == 0,
            'wrong protected player or root')
    rows = []
    seen = {}
    for node in document['nodes']:
        action = node.get('action')
        if action is None:
            require('terminal_margins' in node and all(
                not node[side]['remaining'] or sum(node[side]['remaining']) <
                abs(node[side]['scores'][0] - node[side]['scores'][1])
                for side in ('U', 'V')), 'missing nonterminal action')
            continue  # runCheck handles terminal states before consulting the table.
        side, pick = action['side'], action['pick']
        require(side in ('U', 'V'), 'invalid scheduling side')
        mover = node[side]['mover']
        if pick is None:
            require((side, mover) in (('U', 1), ('V', 0)), 'wrong universal action')
            label = '.actualOpponent' if side == 'U' else '.shadowStrategy'
        else:
            require((side, mover) in (('U', 0), ('V', 1)), 'wrong controller action')
            require(pick in node[side]['remaining'], 'illegal controller pick')
            label = ('.actualPick ' if side == 'U' else '.shadowPick ') + str(pick)
        pair = '(' + lean_state(node['U']) + ', ' + lean_state(node['V']) + ')'
        require(pair not in seen or seen[pair] == label, 'history-dependent normalized action')
        seen[pair] = label
        rows.append('  (' + pair + ', ' + label + ')')
    return ('def policyEntries : List ((GamePosition × GamePosition) × Action) := [\n' +
            ',\n'.join(rows) + ']'), len(rows)


def reject(action, label):
    try:
        action()
    except (ValueError, KeyError):
        return
    raise ValueError('negative control accepted: ' + label)


def check_receipt():
    receipt = json.loads((ROOT / 'verification/two-buffer-port-checks.json').read_text())
    labels = {'protocol-direct', 'mandatory-direct', 'mathematics-build', 'mathematics-axioms',
              'collection', 'semantics', 'earlier-semantics', 'experiments', 'campaign',
              'recovered-reply', 'source-history', 'cryptid-build', 'cryptid-axioms'}
    require(receipt['status'] == 'PASS' and len(receipt['checks']) == len(labels) and
            {row['label'] for row in receipt['checks']} == labels, 'incomplete check receipt')
    for row in receipt['checks']:
        require(row['exit_code'] == 0, 'retained check failed')
        path = Path(row['log'])
        require(path.parts[:3] == ('verification', 'receipts', 'two-buffer-port') and
                '..' not in path.parts, 'invalid receipt log path')
        raw = (ROOT / path).read_bytes()
        require(len(raw) == row['output_bytes'] and
                hashlib.sha256(raw).hexdigest() == row['output_sha256'], 'receipt log changed')
    # These are historical check records. Do not pin mutable shared infrastructure
    # to this receipt's source fingerprints; rerun the current checks instead.


def main():
    manifest = json.loads((ROOT / 'verification/two-buffer-port.json').read_text())
    legacy = {r['id']: r for r in
              json.loads((ROOT / 'verification/legacy-sources.json').read_text())['records']}
    require({r['role'] for r in manifest['inputs']} == set(INPUTS), 'input scope changed')
    inputs = {}
    for row in manifest['inputs']:
        require(INPUTS[row['role']] == row['path'], 'wrong input path')
        raw = (ROOT / row['path']).read_bytes()
        record = legacy[row['source_id']]
        require(row['path'] == record['existing_path'], 'wrong archived source')
        require(hashlib.sha256(raw).hexdigest() == row['sha256'] == record['original_sha256'],
                'original source hash changed')
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        require(blob == row['git_blob'] == record['git_blob'], 'Git blob identity changed')
        require(row['source_commit'] in record['observed_commits'] and
                row['source_branch'] in record['branch_tips'] and
                row['original_path'] == record['original_path'], 'wrong source attribution')
        inputs[row['role']] = raw.decode()
    expected = reconstruct(inputs)
    require(set(manifest['exports']) == set(EXPORTS), 'export scope changed')
    names = []
    for role, path in EXPORTS.items():
        row = manifest['exports'][role]
        require(row['path'] == path, 'wrong export path')
        raw = (ROOT / path).read_bytes()
        require(raw == expected[role], 'undisclosed source change: ' + path)
        require(hashlib.sha256(raw).hexdigest() == row['sha256'] and
                len(raw) == row['bytes'], 'export fingerprint changed')
        names += re.findall(r'^theorem\s+([^\s(:]+)', raw.decode(), re.M)
    require(names == manifest['public_theorem_names'], 'theorem inventory changed')
    policy_raw = (ROOT / POLICY).read_bytes()
    require(hashlib.sha256(policy_raw).hexdigest() == manifest['policy_sha256'],
            'retained policy changed')
    document = json.loads(policy_raw)
    table, count = policy_table(document)
    actual = expected['mandatory'].decode()
    start = actual.index('def policyEntries :')
    end = actual.index('\n\n/-- Table lookup', start)
    require(table == actual[start:end], 'Lean table differs from JSON policy')
    # Exercise reconstruction and actual table comparison, not just copied hashes.
    bad = dict(inputs)
    bad['protocol'] = bad['protocol'].replace('v.completedMargin .p1 - 2',
                                              'v.completedMargin .p1 - 3')
    require(reconstruct(bad)['protocol'] != expected['protocol'], 'margin mutation accepted')
    bad = dict(inputs)
    bad['roots'] = bad['roots'].replace('{2, 5, 6, 9, 10, 11}', '{2, 5, 6, 8, 10, 11}')
    require(reconstruct(bad)['mandatory'] != expected['mandatory'], 'root mutation accepted')
    bad = copy.deepcopy(document)
    bad['nodes'][0]['action']['pick'] = 5
    require(policy_table(bad)[0] != table, 'policy mutation accepted')
    bad = copy.deepcopy(document)
    bad['nodes'].pop(1)
    require(policy_table(bad)[0] != table, 'missing table row accepted')
    bad = copy.deepcopy(document)
    bad['nodes'][0]['action']['side'] = 'V'
    reject(lambda: policy_table(bad), 'controller-side mutation')
    check_receipt()
    print(f'Two-buffer Lean port checks passed: 2 modules, {len(names)} public theorems, '
          f'{count} nonterminal policy rows; source reconstruction and five mutation controls')


if __name__ == '__main__':
    main()
