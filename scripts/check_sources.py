#!/usr/bin/env python3
"""Reference fidelity checks reused from the existing research verifier."""
from pathlib import Path
import re, json, hashlib
ROOT = Path(__file__).resolve().parents[1]
def strip_comments(text):
    text = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    return re.sub(r'--[^\n]*', '', text)


def declaration(text, kind, name):
    text = strip_comments(text)
    match = re.search(r'^' + re.escape(kind + ' ' + name) + r'(?=[\s(:])', text, re.M)
    assert match, (kind, name)
    rest = text[match.start():]
    following = re.search(
        r'\n(?:noncomputable def |def |theorem |lemma |inductive |structure |instance |end )',
        rest,
    )
    if following:
        rest = rest[:following.start()]
    rest = re.sub(r'@\[[^\n]*\]', '', rest)
    return re.sub(r'\s+', '', rest)


def assert_source_fidelity(compiled, literal):
    for kind, name in [
        ('inductive', 'Player'), ('def', 'Player.other'), ('inductive', 'Outcome'),
        ('def', 'Outcome.neg'), ('def', 'Outcome.best'), ('noncomputable def', 'valueAux'),
        ('noncomputable def', 'value'),
    ]:
        assert declaration(compiled, kind, name) == declaration(literal, kind, name), name


def source_checks():
    sources = json.loads((ROOT / 'verification/SOURCES.json').read_text())
    frozen = (ROOT / 'verification/upstream/CatchUpConjecture.lean.txt').read_bytes()
    blob = hashlib.sha1(b'blob ' + str(len(frozen)).encode() + b'\0' + frozen).hexdigest()
    assert blob == sources['reference_blob']
    raw = frozen.decode()
    expected = raw[:raw.rindex('/--\nLet $T_N')] + 'end CatchUp\n'
    expected = expected.replace('import FormalConjecturesUtil', 'import Mathlib')
    expected = re.sub(r'^@\[([^\n]*category[^\n]*)\]\n',
                      lambda m: '@[simp]\n' if 'simp,' in m[1] else '', expected, flags=re.M)
    expected = expected.replace('namespace CatchUp',
        '/-\nVendored from bb10b8246c8f7b99de084865826150459e5627f1. The unfinished conjecture is\n'
        'omitted; imports and repository-specific attributes are the only other changes.\n'
        '-/\n\nnamespace CatchUp', 1)
    compiled = (ROOT / 'CatchUp/Reference.lean').read_text()
    assert compiled == expected
    classifier = (ROOT / 'verification/upstream/Classifier.lean.txt').read_bytes()
    classifier_blob = hashlib.sha1(
        b'blob ' + str(len(classifier)).encode() + b'\0' + classifier).hexdigest()
    assert classifier_blob == sources['classifier_blob']
    assert (ROOT / 'CatchUp/Classifier.lean').read_text() == classifier.decode().replace(
        'import FormalConjectures.Paper.CatchUpConjecture', 'import CatchUp.Reference')
    literal = (ROOT / 'verification/upstream/LiteralReference.lean.txt').read_text()
    literal_bytes = literal.encode()
    literal_blob = hashlib.sha1(
        b'blob ' + str(len(literal_bytes)).encode() + b'\0' + literal_bytes).hexdigest()
    assert literal_blob == sources['literal_reference_blob']
    assert_source_fidelity(compiled, literal)
    # Positive control: a changed inequality must fail the fidelity check.
    corrupted = compiled.replace('if s_me\' ≥ s_opp then', 'if s_me\' > s_opp then')
    assert corrupted != compiled
    try:
        assert_source_fidelity(corrupted, literal)
    except AssertionError:
        pass
    else:
        raise AssertionError('fidelity checker accepted changed equality semantics')
    for path in (ROOT / 'CatchUp').glob('*.lean'):
        code = strip_comments(path.read_text())
        assert not re.search(r'\b(sorry|sorryAx|axiom|native_decide|ofReduceBool)\b', code), path
        assert 'value_of_even_mul_succ_self_div_two' not in code, path
    print('SOURCES_PASS: exact reference declarations, pinned blobs, mutation control, clean target')



if __name__ == "__main__":
    source_checks()
