#!/usr/bin/env python3
"""Check copied source hashes, publication hygiene, and relative documentation links."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]

def stripped(s):
    # Nested Lean block comments, then line comments. Strings are retained deliberately.
    out=[];i=depth=0
    while i<len(s):
        if s.startswith('/-',i):depth+=1;i+=2
        elif depth and s.startswith('-/',i):depth-=1;i+=2
        elif depth:i+=1
        elif s.startswith('--',i):
            end=s.find('\n',i);i=len(s) if end<0 else end
        else:out.append(s[i]);i+=1
    return ''.join(out)

def main():
    manifest=json.loads((ROOT/'verification/source-manifest.json').read_text())
    for rel,expected in manifest.items():
        data=(ROOT/rel).read_bytes()
        assert hashlib.sha256(data).hexdigest()==expected['sha256'],rel
        assert len(data)==expected['bytes'],rel
    files=[p for p in ROOT.rglob('*') if p.is_file() and not any(t in p.relative_to(ROOT).parts for t in ['.lake','.git','__pycache__','local'])]
    for p in files:
        if p.relative_to(ROOT).as_posix() == 'archive/recovered/reply-maximum-companion/ReplyMaximumCompanion.olean':
            # The only archival binary: pin exact bytes, scan below, never import.
            recovery=json.loads((ROOT/'verification/reply-maximum-companion.json').read_text())
            row=next(r for r in recovery['artifacts'] if r['path']==p.relative_to(ROOT).as_posix())
            data=p.read_bytes()
            assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256']
            s=data.decode('utf-8',errors='replace')
        else:
            s=p.read_text()
        # Ordinary source references to account usage are not part of this public package.
        assert not re.search(r'[/]Users/|[/]private/var/|gh[opusr]_[A-Za-z0-9]{20,}|BEGIN (?:RSA |OPENSSH )?PRIVATE KEY',s),str(p)
        if p.suffix=='.lean':
            code=re.sub(r'"(?:[^"\\]|\\.)*"', '""', stripped(s))
            assert not re.search(r'\b(sorry|sorryAx|axiom|native_decide|ofReduceBool)\b',code),str(p)
            assert 'value_of_even_mul_succ_self_div_two' not in code,str(p)
        if p.suffix=='.md':
            for link in re.findall(r'\]\(([^)]+)\)',s):
                if re.match(r'[a-z]+://|#|mailto:',link):continue
                target=link.split('#')[0]
                if target:assert (p.parent/target).exists(),(str(p),link)
    # Positive control for forbidden proof terms.
    assert re.search(r'\bsorry\b',stripped('theorem bad : False := by sorry'))
    subprocess.run([sys.executable,str(ROOT/'scripts/check_sources.py')],cwd=ROOT,check=True,timeout=60)
    print(f'Export verified: {len(manifest)} preserved sources/data; documentation links and reference fidelity passed')

if __name__=='__main__':main()
