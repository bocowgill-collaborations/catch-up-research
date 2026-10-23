#!/usr/bin/env python3
"""Audit each entry point separately, preserving the original namespaces."""
from pathlib import Path
import hashlib, json, platform, re, resource, subprocess, sys, time
ALLOWED={'propext','Classical.choice','Quot.sound'}

def validate(output, expected):
    reports={name:{a.strip() for a in axioms.split(',') if a.strip()}
             for name,axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",output)}
    for name in re.findall(r"'([^']+)' does not depend on any axioms",output):reports[name]=set()
    assert reports.keys()==expected, {'missing':sorted(expected-reports.keys()),'extra':sorted(reports.keys()-expected)}
    for name,axioms in reports.items():assert axioms<=ALLOWED,(name,axioms-ALLOWED)
    return len(reports)

def main():
    root=Path.cwd()
    assert (root/'AxiomAudit.lean').is_file(),'Run from the repository root or cryptid directory'
    try:validate("'control' depends on axioms: [sorryAx]",{'control'})
    except AssertionError:pass
    else:raise AssertionError('negative control accepted')
    start=time.monotonic()
    dest=root/'verification/local';dest.mkdir(parents=True,exist_ok=True)
    groups=[('','AxiomAudit.lean','AuditAll.lean')]
    if (root/'ComponentAxiomAudit.lean').is_file():
        groups.append(('components-','ComponentAxiomAudit.lean','ComponentAuditAll.lean'))
    receipts=[]
    for prefix,named,full in groups:
        begin=time.monotonic()
        expected=set(re.findall(r'^#print axioms ([\w.]+)',(root/named).read_text(),re.M))
        command=['lake','env','lean','-DwarningAsError=true',named]
        result=subprocess.run(command,text=True,capture_output=True,timeout=900)
        output=result.stdout+result.stderr
        (dest/(prefix+'axioms.log')).write_text(output)
        if result.returncode:print(output);raise SystemExit(result.returncode)
        n=validate(output,expected)
        full_command=['lake','env','lean','-DwarningAsError=true',full]
        result=subprocess.run(full_command,text=True,capture_output=True,timeout=900)
        output=result.stdout+result.stderr
        (dest/(prefix+'all-theorems.log')).write_text(output)
        if result.returncode:print(output);raise SystemExit(result.returncode)
        match=re.search(r'Full theorem audit passed: (\d+) public Catch-Up theorems',output)
        assert match,output
        receipts.append({'entry':named,'endpoints':n,'all_public_catchup_theorems':int(match[1]),
                         'commands':[command,full_command],'seconds':time.monotonic()-begin,
                         'audit_source_sha256':hashlib.sha256((root/named).read_bytes()).hexdigest(),
                         'full_audit_source_sha256':hashlib.sha256((root/full).read_bytes()).hexdigest()})
    peak=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    if sys.platform!='darwin':peak*=1024
    receipt={'status':'PASS','groups':receipts,'seconds':time.monotonic()-start,
             'peak_child_rss_bytes':peak,'platform':platform.platform(),
             'allowed_axioms':sorted(ALLOWED),'negative_control':'rejected sorryAx'}
    (dest/'axioms.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('Axiom audit passed: '+', '.join(f"{g['entry']} {g['endpoints']} endpoints" for g in receipts)+'; negative control rejected')

if __name__=='__main__':main()
