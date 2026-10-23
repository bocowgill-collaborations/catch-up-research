"""The disclosed, deterministic public-text transformations for legacy Git exports.

This is formatting, not mathematical validation. Account-detail lines are removed
only by the rules below; reviewing that removal remains a separate obligation.
"""
import json
import os
import re
from pathlib import Path


PRIVATE_LINE = re.compile(
    r'(?:usage (?:meter|cutoff|threshold|shutdown)|(?:initial|latest|remaining|account|reported|start).*usage|'
    r'usage.*\d+%|\d+%.*(?:usage|remaining|preservation)|shutdown threshold)', re.I)


def clean(text):
    text = re.sub(r'[/]Users/[^/\s]+/(?:gh|\.codex/worktrees/[^/]+)/formal-conjectures(?=/|[\s`\"\'])',
                  'SOURCE_CHECKOUT', text)
    text = re.sub(r'ended early when the user-reported usage meter reached \d+(?:\.\d+)?%, '
                  r'as requested\. All\nresearch agents were stopped,',
                  "ended early at the user's request. All research agents were stopped,", text)
    text = re.sub(r'Reported account usage went from[^.]+shutdown threshold was not reached\.',
                  'Administrative stopping details omitted.', text, flags=re.S)
    text = re.sub(r'below, not because of a usage cutoff \(\d+(?:\.\d+)?% remained at the final check\)\.',
                  'below. Administrative stopping details are omitted.', text)
    text = re.sub(r'[/]Users/[^\s`\"\'<>\[\]()]+', 'SOURCE_CHECKOUT', text)
    text = re.sub(r'/private/(?:tmp|var)/[^\s`\"\'<>\[\]()]+',
                  lambda m: 'HISTORICAL_TMP/' + m[0].split('/')[-1], text)
    text = re.sub(r'(?<!\w)/tmp/[^\s`\"\'<>\[\]()]+',
                  lambda m: 'HISTORICAL_TMP/' + m[0].split('/')[-1], text)
    text = re.sub(r'(?<!\w)~/(?:\.codex|\.cache|\.unlazy)[^\s`\"\'<>\[\]()]*',
                  'HISTORICAL_TOOL_PATH', text)
    text = re.sub(r'\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}\b', '[contact omitted]', text)
    text = re.sub(r'gh[opusr]_[A-Za-z0-9]{20,}', '[credential omitted]', text)
    text = re.sub(r'\b[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\b',
                  'HISTORICAL_ATTACHMENT_ID', text)
    text = '\n'.join('[Administrative account detail omitted.]' if PRIVATE_LINE.search(line)
                     else line.rstrip() for line in text.splitlines()).rstrip() + '\n'
    text = re.sub(r'\[([^\]\n]+)\]\((?!https?://|#|mailto:)([^)\n]+)\)',
                  lambda m: m[1] + ' (`' + m[2] + '`; historical path)', text)
    # Do not expose the name of the private historical remote.
    text = re.sub(r'\b[\w.-]+/catch-up-(?:lean|private)-research\b',
                  'the historical private research remote', text)
    return text


def public_export(raw, original_path, export_path):
    """Reconstruct one Git-backed export, including JSON formatting and banner."""
    text = raw.decode('utf-8')
    suffix = Path(original_path).suffix
    if suffix in ('.json', '.jsonl'):
        def walk(value):
            if isinstance(value, str):
                return clean(value).rstrip('\n')
            if isinstance(value, list):
                return [walk(v) for v in value]
            if isinstance(value, dict):
                return {clean(k).rstrip('\n'): walk(v) for k, v in value.items()}
            return value
        if suffix == '.json':
            text = json.dumps(walk(json.loads(text)), ensure_ascii=False, indent=2) + '\n'
        else:
            text = ''.join(json.dumps(walk(json.loads(line)), ensure_ascii=False) + '\n'
                           for line in text.splitlines() if line.strip())
    else:
        text = clean(text)
        if suffix == '.md':
            target = os.path.relpath('results/legacy-findings.md', Path(export_path).parent)
            text = ('> **Historical campaign record.** This is a sanitized archival version, outside the verified build. '
                    'Claims of compilation, exact values, novelty and review below describe the original run. '
                    'Consult the [finding ledger](' + target + ') and current route guide for present assurance; '
                    'source hashes and all versions are in `verification/legacy-sources.json`. '
                    'Old commands and CHECK lines are inert historical text.\n\n' + text)
    return text.encode('utf-8')
