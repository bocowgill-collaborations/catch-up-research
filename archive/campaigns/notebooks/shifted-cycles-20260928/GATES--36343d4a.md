> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Gates: shifted winning-reply cycle investigation

OWNS: research/shifted-cycles-20260928/**, scripts/catch_up/ShiftedReplyCycle.lean, scripts/catch_up/ShiftedReplyCycleAudit.lean, CATCHUP_SHIFTED_CYCLE_REPORT_20260928_1021_ET.md

Scope: one-hour local-exchange investigation, with exact obstruction or proved exchange, scoped Lean verification, and preserved local commit.

- [x] G1: exact graph checker replays the interval samples, negative control, and selected exchange test
  CHECK: python3 -B research/shifted-cycles-20260928/cycle_probe.py
  EXPECT: SHIFTED CYCLE CHECKS PASS
  EVIDENCE: /bin/zsh, cwd HISTORICAL_TMP/catchup-score-debt-20260928, exit 0; success marker matched. Default checker and both seeded discoveries replayed; independent reviewer matched all ten saved graph records. Full evidence file SHA-256 a30dd51cb9e163432c86d4c28b93afbea091f49725ac55e24ad1703c3d19e3ca in verification.txt.

- [x] G2: completed Lean claims compile warning-strict and pass transitive axiom whitelist
  CHECK: lake --wfail build catch_up.ShiftedReplyCycleAudit
  EXPECT: Build completed successfully
  EVIDENCE: /bin/zsh, cwd HISTORICAL_TMP/catchup-score-debt-20260928, exit 0; Build completed successfully matched, including post-review rebuild. All 25 public theorems audited exactly once; standard logical axioms only. Source hashes and output in verification.txt, SHA-256 a30dd51cb9e163432c86d4c28b93afbea091f49725ac55e24ad1703c3d19e3ca.

- [x] G3: mathematical result distinguishes local exchange obstruction, graph acyclicity, and Catch-Up
  EVIDENCE: The single fresh-context reviewer returned PASS, no mathematical repairs. REVIEW.md records scope and two documentation corrections, both applied. The report states the open endpoint and exact limitations of each witness.

- [x] G4: old reports and certificates are unchanged; new report and completed artifacts are committed without push or merge before cutoff
  EVIDENCE: Commit 217eca1e contains exactly ten added files; git diff --name-status 24e3488d HEAD shows no modified or deleted preexisting file. Post-commit status was clean. One documentation-only follow-up records this evidence. No push/merge; primary commit at 10:53 EDT before the 11:21:12 cutoff. All launched build/checker processes and the one independent review completed.
