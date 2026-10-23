> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Gates: certificate-complexity pilot

OWNS: research/certificate_complexity_20260929/**, scripts/catch_up/CertificateComplexity*.lean, CATCHUP_CERTIFICATE_COMPLEXITY_REPORT_20260929_*.md

Scope: A precisely delimited certificate-size investigation, checked calibration and completed Catch-Up claims, reproducible measurements, independent review, and preserved report.

- [x] G1: The model distinguishes certificate existence, explicit DAG size, and mathematical proof size.
  EVIDENCE: CertificateComplexity.lean defines InitialCertificate, CertificateExists, and existence-indexed minimumNodes; report sections 1 and 6 distinguish the full and partial languages and proof length; REVIEW_FINAL.md independently accepts the exact quantifiers and classifications.

- [x] G2: Completed formal claims pass a warning-strict scoped build and a transitive axiom whitelist.
  CHECK: lake --wfail build catch_up.CertificateComplexityAudit catch_up.CertificateComplexityFixtures
  EXPECT: Build completed successfully
  EVIDENCE: exit=0; shell=/bin/sh; cwd=HISTORICAL_TMP/catchup-score-debt-20260928; path=b3b3957d716f/28 entries; EXPECT=matched; output-sha256=43ac4f298c607f48eb8f3fc10676737afc56be09c964a18638abac2df961855a; output-bytes=8210

- [x] G3: Any numerical measurements have reproducible witnesses and honest upper/lower/exact classifications.
  CHECK: python3 research/certificate_complexity_20260929/replay.py
  EXPECT: CERTIFICATE COMPLEXITY REPLAY PASSED
  EVIDENCE: exit=0; shell=/bin/sh; cwd=HISTORICAL_TMP/catchup-score-debt-20260928; path=b3b3957d716f/28 entries; EXPECT=matched; output-sha256=71d1e5ab316db6a47aaf9063d0a2f0e3e858d3eeb0397aa6fe8b29e44f8de960; output-bytes=730

- [x] G4: An independent reviewer checks the completed argument and the representation/proof-size distinction.
  EVIDENCE: REVIEW.md accepts the calibration and initial covering argument; REVIEW_HIGH_COUNTER.md accepts the exponential strengthening; REVIEW_FINAL.md independently rechecks the final statements, builds, axioms, literal counts, and replay. One reviewer, no helper agents; all final gates PASS.

- [x] G5: Old reports and certificates are unchanged; a new timestamped report states exact results and gaps.
  CHECK: python3 research/certificate_complexity_20260929/preserve_check.py
  EXPECT: CERTIFICATE COMPLEXITY PRESERVATION PASSED
  EVIDENCE: exit=0; shell=/bin/sh; cwd=HISTORICAL_TMP/catchup-score-debt-20260928; path=b3b3957d716f/28 entries; EXPECT=matched; output-sha256=e0ba2f96669401e84e38cc34dbfb3953565a4fbd33e06642d61e15ff24f30cba; output-bytes=74
