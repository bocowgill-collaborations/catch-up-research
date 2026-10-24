> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Gates: upper-opening exchange

OWNS: research/upper-exchange-20260929/**, scripts/catch_up/LowerRayFourthEndpoint*.lean, CATCHUP_UPPER_EXCHANGE_REPORT_20260929_0034_ET.md

Scope: bounded conceptual research, exact status of both targets, audited completed claims, preservation.

- [x] G1: New branch starts at the latest local descendant of d016a035 and old artifacts are preserved.
  EVIDENCE: Initial HEAD d016a035 on newest local descendant; new branch codex/catchup-upper-exchange-20260929. All changes before staging are new untracked files only.
- [x] G2: Target A has a concrete derivation or exact documented gap after a serious exchange attempt.
  EVIDENCE: ARGUMENT.md common-support diamond reaches positive deficit, not a tied state; independently reviewed in REVIEW.md. Full A is explicitly unresolved.
- [x] G3: Target B has a concrete derivation or exact documented gap, unless A consumes the allowed proof window with a near-complete proof.
  EVIDENCE: LowerRayFourthEndpoint.lean proves stronger unconditional N>=15 result and requested even-total N>=11 result, without smaller draw premise.
- [x] G4: Every new production Lean theorem passes the affected-scope warning-strict build and standard-axiom audit.
  CHECK: lake --wfail build catch_up.LowerRayFourthEndpoint catch_up.LowerRayFourthEndpointAudit
  EXPECT: Build completed successfully
  EVIDENCE: exit=0; shell=/bin/sh; cwd=HISTORICAL_TMP/catchup-score-debt-20260928; path=b3b3957d716f/28 entries; EXPECT=matched; output-sha256=a26b42566153e9802da1f2d6c79acdf34ce4d73bfa2200a17a122b5f8b2fab5c; output-bytes=2373
- [x] G5: Claimed complete mathematical arguments receive independent semantic review.
  EVIDENCE: Independent read-only reviewer approved all B branches, exact statement, polarity, terminal cases, finite exceptions, and source dependencies; also approved narrow A diagnosis. SIDE_IDEA.md explicitly makes no audited claim.
- [x] G6: New report separates proof, computational evidence, conjecture, and remaining gaps; completed work is committed locally without pushing or merging.
  EVIDENCE: Commit 3b7e47fd contains only ten new intended files; git diff --cached --check passed, and post-commit status was clean. Report explicitly distinguishes proved B, unresolved A, and unformalized side idea. No push or merge occurred; final preservation notes are committed separately.
