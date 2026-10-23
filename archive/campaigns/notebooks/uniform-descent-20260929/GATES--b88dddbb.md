> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Gates: Catch-Up uniform descent

OWNS: research/uniform-descent-20260929/**, scripts/catch_up/UniformExactSumDescent*.lean, scripts/catch_up/AdjacentPairGeometry*.lean, scripts/catch_up/LowerRayFifthEndpoint*.lean, CATCHUP_UNIFORM_DESCENT_REPORT_20260929_*.md

Scope: A bounded conceptual search for uniform exact-sum descent and first-pair geometry, with verified results or exact preserved gaps.

- [x] G1: A new branch preserves the clean base and prior research artifacts.
  EVIDENCE: Base faad9dcc was the only latest local descendant; clean initial research tree; branch codex/catchup-uniform-descent-20260929 created. Separate main checkout unchanged.

- [x] G2: The report distinguishes parametric proofs, counterexamples, and unresolved parent obligations.
  EVIDENCE: CATCHUP_UNIFORM_DESCENT_REPORT_20260929_0843_ET.md gives exact k=4/N≥23 coverage, three-pair geometric results, computational-only examples, and all unbounded gaps. No claim of solving Catch-Up or increasing the certificate frontier.

- [x] G3: Every new production module passes warning-strict compilation and transitive axiom audit.
  CHECK: lake --wfail build catch_up.LowerRayFifthEndpointAudit catch_up.AdjacentPairGeometryAudit catch_up.UniformExactSumDescentAudit catch_up.AdjacentPairGeometryRepairAudit
  EXPECT: Build completed successfully
  EVIDENCE: Final rerun exit 0; expected success token matched. CWD=HISTORICAL_TMP/catchup-score-debt-20260928; zsh launcher and node spawnSync; 2840 ms; SHA256(stdout+stderr)=a170ea64066da109f52e238b6de6f9d90f8c789bf99c0cdc05c122d543a8b1bd. CHECKS.json preserves the complete output. All 24 named production declarations use only propext, Quot.sound, Classical.choice. GapAccounting separately passed warning-strict checking and the same whitelist (exit 0, 3909 ms). The negative control exited 1 specifically with 'Negative control rejected axiom' and 'sorryAx' (3787 ms), not an unrelated failure.

- [x] G4: An independent reviewer checks every claimed completed proof and its bridge to the parent target.
  EVIDENCE: PASS in REVIEW.md, PAIR_REVIEW.md, UNIFORM_OBSTRUCTION_REVIEW.md, REPAIR_REVIEW.md. The last includes the conditional GapAccounting theorem and its limitation, and a final-report scope review. The report's one nonblocking wording correction (no NONLOSS theorem in arbitrary k) was applied. One reviewer reused sequentially, no parallel reviewers.

- [x] G5: New timestamped report, reproducible artifacts, and local commits preserve the final state without push or merge.
  EVIDENCE: Research commit e293017b2e8855d0419bf0205b50116e48e70ee4 succeeded. Post-commit git status --porcelain=v1 was empty; all 35 paths added relative to faad9dcc, with no existing path changed or removed. A final documentation-only commit records this evidence. Main checkout still has only its original unrelated untracked research-targets-2026-08-07.md. No push or merge. Both run-owned helpers are completed and no run-owned terminal job remains.

Final accounting: 5 gates met, 0 unmet, 0 abandoned. These are verification and
handoff gates, not a claim that either uniform mathematical target was solved.
The final build was rerun successfully after removing trailing blank lines in
three audit files and GapAccounting; no theorem changed after review.
