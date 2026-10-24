# PR #4: fresh review and integration

Reviewed original head `0dcb218f0e1c48f5b4cce18abb3567de5b4ccec2` against
main `39ea2ee354d87b33b87c2ad6359dc9f3eae85f88` after PR #3 merged.
This is a new evidence-led review pass by the AI assistant, not a separate
human review or an independently staffed verification team.

## Findings and fixes

1. **Integration conflict:** PR #3 and this PR edited the module count, coverage
   table and collection-check dispatch. Resolve by retaining both contributions
   and all check calls. The combined catalog contains 101 modules. No existing
   mathematical proof or toolchain pin is changed.
2. **Historical receipt incorrectly froze shared infrastructure:**
   `check_recovered_reply.py` required the original run's fingerprints to match
   the current aggregator, audit entry point, CI workflow and checker. This made
   independently valid additions fail. Keep that original receipt and all its
   logs unchanged as historical evidence, validate its hash fields, and continue
   enforcing the manifest's five current recovery-input fingerprints. Also
   cross-check the three immutable Lean inputs against the original receipt.
   Shared infrastructure is instead freshly exercised by current CI.
3. **Provenance qualification:** the raw trace establishes a now-missing source
   checkout directory, not its Git revision. The matching context branch and
   observed tip are useful leads, but their association is inferred. Clarify that
   distinction in the manifest and guide. Do not claim a compilation-time commit,
   original source recovery or an August creation date.

## Mathematics, source fidelity and privacy

The public source retains the maximum-bound and all-smaller-pair catchability
hypotheses. An edge `c→a` gives WIN for the replying mover. Since `a<c`, the turn
continues without negation. The nonterminal recurrence supplies a winning legal
`b`, and erasure ensures `b≠a,c`. The cross-pick identity handles both orders of
`a,b`, including equality at the catch threshold. The second nonterminal recurrence
then supplies edge `c→b`. The corollary drops only the additional witnesses from
the conclusion, not any assumption. At `c=0` an edge is impossible; zero counters
and empty residuals cause no omitted boundary case under the explicit hypotheses.

The original `.olean` and `.ilean` match the surviving private cache byte-for-byte;
all five private backup hashes also match. Lean's pinned `addDeclCore` implementation
calls `addDeclCheck` when `doCheck=true`; `readModuleData` only deserializes module
data. The replay installs no old imported environment or custom outcome assumption.
The readable proof has no dependency on the archived binary.

All 17 fingerprints in the original check receipt were independently compared
with their files at original head `0dcb218`; none was fabricated or silently
updated. Their historical meaning is retained after the integration fix.
The exact August scratch file and its reported hash remain unrecovered.

The publication scan covers the archived binary and metadata as well as public
text. Raw trace/setup files are not published. Public logs disclose path
redactions and retain both original and exported fingerprints. No private
correspondence or third-party PDF is added.

## Reverification

Fresh integrated-head checks and retained output fingerprints are recorded in
[pr4-review.json](pr4-review.json). Hosted CI is checked on the pushed head before
the merge decision; the original six green jobs are not treated as assurance
for the conflict resolution. Original recovery receipts remain unchanged.

All eleven recorded local commands passed. Mathematics has 174 named audit
endpoints and 4,503 public theorem declarations, including generated ones; only
the three permitted standard axioms occur. Both cryptid audit groups passed
(23/500 baseline and 201/2,962 components). The collection has 101 modules;
provenance/privacy checks, semantics, earlier certificate regressions, the finite
two-buffer replay, and both solver/campaign smoke suites passed. A fresh direct
compilation of the readable companion source passed with warnings as errors.
Mocking an altered current proof input through the full provenance checker still
rejects it after the historical-receipt fix; no file was mutated for that control.

Builds used warm pinned caches, and the unchanged cryptid import warnings remain
disclosed. No mathematical statement, proof body, toolchain or original artifact
was changed by this review. Remaining missing-source/historical-evidence caveats
are documented scope limitations, not claims resolved by this PR.
