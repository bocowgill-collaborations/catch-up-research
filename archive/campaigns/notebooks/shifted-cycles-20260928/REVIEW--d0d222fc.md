> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Independent review — September 28, 2026

Reviewer: `/root/shifted_cycle_review_20260928`, fresh context, read-only.
This was the only reviewer used for the run; no research agents were launched.

Verdict: **correct within the stated scope (PASS)**. No mathematical error found.

Checked:

- `Edge` requires both memberships, nonterminality, and a winning move outcome.
  Player polarity and equality switching agree with the actual definitions.
- Adjacent and nonadjacent reversal formulas handle natural subtraction correctly.
- Root loss forces outgoing edges; the finite relation argument proves a
  positive-length closed directed walk, not a cyclic sequence of actual play.
- `S0` refutes filled-span exclusion even under root loss.
- `S1` refutes the unconditional minimum slide. Its computational draw is not a
  root-loss-conditioned counterexample.
- The maximum vertex at `N=7` has only the winning reply three. The parametric
  critical inversion is a raw-outcome theorem; legal interpretation needs the
  additional conditions stated in the report.
- All 25 public theorems are covered by the transitive axiom audit. The reviewer
  replayed the scoped warning-strict build; only `propext`, `Classical.choice`,
  and `Quot.sound` appeared.
- The checker replay passed. The reviewer separately regenerated all ten saved
  graph records and both seeded discoveries and matched `results.json`.
- Tuple-based outcomes and selected absolute-score checks agree with the exact
  completed-margin recurrence.

Two documentation corrections were requested: fix the malformed Lean module
heading and replace the report's pending verification paragraph with final status.
The parent applied these corrections; no mathematical changes were needed.

The optional 6,585-support negative scan was not independently replayed. This
bounded negative scan is not used to prove any theorem.

This review does not certify full-interval acyclicity, loss-conditioned
intact-interval sliding, the uniform first-pair endpoint, or Catch-Up.
