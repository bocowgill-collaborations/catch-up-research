> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Candidate recorded before the search

Start: 2026-09-28 10:21:12 EDT. Hard cutoff: 11:21:12 EDT.

We test a local cycle-span mechanism, not arbitrary graph acyclicity as an assumption.

Candidate H: Let S be a finite set of integers at least three, with odd sum (so
the deficit-one effective total is even). A simple directed shifted-reply cycle
cannot have its entire integer span contained in S.

This is deliberately stronger than the intact-interval target: counters outside
the cycle span may have holes. It isolates the proposed justification that all
intermediate counters between the cycle extrema are available. If H holds,
every cycle for S = Icc 3 N is forbidden. If H fails, it refutes this local-span
mechanism, not the original full-interval acyclicity claim or Catch-Up.

Proposed proof step to inspect if H survives: slide a minimum cycle vertex to an
available intermediate counter, preserving its incoming and outgoing winning
replies, or create a shorter cycle. This step is not assumed true.

Search: exact shifted graphs on the requested interval roots and sparse negative
control, then short intact prefixes with two or three exceptional larger counters.
Stop at the first cycle whose span is full. Preserve it and inspect the common
three-deletion states. No buffer search, large table extension, or outcome-defined
rank is permitted.

## Disposition

The initial 6,585-support scan did not refute H. A bounded eight-counter residual
search then found S0 with a full-span adjacent two-cycle and a losing root. A
second bounded residual search found S1 with a nonadjacent two-cycle and an
unused intermediate counter, directly refuting the proposed minimum slide.
These examples and the intact N7 maximum-companion failure were reconstructed
and formalized. No new interval exchange survived; discovery stopped before the
halfway point. The remaining work was scoped verification, one independent
review, documentation, and preservation, not graph elaboration or table expansion.
