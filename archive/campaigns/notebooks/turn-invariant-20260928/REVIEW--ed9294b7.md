> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Independent review

Reviewer: `/root/turn_reserve_review_20260928`, fresh-context, read-only.
No other reviewer or research agent was launched for this session.

## Paper argument

Verdict: **PASS**. No mathematical error found; scope is honest.

- Actual player identities agree with `CompletedTurn`, including equality.
- Every unpaired preparation prefix is below the opponent's deficit. An
  available paired counter prevents premature inability-to-catch termination.
- Both slack identities are correct. The relevant natural subtractions do not
  truncate: `t<=W<=L`, `g<=D`, and `L-t+delta>=0`.
- The empty-pair base case covers strict loss for the opponent, exhaustion at
  equality, and the empty tied state.
- Every genuine pairing satisfies `card(P)<=2D`. The minimum-counter argument
  forces opening three, empty unpaired pool, and N<=7.
- The obstruction excludes any immediate first-pick initialization within this
  certificate, not later entry, other adaptive strategies, or the conjecture.

One presentation correction was requested and applied: declare that D is a
natural number in the relaxed envelope.

This review of the prose is independent criticism, not formal verification.

## Final Lean statement-fidelity check

Verdict: **PASS**, no mismatch.

`BudgetEnvelope` is exactly the relaxed envelope E, with arbitrary B subset S
and natural D. The public iff theorem uses the correct child support and lead
`a-1`, and concludes feasibility exactly at N=7 and a=3 without parity.
There is no hidden outcome or strategy-existence assumption.

The genuine-pairing-to-envelope bridge and strategy soundness are paper-level
arguments. The numeric initialization classification is Lean-verified. The
reviewer checked the source statement and this distinction, not the kernel
implementation or a general Catch-Up proof.
