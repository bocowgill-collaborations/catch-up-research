> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Independent review

Reviewer: independent agent `upper_exchange_review_20260929`.
Read-only assignment, no additional agents, computations, or source edits.

Verdict: **PASS for Target B**, with no mathematical gap found.

The reviewer independently checked:

- Q_N(N-3) has the stated remaining set and deficit N-4.
- A winning tied opening means its responder-relative post-opening value is loss.
- The exact-sum obstruction uses strictly subdeficit preparation, followed by an
  equality catch that switches players. Its terminal conditions are justified.
- The residual after deleting 1,N-3,N-4 is exactly [2,N-5] plus the three top counters.
- Every symbolic branch, exact sum, membership, distinctness, and dominating
  leaf in the new module, including m=10 and m=11 boundaries.
- The exceptional turn 2,6,15 has prefix sum 8<9 and leaves ({3,7},14), a terminal loss.
- The four small kernel classifier calls select the correct protected player;
  parity below N=15 leaves exactly N=11 and N=12.
- Source dependencies through exact-sum obstruction, winning-opening uniqueness,
  completed-turn safety, and the classifier are independent of the open conjecture.

The transitive axiom audit subsequently passed for every public claim and the
set-difference/transfer restatements. The reviewer accepted this as closing the
machine-dependency caveat. The source-path inspection and machine audit are
separate checks, not substitutes for each other.

## Additional narrow review: common-support exchange

The reviewer approved the diagnosis in ARGUMENT.md: deleting the other disjoint
exact-sum block produces a common parent at deficit d, not zero. When the initial
post-opening state can catch, the preparation is legal; when it cannot, the
derived state is directly terminal and losing. Both cases justify the value
claim. The even-effective-total example ({6,7,8},3) has three winning catches.

This only blocks the naive tied-uniqueness inference. It neither refutes Target A
nor establishes that its dense ancestry can realize that example.

No approval was requested or claimed for the conceptual helper's separate
dominant-pair candidate. That idea is marked unformalized in SIDE_IDEA.md.
