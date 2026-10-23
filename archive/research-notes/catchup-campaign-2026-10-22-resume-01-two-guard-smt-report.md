> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.UnitGuardObstruction](../../CatchUp/UnitGuardObstruction.lean).

# Unit-deficit, minimum-two diagnostic

Candidate lemma: if min R=2 and Even(sum R+1), then V(R,1) is NONLOSS.
The parent asked for falsification, not a formal theorem. We queried
R={2} union U, with exactly k distinct ordered integer labels U>=3 and odd
sum U. This is exactly the stated minimum/parity condition. Labels were
unbounded; cardinality was bounded.

Results: **UNSAT at k=2,3,4,5**, corresponding to support sizes 3 through 6.
Solver times were 0.029, 0.021, 0.110, and 1.365 seconds. Maximum recorded
child RSS was 127,549,440 bytes. All four queries exited zero; no timeout or
unknown occurred. No k>=6 query was run. No SAT witness or Lean theorem was
produced. An UNSAT result is evidence only for this unverified encoding and
fixed cardinality; it does not establish the uniform candidate.

`search.py` imports the already independently reviewed ownership-state
`Encoding` class unchanged from `../shadow-smt/search.py`. That class was
checked against 16 literal roots, 16 second-mover controls, score translations,
wrong-outcome and broken-alternation controls. The new query adds only the
minimum, ordering, odd-sum and LOSS constraints. Both players retain every
legal choice, and compulsory continuation/equality switching are preserved.
No new numerical evaluator or game semantics was introduced.

Exact commands, timings, hashes, ownership/edge counts and outputs are in
`query_k*.json`, `query_k*.smt2`, and `query_k*.out`; compact results are in
`summary.json`. Z3 5.1.0 ran with memory_max_size=8192 MB, 60-second internal
query limits, 65-second subprocess limits, and a 300-second overall loop
budget. The complete run took under two seconds. No active process remains.

Reproduce from the workspace root:

```sh
python3 research/catchup/campaign_2026_10_22/resume_01/two-guard-smt/search.py
```

This leaves the proof question open. If the candidate is proved uniformly,
the intended root application chooses 7 in the eight-shadow, then invokes
the lemma on {2,3,4} union T at deficit1. That strategic implication still
requires its actual formal proof; these solver results are not its premise.
