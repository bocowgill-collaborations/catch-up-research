> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.DenseTerminalReduction](../../CatchUp/DenseTerminalReduction.lean).

# Uniform cutoff for the actual terminal lower branch

`CatchUp/DenseTerminalReduction.lean` proves the arithmetic cutoff N<=9.
The statement needs neither a losing parent value, a winning-opening premise,
nor maximality of the exact block. It isolates the actual terminal condition
`sum((S minus B).erase w)<w`.

## Exact scope

`terminal_branch_bound` assumes:

* S is contained in [1,N], and h is its **actual** missing-counter count;
* `2*h+1 <= d <= N`, and `sum(S)+d` is even;
* B is a subset of S with sum d;
* w belongs to S minus B, w<d, and d-w is missing from S;
* after deleting B and w, the remaining total is strictly below w.

It concludes N<=9. There is no parity assumption on N itself. The target
t=d-w is positive because w<d. Its missingness is arithmetic membership,
not a predicate defined through the evaluator's answer.

## Proof

Replace w in S by the missing target t, forming
`A=insert t (S.erase w)`. The replacement preserves the cardinality r of S.
It remains a set of distinct positive counters in [1,N]. Exact deletion gives
`sum(S)=d+w+sum(C)`, where `C=(S minus B).erase w`.
Consequently `sum(A)=d+t+sum(C)<d+t+w=2*d<=2*N`.
Also `sum(S)+d=sum(A)+2*w`, so sum(A) is even.

The actual hole count gives `N=r+h`; the density assumption gives
`N+1<=2*r`. If N>=10, then r>=6. A positive r-element set has sum at least
the triangular sum r*(r+1)/2. The module derives this lower bound using
the complement and the previously proved `TurnDepth.interval_subset_sum_core`
and `TurnDepth.interval_sum_twice`; it introduces no new generic framework.

For r>=6, that triangular lower bound is at least 4*r-3, hence at least 2*N-1.
But an even sum strictly below 2*N is at most 2*N-2. This contradiction proves
the cutoff. `small_even_sum_bound` contains this final symbolic argument.

## Sharp arithmetic boundary

`cutoff_nine_witness` checks the following finite arithmetic instance in
Lean's kernel:

```
N=9, d=9, S={2,3,4,6,8}, B={3,6}, w=8, t=1.
```

There are four holes, so 2*h+1=d. The effective total is 32; B sums to 9;
t is missing; and C={2,4} has total 6<8. Thus the same arithmetic hypotheses
cannot imply N<=8. This witness makes no game-outcome claim about `(S,d)`.

## Verification and remaining finite obligation

From `research/catchup`:

```
lake --wfail build CatchUp.DenseTerminalReduction
lake env lean campaign_2026_10_22/frontier/dense-terminal/audit.lean
```

The explicit module build passed in 6.103 seconds wall time, with 3.6 seconds
reported for the new module. `build.log` and `axioms.log` retain the checks.
Four transitive axiom audits use only the three standard axioms. Source
hashes, bytes, lines, theorem count, and preservation checks are recorded in
`source-check.json`. No old source, root import, dependency, or toolchain was
changed. There is no `sorry`, native proof evaluation, custom axiom, unsafe
definition, or budget override. `MinSumProbe.lean` retains the independent
helper proof; no production module imports campaign scratch files.

This module reduces this terminal branch to N<=9. It does not classify the
remaining finite parent games or prove the complete proposed terminal-branch
nonloss statement. The parent assigns that finite proof and its composition
separately. No closure of density/subsum hypotheses, complete strategy, H,
or C is established here.
