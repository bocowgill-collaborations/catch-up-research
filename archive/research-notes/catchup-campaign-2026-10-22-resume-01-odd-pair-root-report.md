> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.OddPairRootObstruction](../../CatchUp/OddPairRootObstruction.lean).

# Odd-start pairs do not rescue arbitrary tied NONWIN

The very first prescribed variant has tied-root value WIN computationally:

  Pair starts: {3,57,65,77,81,97}.
  Support: {3,4,57,58,65,66,77,78,81,82,97,98}.
  Deficit:0. Total sum:766 (even).

All six pair starts are odd and all pairs are disjoint. Opening4 is the
unique winning choice and the only nonlosing choice; the other11 openings
all lose. Frozen ExactSlots and the independent literal-score evaluator
agree on the root and every one of its12 openings. This is computational
evidence; no Lean certificate was generated in this experiment.

The eight prescribed supports were saved in lexicographic start order before
evaluation. The first WIN triggered the required stop immediately:1 of8
cases completed,7 explicitly preserved as unprocessed. No non-WIN cases
completed, so none of the three predetermined non-WIN literal controls could
be run without violating the stop instruction. The actual WIN received the
full independent check. No additional population or extended search ran.

This refutes the broad conjecture that every even number of disjoint
odd-start adjacent pairs has a nonwinning tied root. It does not refute
Catch-Up or the particular consecutive-tail one-pair-deletion obligation.
For a precise comparison, write A_N={3,4} union [9,N]. The witness is a
subset of A_100 obtained by deleting41 whole adjacent pairs, leaving6.
It is not A_N with only one pair deleted. `ambient_embedding.json` lists
all41 missing pair starts. The gaps are substantial and cannot be removed
without an independently proved outcome-preservation theorem.

Total runtime including compilation and literal replay was
0.937s; native CPU was0.000466s. Peak child RSS
high-water was105824256 bytes. The15-second CPU and30-second
wall caps were not reached. All owned jobs have ended.

Reproduce from workspace root:

```sh
python3 research/catchup/campaign_2026_10_22/resume_01/odd-pair-root/run.py
```

The appropriate next step is a compact kernel certificate if this obstruction
will be used to retire the general odd-start route. The actual residual
problem needs its consecutive-tail and single-hole hypotheses retained.
No claim is made that this is the smallest such witness.
