> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.UnitGuardObstruction](../../CatchUp/UnitGuardObstruction.lean).

# Counterexample to the minimum-two/unit-deficit candidate

The proposed uniform nonloss statement fails in the exact computation:

    R={2,4,7,13,15,19,35,36,50,57,60,99}, deficit1.

Minimum(R)=2, sum(R)=397, and sum(R)+1=398 is even. The value is LOSS and
every one of its12 legal first picks loses against optimal opposition.
Frozen ExactSlots and independent literal-score evaluation agree on both
the root and every first choice. A new Lean certificate is still required;
no completed formal theorem is claimed in this experiment.

The state changes just37 to35 in the supplied DRAW position whose only safe
first pick was13. The same resulting set also arises by changing36 to35
and37 to36 simultaneously. Both generation histories are retained; no
outcome-preserving interpretation of either transformation is assumed.
Counter13 remains present, but its former defense fails, as do all alternatives.

The requested mutation neighborhood contained199 distinct valid new supports:
one non2 label +/-2, or two distinct non2 labels each +/-1. Invalid duplicate
labels, minimum violations and unchanged supports were discarded with their
reasons. Supports lacking the previous defense13 were queried first; then
single edits before double edits, and exact support lexicographic order.
This order was saved before evaluation.

The run stopped immediately on its first LOSS at case40:38 DRAW,1 WIN,1 LOSS.
The remaining159 supports are explicitly preserved and unprocessed. No further
mutation, tuning, arity expansion or outcome table was started. The first36
completed supports lacked13; the actual failure retains13. This is not a
minimum-counterexample claim.

The witness's twelve first-pick children all have value WIN from the next
player's perspective. A pick x removes x and produces deficit x-1; because
x>=2>1, every root pick ends the turn. This describes optimal game values,
not a claim that every subsequent opponent choice wins.

Native CPU time through the stop was0.011892 seconds. Compilation, probe and
independent root/all-pick replay together took1.31 seconds. The15-second CPU
and30-second wall caps were not reached. No active job remains. Inputs were
checkpointed before compilation and the final checkpoint records the stop.

`results.json` contains all40 evaluated cases, the literal witness map and
159 unprocessed supports. `seeds.json` contains all deduplicated provenance
and rejected generation attempts. `probe.out` contains flushed native results.
Reproduce from the workspace root:

```sh
python3 research/catchup/campaign_2026_10_22/resume_01/two-guard-adaptive-mutation/run.py
```

This refutes the broad minimum-two/unit-deficit candidate computationally.
It does not refute the actual consecutive-tail eight-shadow statement or the
Catch-Up conjecture: the support is sparse and lacks counter3. The next useful
verification is a compact kernel certificate for this diagnostic, followed
by a revised mathematical decision that retains any additional actual-root
hypotheses. No such repaired invariant is asserted here.
