> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.AlternatingTailObstruction](../../CatchUp/AlternatingTailObstruction.lean), [CatchUp.NearDeficitGuardObstruction](../../CatchUp/NearDeficitGuardObstruction.lean).

# Diagnostic counterexample to the insertion bridge

The proposed bridge B says: if x belongs to C and sum(C)+x+1 is even, then
V(C,x+1) is NONLOSS. The relevant variant also requires minimum(C)>=3.

Both variants fail in the exact computation at

    C={4,7,13,19,36,37,50,57,60,99}, x=13, deficit14.

Here min(C)=4, sum(C)=382, and effective total396 is even. The game value is
LOSS; every one of its ten legal first picks has value LOSS. Frozen ExactSlots
and the independent literal-score evaluator agree on the root and all picks.
These are computational certificates/evidence, **not yet a Lean theorem**.

The structure directly matches the failed induction kernel. Choosing13 stays
with the same mover and reaches the already kernel-certified E1LOSS from
`CatchUp/AlternatingTailObstruction.lean`:

    E={4,7,19,36,37,50,57,60,99}, deficit1.

The remaining normalized children are:

| Pick | Child deficit | Same mover? | Child value |
| --- | --- | --- | --- |
| 4 | 10 | yes | LOSS |
| 7 | 7 | yes | LOSS |
| 13 | 1 | yes | LOSS |
| 19 | 5 | no | WIN |
| 36 | 22 | no | WIN |
| 37 | 23 | no | WIN |
| 50 | 36 | no | WIN |
| 57 | 43 | no | WIN |
| 60 | 46 | no | WIN |
| 99 | 85 | no | WIN |

Each child removes exactly its picked counter. Thus negation occurs only in
the seven catching moves. No single play sequence or alternating-turn
assumption substitutes for exact outcome optimization.

The experiment planned369 explicitly saved legal insertion queries, with no
outcome-preservation assumption. It stopped on the first LOSS after9 queries:
4 WIN,4 DRAW,1 LOSS;360 remain deliberately unprocessed. Old min3/min4 cases
already tested by the parent were excluded. No minimum-witness or exhausted
support-domain claim is made. The min2 controls were not reached.

The native solver used0.00065 CPU seconds through the stop; total compilation,
probe and independent witness replay took1.73 seconds. CPU30s/wall45s limits
were not reached. No active process remains. The original failed broad
bridge should be retired; this witness does not refute the minimum-two,
deficit-one candidate, the conditional G goal, or the interval Catch-Up
conjecture.

`results.json` preserves the full records, literal witness replay, timing,
frozen-evaluator hashes, and360 unprocessed queries. `seeds.json`, `input.txt`,
`probe.out` preserve exact ordering and every skipped case. Reproduce from
the workspace root:

```sh
python3 research/catchup/campaign_2026_10_22/resume_01/near-deficit-guard/run.py
```

The useful next verification is a compact Lean proof reusing the existing
E1LOSS theorem for pick13 and small checked subproofs for the other children.
No further search was run after finding the witness.
