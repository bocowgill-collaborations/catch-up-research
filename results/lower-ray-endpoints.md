# Lower-ray endpoint results

Write `I_N={1,...,N}` and
`Q_N(b)=Position(I_N \ {1,b}, b−1)`. Values are from the current mover's
perspective. The [pair-deletion criterion](../CatchUp/PairDeletion.lean) needs
nonloss along the entire lower ray and a draw at the first-pair position
`P_N=Q_N(2)=Position({3,...,N},1)` to conclude the initial interval draws.

The following symbolic ports settle particular upper endpoints:

| Endpoint | Exact hypotheses and conclusion | Maintained source |
| --- | --- | --- |
| Top, b=N | N≥3 gives `value(Q_N(N))≠loss`, without parity. Already maintained before this batch. | [DeficitWinningBound](../CatchUp/Earlier/DeficitWinningBound.lean) |
| Penultimate, b=N−1 | N≥7 gives `value(Q_N(N−1))≠loss`, without parity or a smaller-instance hypothesis. | [LowerRayEndpoints](../CatchUp/LowerRayEndpoints.lean), [endpoint/trap guide](endpoint-trap-atlas.md) |
| Antepenultimate, b=N−2 | N≥7 and `value(afterOpening(I_(N−4),1))=draw` imply `value(Q_N(N−2))≠loss`. No parity premise. | [LowerRayAntepenultimateDescent](../CatchUp/LowerRayAntepenultimateDescent.lean) |
| Fourth from top, b=N−3 | Every N≥15 gives `value(Q_N(N−3))≠loss`, without parity or a smaller-instance hypothesis. Also holds for every even-triangular N≥11. | [LowerRayFourthEndpoint](../CatchUp/LowerRayFourthEndpoint.lean) |
| Fifth from top, b=N−4 | Every N≥23 gives `value(Q_N(N−4))≠loss`, without parity or a smaller-instance hypothesis. | [LowerRayFifthEndpoint](../CatchUp/LowerRayFifthEndpoint.lean), [proof guide](fifth-endpoint.md) |

The antepenultimate hypothesis is about the **specified opening one**. A draw
of the smaller tied root establishes that some opening draws; it does not
identify that opening as one. Each conclusion is nonloss at the displayed
intermediate position, not a draw or a result about all deleted counters.

## Antepenultimate descent

Suppose Q_N(N−2) loses. Its exact deficit N−3 remains available. The existing
winning-opening bound forces a losing post-opening position on
`I_N \ {1,N−3,N−2}` at a counter larger than N−3. Only N−1 and N remain.
Respond with the other one. The support becomes `I_(N−4) \ {1}` and the deficit
becomes one, exactly the assumed drawn smaller opening-one position.

If the residual opening is N−1, the reply N catches and switches players.
If it is N, the reply N−1 continues the same turn. The opening-order identity
handles their polarity; negating a draw is still a draw. The helper showing that
an available drawing move prevents loss explicitly rules out an impossible-catch
terminal state, so legality is not inferred from a total update alone.

## Fourth-from-top exact-sum exchanges

Put `m=N−5`. A hypothetical loss at Q_N(N−3) forces an upper opening on

```text
F(m,3) = [2,m] union {m+3,m+4,m+5}.
```

For m≥10, three structural theorems exclude these upper losses. At each step,
an available positive block sums exactly to the deficit. The already maintained
[exact-sum interface](../CatchUp/ExactSumResiduals.lean) reduces nonloss to every
residual opening above a chosen block member. The proof enumerates all permitted
openings, including lower intruders; terminal branches have no possible witness.

One boundary branch at m=10 needs a real completed turn. From remaining
`{2,3,6,7,15}` at deficit 9, take 2, then 6, then 15. The first two total 8<9;
the third is the first catch. The opponent receives `{3,7}` at deficit 14 and
cannot catch because its total is 10. Counter 6 is used only once.

Four small `decide +kernel` checks cover the first and middle upper openings
at m=6 and m=7; the last-opening theorem already applies. These supply N=11,12.
For 11≤N<15, the even-triangular hypothesis excludes 13 and 14. These are small
kernel evaluations, not native compilation or a large outcome-table replay.

## Provenance and remaining obligations

These are ports of earlier research, not new discoveries. The penultimate
endpoint has its own [source manifest and checks](../verification/endpoint-atlas-ports.md).
The antepenultimate and fourth-endpoint
[source manifest](../verification/endpoint-ports.json) records the unchanged
theorem statements and proof bodies, adapted imports/module references and removed
repository indexing attributes. The fourth-endpoint port reuses the generic
exact-sum lemma already extracted for the fifth endpoint. Its archived duplicate
is not redeclared. [Verification](../verification/endpoint-ports.md) separates
source reconstruction from Lean checking and transitive axiom audits.

Neither these endpoints nor the fixed four-tail forest gives a uniform descent
in upper-tail length. The full lower ray and both directions of the unbounded
first-pair draw remain open. The [current route guide](research-routes.md) and
[earlier findings](legacy-findings.md) retain those exact gaps.
