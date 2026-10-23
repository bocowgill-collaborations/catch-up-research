> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.IntervalSuccessorReplyObstruction](../../CatchUp/IntervalSuccessorReplyObstruction.lean).

The fixed reply policy is false within the authorized six interval supports. All 51 policy outcomes were computed by unchanged ExactSlots and independently replayed with literal scores. For the 42 target endpoints with N >= 15, there are 5 LOSS, 35 DRAW and 2 WIN policy outcomes.

Scope: N in {11,12,15,16,19,20}; F={7} union [9,N]; y ranges over every element of F; endpoint S=F\{y}, deficit d=y-3. The policy is a=9 for y=7, a=y+1 for 9<=y<N, and a=N-1 for y=N. Every a belongs to S and is greater than d, so its outcome for the original player is -V(S\{a},a-d). Child deficits are respectively 5, 4 and 2. The 51 endpoints are exactly the previous frozen root_interval_four_results.json domain. No new support, N, table or policy repair was tested.

| N | Endpoints | Policy WIN | DRAW | LOSS | Failing y |
|---|---:|---:|---:|---:|---|
| 11 | 4 | 2 | 2 | 0 | none |
| 12 | 5 | 0 | 1 | 4 | 7,9,11,12 |
| 15 | 8 | 2 | 5 | 1 | 11 |
| 16 | 9 | 0 | 5 | 4 | 7,11,13,16 |
| 19 | 12 | 0 | 12 | 0 | none |
| 20 | 13 | 0 | 13 | 0 | none |
| Total | 51 | 4 | 38 | 9 | |

Smallest target failure, ordered by (N,y): N=15,y=11, S={7,9,10,12,13,14,15}, d=8. The endpoint value is DRAW. Policy a=12 leaves {7,9,10,13,14,15} at opponent deficit 4 with value WIN, hence the policy move is LOSS. The complete friendly first-pick map is 7:DRAW, 9:DRAW, 10:DRAW, 12:LOSS, 13:DRAW, 14:LOSS, 15:DRAW. Safe alternatives are {7,9,10,13,15}. All seven first-pick outcomes and the six-counter policy child were independently replayed literally.

The known N=12 initial first4 failure is retained separately: E1=DRAW, F3=WIN, first4=LOSS. Its y=7 and y=9 endpoints are already LOSS regardless of reply; y=11 and y=12 are WIN endpoints at which this policy also chooses LOSS. This baseline does not account for the new N>=15 failures.

All failing endpoints retain complete friendly first-pick maps and safe alternatives in root_interval_lead4_results.json. Every one of those 55 first-pick values was independently replayed. Every policy outcome was replayed twice: the normalized opponent child absolute(S\{a},0,a-d), and the actual-score original outcome -absolute(S\{a},1+y,4+a), with same-player consecutive picks handled by verify.absolute. Thus 51 policy outcomes, 102 score-form checks, and 55 failing-endpoint first-pick checks completed; no missing, skipped or resource-limited case remains.

The fixed N=16 controls also passed literal replay. For y=9, policy10 leaves K={7,11,12,13,14,15,16} at deficit4 with value DRAW. For y=10, the copying-down control9 leaves exactly K at deficit2 with value WIN, so that move loses. The primary y=10 policy11 instead leaves {7,9,12,13,14,15,16} at deficit4 and draws. These are distinct deficits and, for primary11, distinct support; no invariant was assumed.

Commands, command hashes, output hashes and wall times are retained in root_interval_lead4_run.json. Compile took 0.666407625 s, native probe 0.415136 s, literal replay 1.006973542 s (2.088517167 s total). Peak recorded compiler RSS was 140017664 bytes; probe internal peak RSS 1802240 bytes; literal replay peak RSS 18759680 bytes. These remain below the 30-second/512-MiB bounds. The native probe used at most 12 endpoint labels and 11 policy-child labels, with actual magnitudes <=20; no interval table was built.

The final metadata audit verified every hash in root_interval_four_manifest.json, including frozen slots.hpp and verify.py, unchanged. This receipt refutes only the specified concrete reply policy. It supplies no uniform interval theorem and no B, Q_N or C counterexample claim. The separate Lean certification of the smallest policy failure is outside this computational receipt.
