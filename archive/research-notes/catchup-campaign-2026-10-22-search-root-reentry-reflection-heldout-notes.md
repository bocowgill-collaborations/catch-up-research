> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current results guide](../../results/README.md).

# Held-out direct anchor nonloss test

The single held-out batch found **zero anchor losses in 202 states**. Every result was independently replayed with literal scores. This tests the stronger direct NONLOSS candidate on explicit supports; it is distinct from the original reflection-domain test whose implications were vacuous. No uniform theorem or actual root Q_N/C conclusion follows.

Each family has exactly101 supports:

- 28 unions of two adjacent pairs and70 unions of four adjacent pairs, using distinct starts from A-bank `{8,10,12,18,20,30,40,80}`. Each pair is `{s,s+1}`; all chosen pairs are disjoint, including adjacent starts8 and10. These tails have4 or8 labels and even sum.
- Two supplied advice supports: `{8,9,12,13,22,23,42,43}` and `{8,9,14,15,20,21,42,43}`.
- The supplied fixed scattered control `{18,28,34,40,58,68}`.

A uses these exact tails with `U={2,3,4}∪T`, shadow deficit7 and reflection target3. B translates **every** tail above by+2, with `U={2,3,4,7}∪T`, shadow deficit8, targets2 and `(U.erase2,4)`. Thus B-bank starts are `{10,12,14,20,22,32,42,82}`; B-advice tails are `{10,11,14,15,24,25,44,45}` and `{10,11,16,17,22,23,44,45}`; B-scattered is `{20,30,36,42,60,70}`. All actual magnitudes are preserved, with maximum label83 and at most12 supplied labels per state. All202 tails are even-sum and meet their respective lower bounds.

| Family | Direct anchor LOSS | DRAW | WIN | First reflection target | Erased-2 target |
|---|---:|---:|---:|---|---|
| A, 101 supports | 0 | 88 | 13 | 101 DRAW | — |
| B, 101 supports | 0 | 20 | 81 | 101 DRAW | 78 DRAW,23 WIN |

All505 direct queries were independently evaluated by the frozen literal-score recurrence:202 anchor shadows,202 first reflection targets,101 erased-2 targets. Every value matched the unmodified frozen ExactSlots solver. Literal caches were cleared after each query, and checkpoints were saved every20 cases. Because no anchor LOSS occurs, the conditional reflections again have zero nonvacuous instances. There is no failing-shadow first-pick set to replay; the positive replay scope is complete state-value verification, not a general strategy certificate.

The precise support list and translations are in `root_reentry_reflection_heldout_seeds.json`. `root_reentry_reflection_heldout_results.json` retains all202 cases, all505 literal-query records, value counts and complete verification flags. Exact command arrays/output hashes and resource receipts are in the separate held-out run JSON. Its manifest hashes only new held-out artifacts plus frozen sources and the original manifest. The original `root_reentry_reflection_manifest.json` and every file it lists were rehashed unchanged; original results, notes and receipts were not overwritten.

No interval table or extra support batch was built. This batch used only unchanged `seven_pairs/slots.hpp` on7/8/9/10/11/12-label supports, plus independent `verify.absolute`. Compile0.599s, probe0.554s (internal0.041s;1,316,813 explicit-slot states visited), literal replay23.842s; total24.995s. Peak compiler RSS141,901,824 bytes, probe2,375,680 bytes, literal45,940,736 bytes. Every job and the combined batch stayed below30s/512MiB. No further experiment was started.
