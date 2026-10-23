> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current results guide](../../results/README.md).

# One unpaired arbitrary-tail anchor discriminator

All **512 planned anchor states completed**, with no LOSS, skipped case, or resource-limited case. This leaves the stronger generic anchor candidates unrefuted by this single batch; it is finite evidence, not a uniform anchor/reflection proof or an actual interval-root Q_N/C result. No additional batch was started.

| Family | Completed supports | LOSS | DRAW | WIN | Tail cardinalities |
|---|---:|---:|---:|---:|---|
| A: `({2,3,4}∪T,7)` | 256 | 0 | 35 | 221 | 1..11 |
| B: `({2,3,4,7}∪T,8)` | 256 | 0 | 28 | 228 | 1..10 |

Every tail is explicit, has even sum, consists of distinct labels with min≥8 for A or min≥9 for B and max≤1000, and **cannot be partitioned into adjacent pairs**. Some contain clusters/adjacencies deliberately; they are not the all-paired geometry of the previous batch. Both odd and even cardinalities occur. The batch combines fixed scattered/cluster supports, deterministic uniform and multiscale supports, clusters with outliers, nonlinear separation, and transformed prior root-loss geometries. Generator seeds are20261022/20261023. The saved explicit list is authoritative; no random or statistical conclusion is asserted.

The unchanged ExactSlots solver retains actual labels and its14-label bound. A has at most11 tail+3 anchor labels, B at most10+4. It stops on the first anchor LOSS or an8s internal probe cap; neither occurred. All512 cases completed in saved order `(tail cardinality,max label,tail sum,lexT,family)`. No interval table was built, and no solver limit was extended.

Three prior even root-loss geometries were included without any outcome-preservation assumption:

- Complete set `{1,2,3,7,14,23,37,68,101,111,123}`, total490, from pinned `bb10b824:CATCHUP_CAMPAIGN_20260808_2206_ET.md:2205–2217`. A uses the whole support shifted+8 and a second scaled/shifted version. B explicitly deletes even counter2 before embedding, to respect its10-tail-label limit. The two A embeddings are WIN; both B embeddings DRAW under ExactSlots.
- `{2,5,6,9,11,13}`, total46, same pinned report:1329–1333. Shift+6 for A and+8 for B makes admissible new tails. Both anchored states DRAW.
- `{9,16,17,18,26,28,31,37}`, total182, from pinned `CATCHUP_SHIFTED_CYCLE_REPORT_20260928_1021_ET.md:99–120`. The unchanged tail already fits both families; both anchored states WIN. Fixed translated/scaled versions are also in the explicit list, including separated labels through740.

Independent literal-score controls confirmed **all three original source supports are tied root LOSS**, with every opening value saved. This confirms the prior geometry but does not transfer its outcome to an anchored game. Four fixed anchored controls—the six-label and unchanged eight-label geometries in each family—also had their shadow values, conditional targets, and all initial picks replayed literally. These controls give13 direct literal queries plus their first-move checks. The full512 primary values were not all literally replayed. Because no anchor LOSS occurs, there is no failing-anchor minimax/reply set to certify, and the conditional reflection antecedents remain absent.

`root_anchor_unpaired_seeds.json`/`.txt` preserve every planned support and provenance. `root_anchor_unpaired_results.json` retains all512 values, family/cardinality counts, literal source/anchor controls, and exact completion status. `root_anchor_unpaired_checkpoint.json` records completed IDs1..512 and no unprocessed IDs; `root_anchor_unpaired_remaining_seeds.txt` is empty. The executable accepts a saved first-ID argument if a future separately authorized resume is needed. No automatic resume is scheduled.

Exact commands/output hashes/resources are in `root_anchor_unpaired_run.json`; the manifest hashes all new artifacts and frozen sources. The original and held-out `root_reentry_reflection_*` manifests and every listed original receipt were separately verified unchanged. No source or file outside the new prefix was edited.

Compile0.641s, probe0.826s externally (internal0.053s;1,009,277 explicit-slot states visited), fixed literal audit0.401s; combined1.868s, plus0.003s internal seed preparation. Peak compiler RSS141,934,592 bytes, probe278,364,160 bytes, literal29,081,600 bytes. Both time and memory remain below30s/512MiB. The higher probe RSS comes from the unchanged explicit-cache allocations across varied magnitudes, not a new interval table.
