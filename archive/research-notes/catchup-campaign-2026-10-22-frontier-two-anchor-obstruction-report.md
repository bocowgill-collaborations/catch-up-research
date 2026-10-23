> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.TwoAnchorDoubleLossObstruction](../../CatchUp/TwoAnchorDoubleLossObstruction.lean), [CatchUp.WinningOpening](../../CatchUp/WinningOpening.lean).

# Certified sparse two-anchor double loss

Status: kernel certified; production gates passed; independent review requested.
The unrestricted auxiliary claim is FALSE. The interval target and actual
parent/high-shadow branch are NOT refuted.

## Explicit witness and proved claims

Let

    T = {18,33,35,36,52,56,62,74,100},
    E = {4,7} union T,
    C = {2,3,4,7} union T.

`CatchUp/TwoAnchorDoubleLossObstruction.lean` proves:

- T has nine distinct positive labels, every label at least 9, and even sum466.
- E has eleven counters and sum477; V(E,1)=LOSS and V(E,3)=LOSS.
- Every legal first pick loses at EACH of those two deficits, under optimal play.
- C has thirteen counters and sum482; V(C,8)=WIN.
- The universal assertion that even tails above the anchors exclude the
  simultaneous E1/E3 losses is false (`not_uniform_two_anchor_separation`).

These are normalized post-opening values, from the current mover's perspective,
connected by the existing executable/reference correctness theorem. They are
not single play outcomes or heuristic estimates.

The tail is sparse, not an interval. In particular, C is NOT a losing high8
shadow; it wins. Thus this is not a counterexample to anchor B, to the actual
root-specific w8 exclusion, to H, or to the original Catch-Up conjecture C.
It establishes that a proposed proof cannot discard those extra hypotheses
and rely only on the unrestricted two-anchor double-loss exclusion.

The independently replayed literal contexts also give C2 WIN and
V(C.erase2,4)=LOSS. Those two results are **experimental exact evidence only
in this deliverable**, not additional kernel-certified headline claims.
No general minimum-counterexample claim is made.

## Shared proof certificate and trust boundary

The fixed solver exported a proof DAG, serialized as ordinary JSON at
`search/root_anchor_jointloss_shrink_certificate7.json`. It contains 290 exact
normalized state records, 308 edges, and 145 leaves of at most seven counters.
The root records are E1=112, E3=222, and C8=290.

For each WIN node the data supplies one legal winning move. For each LOSS
node it supplies EVERY legal move. Each child has exactly the parent support
with the picked counter erased, and deficit |pick-oldDeficit|. Outcomes are
preserved on continuing picks and negated on catching/equality picks.
Full supports and exact natural deficits identify states; hash equality is
not used as mathematical equality.

The untrusted `generate.py` validates those elementary data properties and
renders a separate Lean theorem for every node, in strict child-before-parent
order. It does not assert any solver answer as an axiom. Nonleaf proofs reuse
existing exact minimax lemmas from WinningOpening and DeficitTwo; transition
equalities and all local branch obligations are kernel checked. Small leaves
use `Position.eval_eq_value` and ordinary `decide +kernel`. There are no DRAW
nodes on these selected W/L proof obligations, and no absent opponent branch
is treated as a draw.

The Lean source is the independently checkable proof certificate. Corrupting
the untrusted generator or JSON cannot bypass the kernel obligation that each
explicit state has its claimed value. Python validation separately rejects
missing LOSS branches, illegal WIN picks, and circular child references.
A deliberately altered Lean headline claiming E1 WIN instead of LOSS is also
rejected by Lean with a type mismatch; its failing source/log are retained as
`negative-control.lean` and `negative_control.log`.

This directly shares local minimax subproofs instead of expanding eleven-counter
factorial evaluation. No new checker framework, semantic axiom, or native proof
computation was introduced. Existing pinned certificate APIs were inspected;
porting their State/decoder infrastructure was unnecessary for this diagnostic.

## Verification and cost

Lean: v4.27.0. Mathlib: a3a10db0e9d66acbebf76c5e6a135066525ac900.
No heartbeat, recursion-depth, or kernel budget was increased.
Each Lean run had a 120-second hard timeout.

| Check | Result | Wall seconds |
|---|---|---:|
| Eight-counter LOSS pilot | PASS | 7.499 |
| Cutoff8 hardest-literal-leaf WIN pilot | PASS | 4.479 |
| Full generated source, warnings as errors | PASS | 63.569 |
| Strict scoped Lake build | PASS | 60.901 |
| Eight public transitive axiom audits and combined instance | PASS | 4.698 |
| Altered-outcome Lean negative control | REJECTED as required | 3.883 |

Every public theorem's axiom closure is exactly
`propext`, `Classical.choice`, `Quot.sound`. There is no sorry, custom axiom,
`Lean.trustCompiler`, native-only evaluation, or dependency on the unfinished
Catch-Up conjecture. The full fresh source check produced no warnings/errors.

The cutoff was lowered from8 to7 after the pilot to keep the full check bounded.
A first local template attempt lacked an explicit WinningOpening import for
its private recurrence lemma and failed with `unknown module CatchUp.WinningOpening`;
the direct import fixed it. This was a local assembly error, not a failed
mathematical candidate. The final source is free of placeholders.

Machine recorded: macOS26.6.2 arm64; hardware model unavailable. Largest
cumulative child RSS observed in production was 13,490,044,928 bytes; the fresh
source process separately recorded 12,510,773,248 bytes. These are process RSS
measurements, not aggregate memory or isolated peaks for every stage.

## Proof-size accounting

- Serialized JSON data: 135,720 bytes; 290 nodes, 308 edges, 145 leaves.
- Full generated Lean proof/source: 2,072 lines, 114,176 bytes.
- It contains 290 private shared state lemmas, three concrete set definitions,
  and eight public theorems, including all new supporting proof data.
- Compiled `.olean`: 1,713,472 bytes, including declaration/environment data;
  this is not a pure proof-term byte count.
- Untrusted generator: 7,999 bytes; generation took0.0104s, peak RSS13,680,640
  bytes, under the explicit30s/512MiB generation allowance.

The existing executable/reference equivalence and generic minimax lemmas remain
supporting dependencies; these figures do not claim to count all transitive
library mathematics. This is an upper bound exhibited by this proof, not a
shortest-certificate claim or a formal proof-size lower bound.

Frozen source SHA-256:
`93ed1e63c17b016d28a36a48b66a29771441e083947c31d7b552fd0fb27474b9`.
Serialized JSON SHA-256:
`bf56232f4cb111542c88fd98fb7b3831765fe0d5f42f787e9627899c3b1865b2`.
Compiled `.olean` SHA-256:
`0225ddd1255fa0b93e904b8660647f770c598f4e10ea6a696f030f667e3441d4`.
Logs, stage commands, generator checks, and hashes are retained in
`generation.json`, `verification.json`, and the adjacent logs.

## Reproduction

From `research/catchup`:

    python3 -B campaign_2026_10_22/frontier/two-anchor-obstruction/generate.py
    python3 -B campaign_2026_10_22/frontier/two-anchor-obstruction/verify.py --fresh

The first command renders the retained frozen JSON into the complete Lean
proof and checks generator corruption controls. The second freshly checks
that source, runs the strict target build, audits every public theorem, and
requires rejection of the altered-outcome control. Omitting `--fresh` reuses
the retained fresh-source record but still reruns build/audit/negative control;
that distinction is explicit in the verifier.

## Discovery evidence, separately from proof checking

Search and literal-replay artifacts are owned by the search worker, under
`search/root_anchor_jointloss_*`. The original witness and all first-pick maps
were independently literal-score replayed before certificate generation.
The authorized deletion test enumerated all512subsets of this fixed nine-label
tail and queried all256even-sum subsets. Only the full tail retained both losses.
Thus deletion compression within THIS fixed support failed. That is bounded
computational evidence, not global minimality or a kernel-certified exhaustive
classification of smaller arbitrary tails. Search cost is separate from the
Lean checking costs above; the fixed-state cutoff7 export took0.00137s and
visited11,287memoized slot states, according to its retained untrusted receipt.

## Highest-value next step

Retire the unrestricted E-only separation claim. Return to the actual w8
branch retaining its interval geometry and high-shadow/parent-loss hypotheses.
Those premises were discarded by the failed strengthening and are not met by
this witness. No new table or finite-cardinality ladder was started here.
