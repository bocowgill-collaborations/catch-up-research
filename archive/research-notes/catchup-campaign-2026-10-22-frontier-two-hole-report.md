> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.TwoHoleTopBoundary](../../CatchUp/TwoHoleTopBoundary.lean).

# Two-hole top boundary: conditional reduction

This result repackages the existing exact-block, dense exact-deficit, and
winning-opening APIs. It is not a new density closure mechanism.
The only production addition is `CatchUp/TwoHoleTopBoundary.lean`, importing
`DenseLossGeneral`. No earlier source was edited.

For d>=5, S contained in [1,d], and at most two missing counters:

* `loss_forces_exceptional_opening` proves that a loss at deficit d forces
  `S=[2,d-1]` and makes opening1 of `[1,d-2]` losing for its opponent.
* `loss_forces_smaller_win` therefore proves the smaller complete interval
  `[1,d-2]` winning.
* `nonloss_of_smaller_nonwin` proves the requested conditional result:
  if `[1,d-2]` is not winning, then `(S,d)` is nonlosing.
* `loss_forces_smaller_even_win` adds the optional parity statement. If
  `sum(S)+d` is even, the smaller triangular sum `(d-2)*(d-1)/2` is even.

These are necessary conditions on a hypothetical loss. No converse from
a smaller winning root to a loss in the exceptional support is claimed.
The smaller-root condition remains a hypothesis in the nonloss theorem.

The proof uses `DenseLossGeneral.exact_deficit_nonloss` for an available1,
and `Position.value_ne_loss_of_exact_sum_block_dominates` for an available d.
A loss thus misses both1 and d. They exhaust the two-hole budget, forcing
exactly `[2,d-1]`. The legal pick d-1 is strictly smaller than deficit d,
so the preserved continuing-pick lemma gives a loss at deficit1, with
remaining support `[2,d-2]`. This is exactly the post-opening1 state of
the smaller interval. `value_eq_win_iff_exists_winning_opening` supplies
its winning root value.

The exact-block and winning-opening facts come from the adapted, preserved
other-repo proofs at commit `bb10b824`; their hashes and minimal import
transformations are recorded in `../second-provenance.json`. The two-hole
packaging does not duplicate those proof bodies. `ParityProbe.lean` retains
the separately checked elementary arithmetic proof, which was copied into
the module without importing campaign scratch files.

From `research/catchup`, reproduce with:

```
lake --wfail build CatchUp.TwoHoleTopBoundary
lake env lean campaign_2026_10_22/frontier/two-hole/audit.lean
```

`build.log` and `axioms.log` retain the final checks. Six transitive axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`. There
is no `sorry`, native proof evaluation, custom axiom, unsafe definition,
or budget override. `source-check.json` records bytes, lines, theorem count,
hash, and verification of the four prior finished source hashes. The
parent owns independent game tests and final review. Neither H nor C is
proved or refuted.
