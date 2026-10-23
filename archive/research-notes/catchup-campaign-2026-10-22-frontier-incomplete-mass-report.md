> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.IncompleteSubsumMass](../../CatchUp/IncompleteSubsumMass.lean).

# Missing subset-sum mass bound

Verified result: for a finite set `A` of distinct positive naturals, if some target at most `A.sum id` is not a subset sum, then

```
A.card * (A.card + 1) + 2 * A.card <= 2 * A.sum id + 2.
```

Source: `CatchUp/IncompleteSubsumMass.lean`, namespace `CatchUp.IncompleteSubsumMass`.

The public theorem `missing_target_mass` permits any target `t <= A.sum id`. Missing zero or the total is impossible, so the hypotheses include the desired positive interior gaps without a separate positivity assumption on `t`. No cardinality lower bound is imposed; empty and singleton cases are covered.

The public corollary `missing_target_card_bound` adds `A.sum id <= A.card + c + 1` and concludes

```
A.card * (A.card + 1) <= 2 * c + 4.
```

For an exact block `B` with maximum `b`, setting `A = B.erase b` and `A.card = k - 1` gives the intended bound `k * (k - 1) <= 2 * c + 4`, once the game-specific mass and missing-target hypotheses are supplied. This module does not claim a game outcome or prove that strategic application.

## Proof

Choose a subset `P` of maximal cardinality whose subset sums cover every number from zero through `P.sum id`. Inserting a new element at most `P.sum id + 1` preserves this coverage. Thus every element outside `P` is at least `P.sum id + 2`. The complement is nonempty because `A` is incomplete. Its cardinality and shifted mass give a strengthened triangular lower bound, using the existing `DenseTerminalReduction.interval_subset_sum_lower`. Combining this bound with the triangular mass of `P` gives the result. The arithmetic lemma explicitly handles prefix cardinalities zero and one before the general polynomial argument.

There are 138 new source lines (6,254 bytes), one private definition, six private supporting theorems, and two public theorems. This accounting includes the supporting mathematics rather than only the public theorem invocations. No finite game search, external solver, custom axiom, native computation, or sorry is used.

## Verification

Pinned package: Lean `leanprover/lean4:v4.27.0`; Mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900`.

Reproduce from `research/catchup`:

```
python3 -B campaign_2026_10_22/frontier/incomplete-mass/verify.py
```

All three bounded stages passed with exit code zero:

| Check | Wall seconds |
|---|---:|
| `lake --wfail build CatchUp.IncompleteSubsumMass` | 2.200 |
| Fresh source elaboration with warnings as errors | 4.131 |
| Public axiom audit and small hypothesis examples | 4.186 |

The final build replay was cached; the earlier uncached target compilation reported 3.6 seconds. The fresh source check re-elaborated the proof. Both public theorem axiom closures are exactly `propext`, `Classical.choice`, and `Quot.sound`. Audit examples cover the empty-set impossibility and missing targets for `{2}` and `{1,3}`, using ordinary kernel `decide` for finite hypotheses.

Platform recorded by the verifier: `macOS-26.6.2-arm64-arm-64bit`, architecture `arm64`. Maximum child RSS observed during the replay process was 5,339,119,616 bytes. Python's resource measurement is cumulative across subprocess stages; it is not an independent per-stage peak. Hardware model information was unavailable within the sandbox.

Source SHA-256: `dbc349e05e21cc5e92a4fc3864fa0283cb924f72def3a7e6ec19f4e954570053`.

Logs and hashes are retained in `verification.json`, `build.log`, `source.log`, and `axioms.log`. An initial measurement wrapper using `/usr/bin/time -l` completed the build but returned failure when its resource query hit a sandbox-denied `sysctl`; that wrapper log is preserved as `measurement-failure.log`. The Python resource wrapper then reran all checks successfully.

Independent read-only mathematical review returned PASS with no statement-fidelity or proof blocker; see `REVIEW.md`.

## Remaining obligation

Apply `missing_target_card_bound` to the maximal exact block's tail, using the existing true-gap theorem and the game-specific upper mass bound. This provides a uniform block-cardinality restriction for every residual cardinality. It does not by itself close the remaining nonterminal defense.
