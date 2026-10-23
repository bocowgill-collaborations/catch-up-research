> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.DeficitCrossing](../../CatchUp/DeficitCrossing.lean).

# Legal midpoint turns exclude double loss

For arbitrary finite Nat support S and a legal lower-deficit completed turn Y,
write y=sumY. If y<d and d+e=2y, then V(S,d)=LOSS implies V(S,e)!=LOSS.
No density, parity, positivity, bounded support/cardinality, or tail assumptions.
Zero/terminal high shadows are included through the existing terminal-safe
loss-after-subsum theorem.

Mechanism: the chosen set is a compulsory continuing prefix at d, leaving
(S\Y,d-y) LOSS. If e also loses, its legal completed turn forces
(S\Y,y-e) WIN for the next mover. The two deficits coincide by the midpoint
identity. This is an outcome/perspective argument, not score-margin optimization.

The concrete corollary needs only 2,3 in S:
V(S,7)=LOSS -> V(S,3)!=LOSS, using the legal turn [2,3]. It does not prove
unconditional anchor nonloss or a general deficit monotonicity statement.
The actual consumer RootUpperReentry eliminates residual opening7 from a
hypothetical losing interval parent uniformly in N.

Both proofs were developed with one-tactic LeanProbe checking. An intermediate
small numeral proof failed because erase simplification remained open; the final
source explicitly closes the numeral assertion with ordinary kernel decide.
No unfinished intermediate source is an accepted artifact.

Production strict target build, fresh warning-strict source check and both
public transitive axiom audits passed; only propext, Classical.choice, Quot.sound.
No native reduction, custom axiom or unfinished upstream theorem. Independent
source review PASS in REVIEW.md. checks.json/fresh-source.json retain commands,
output hashes, times, and cumulative child RSS on macOS26.6.2 arm64. metrics.json
records full source and local supporting-source closure plus .olean sizes.
These exclude complete transitive Mathlib/proof-term size and imply no minimality.

Reproduce from research/catchup:
```
lake --wfail build CatchUp.DeficitCrossing
lake env lean -DwarningAsError=true CatchUp/DeficitCrossing.lean
lake env lean -DwarningAsError=true campaign_2026_10_22/frontier/deficit-crossing/audit.lean
```

Existing components supply most of the proof; the new result packages their
crossing mechanism into a reusable quantified theorem. A narrow independent
search found no identical assembled prior statement, not a global novelty claim.
