> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.FivePair](../../CatchUp/FivePair.lean).

This milestone proves the recommended size-fifteen reserve step. For each
`i : Fin 6`, delete the actual pair `{4+2*i,5+2*i}` from `[4,15]`. The resulting
five-pair position is nonwinning at both deficit one and deficit three.
The assembled strategy proves

```lean
CatchUp.FivePair.interval_fifteen_nonwin :
  Position.value ⟨Finset.Icc 4 15,2⟩ ≠ .win

CatchUp.FivePair.first_pair_fifteen_nonloss :
  Position.value ⟨Finset.Icc 3 15,1⟩ ≠ .loss
```

The second statement chooses `3` and uses the first. It provides one nonloss
direction in the first-pair subproblem. Neither statement establishes a draw
there or the original initial-game conjecture. The underlying deficit-two
position is a reachable state after the legal picks `1,2,3`, as proved in the
previous module. This is a finite `N=15` family, not a theorem about arbitrary
five-pair supports or interval lengths.

The proof covers every opposing counter choice. Pair mates normally suffice:
in the initial deficit-two position they leave one of the five-pair reserves
at deficit one or three; in a reserve they leave four pairs at deficit zero,
two, or four. Pair deletion is equality of remaining sets, not a relabeling
symmetry. Actual counter magnitudes and the catch/continue rule are retained.

There are exactly two diagnosed failures of the second-round mate rule.
With `{6,7}` absent, after the opponent chooses `12` at deficit three, replying
`13` loses. Instead take `4` and then `8` on the same turn. With `{12,13}` absent,
after `6` at deficit three, replying `7` loses; take `4` instead. The losing mate
replies both expose the same winning state
`({4,5,8,9,10,11,14,15},4)`. Its win by choosing `8`, both failed mate replies,
and both safe repairs are kernel checked. These refute the unconditional mate
policy, not the Catch-Up conjecture or the deficit-two interval claim.

The proof shares its smaller obligations. Deficit-two leaves reuse the existing
symbolic four-pair theorem. Fifteen tied four-pair supports use the existing
draw-opening theorem: opening `11` when the two smallest pairs are absent,
`7` when `{4,5}` is absent but `{6,7}` is present, and `5` otherwise suffices. Only the
seven-counter post-opening position is computed. Fourteen deficit-four leaves
check the defender's nonloss directly; the one excluded support receives the
explicit repairs. The new source includes all of this supporting mathematics.
It does not hide the finite leaf computations behind a claimed uniform rule.

Kernel replay comprises fifteen seven-counter draw-opening checks, fourteen
eight-counter defender checks, two adaptive-repair leaves, and one smaller
winning-obstruction regression. Finite set identities are also checked.
An initial bulk full-outcome approach hit 200,000 heartbeats. A raised-limit
attempt was manually interrupted without an accepted result. The completed
proof avoids that approach using shared leaves, the draw-opening reduction,
and one-player safety checks. No timeout was treated as a draw or other result.

The independent policy test checks all 132 first/second-round reply obligations
against the separate absolute-score recurrence. It then expands the assembled
strategy below the certified leaves, selecting exact safe witnesses on friendly
nodes and covering every opposing edge: 3,124 distinct states, 2,966 opponent
edges, and 1,307 continuing-player edges. The two bad mate responses are rejected.
The experimental exact evaluator finds draws in all twelve reserves; the main
Lean theorem deliberately claims only the nonwinning guarantee it proves.
The fallback witness policy and experimental outcome values are not proof premises.

Bounded discovery also checked 3,003 disjoint five-pair shapes with starts in
`4..22`: all were nonwinning at deficits one and three. This is evidence for
an unbounded investigation, not a proof. `deficit_four_obstructions.json`
preserves the failed broader deficit-four invariant and its exact sparse
counterexamples; it rules out blindly extending the same mate argument to
arbitrary gaps.

Reproduce from the downstream package directory:

```sh
python3 five_pair/verify.py
```

The verifier checks the existing source hashes, pinned Lean 4.27.0 and Mathlib
commit, warning-strict build, fresh replay of every new proof module including
the shared leaves, fourteen transitive axiom reports, and the adversarial policy
tests. Every process group has a 120-second limit. Only `propext`,
`Classical.choice`, and `Quot.sound` occur in the audited axiom closures.
An independent reviewer also audited the all-counter quantifiers, continuation
thresholds, smaller-leaf dependencies, and finite scope, and independently
replayed the axiom-audit file successfully.

`benchmark.json` records all new proof/support sources, derived compiled sizes,
reused supporting sources separately, checking times, identified machine
information, and scoped peak child memory. Proof discovery and checking are
reported separately. This is an explicit upper bound on the size and cost of
this finite proof, with no minimality claim. No binary Turing-machine work or
new machine equivalence is supplied by this milestone; the earlier high-level
search equivalence remains unchanged.

The next useful structural target is nonwinning of tied **four arbitrary
adjacent pairs** with minimum at least four. Replacing the finite tied-leaf
table with that theorem would remove the principal finite-pool restriction
from the deficit-one five-pair reserve argument. The deficit-three extension
must separately handle the broader deficit-four obstructions already saved.

Final measured replay: 47.2 seconds for the shared leaves, 7.2 seconds for the
main proof, and 4.7 seconds for the regressions, on macOS arm64 with 16 logical
CPUs. Maximum individual child RSS during verification was 6.81 GB, including
Mathlib loading. New proof/support source totals 15,924 bytes (23 theorems);
reused supporting source totals 168,253 bytes. Derived compiled modules total
3,118,512 bytes. These sizes are documented separately, not conflated.
