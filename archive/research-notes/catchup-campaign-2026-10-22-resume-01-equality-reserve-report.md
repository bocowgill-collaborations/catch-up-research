> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.EqualityReserveObstruction](../../CatchUp/EqualityReserveObstruction.lean).

# Equality excludes every reserve-containing repair turn

Informal statement: b,c>0, b∉C, and V(C,b+c)=LOSS. An arbitrary legal whole
turnY from(insertbC,c) avoidsb and totalsb+c. At the resulting actual position
(insertb(C\Y),b), EVERY legal completed repair turnZ containingb leaves WIN
to the opponent. Its whole-turn outcome for the repair mover is therefore LOSS.
This covers arbitrary numbers of counters inC,Y,Z; it is not a finite test or
an assertion about only the immediate pickb.

The new corollary gives a complete pruning criterion: this equality endpoint
is NONLOSS iff it has a legal completed-turn witness avoidingb and leaving a
nonwinning endpoint. The actual endpoint can still draw or win through such
a b-avoiding turn. The theorem does not claim it loses, and does not exclude
usingb on a later turn after a different initial repair.

## Exact statements

```lean
theorem repair_endpoint_win
    (C Y Z : Finset ℕ) (b c final repairFinal : ℕ) (hbpos : 0 < b) (hcpos : 0 < c)
    (hb : b ∉ C) (hloss : (⟨C, b + c⟩ : Position).value = .loss)
    (turn : TurnSet ⟨⟨insert b C, c⟩, .p1⟩ Y final)
    (hbY : b ∉ Y) (heq : Y.sum (fun x ↦ x) = b + c)
    (repair : TurnSet ⟨⟨insert b (C \ Y), b⟩, .p1⟩ Z repairFinal) (hbZ : b ∈ Z) :
    (completedTurnEndpoint ⟨⟨insert b (C \ Y), b⟩, .p1⟩ Z).toPosition.value = .win
```

```lean
theorem nonloss_iff_avoiding_reserve
    (C Y : Finset ℕ) (b c final : ℕ) (hbpos : 0 < b) (hcpos : 0 < c)
    (hb : b ∉ C) (hloss : (⟨C, b + c⟩ : Position).value = .loss)
    (turn : TurnSet ⟨⟨insert b C, c⟩, .p1⟩ Y final)
    (hbY : b ∉ Y) (heq : Y.sum (fun x ↦ x) = b + c) :
    (⟨insert b (C \ Y), b⟩ : Position).value ≠ .loss ↔
      ∃ Z repairFinal, TurnSet ⟨⟨insert b (C \ Y), b⟩, .p1⟩ Z repairFinal ∧
        b ∉ Z ∧
        (completedTurnEndpoint ⟨⟨insert b (C \ Y), b⟩, .p1⟩ Z).toPosition.value ≠ .win
```

The authoritative module is `CatchUp/EqualityReserveObstruction.lean`.
`equality_endpoint_eq` identifies the actual endpoint of the first opponent
turn using the existing PairEntranceShadow endpoint equality.
`repair_turn_loses` states the endpoint value negated back to the repair mover
is LOSS. No paper/manuscript was edited.

## Proof and edge conditions

A legal repair turn containingb must finish withb. Ifb were in its preparation,
that preparation would already have sum>=b, contradicting the strict turn
condition. This is formalized by `reserve_is_final` without any cardinality
restriction. Write K=Z.eraseb. Then K⊆C\Y and sumK<b; singleton repairs use
b>0 to include the empty preparation case.

Letf be the original final counter ofY. Its preparation has sum<c, including
singletonY because c>0. SetsY andK are disjoint. ConsequentlyY∪K is a legal
shadow turn at deficitb+c with finalf: its preparation sum is the sum of the
old preparation andsumK, strictly belowc+b, and its total isb+c+sumK.
The existing `PairEntranceShadow.turn_endpoint_win_of_loss` therefore makes
its endpoint WIN. The actual repair endpoint is exactly the same normalized
position: remainingC\(Y∪K), deficitsumK. This proves the obstruction.

The proof permits arbitrary natural labels inC; explicit positivity is needed
only for b,c in the displayed theorem. Positive-counter Catch-Up is covered.
No c<b, interval geometry, parity, density, monotonicity, tied-root nonloss,
unit-guard insertion, or pair-parity hypothesis is used. All possible legal
repair turns are quantified, not one chosen principal variation.

For `nonloss_iff_avoiding_reserve`, availableb makes the actual state nonempty
and catchable. The existing `Position.value_ne_loss_iff_exists_turn_set` supplies
a whole-turn witness exactly when the state is nonlosing. A witness containingb
would have the just-proved WIN endpoint and contradict its required nonwinning
endpoint. The converse simply forgets the additional avoidance condition.

## Verification and reproduction

From `research/catchup`:

```
lake env lean -DwarningAsError=true -o .lake/build/lib/lean/CatchUp/EqualityReserveObstruction.olean CatchUp/EqualityReserveObstruction.lean
lake --wfail build CatchUp.EqualityReserveObstruction
lake env lean -DwarningAsError=true campaign_2026_10_22/resume_01/equality-reserve/audit.lean
lake env lean -DwarningAsError=true campaign_2026_10_22/resume_01/equality-reserve/lean/Main.lean
```

All passed under120-second per-command caps. Fresh source5.282seconds;
warning-strict build6.913seconds;5transitive axiom audits4.780seconds;
import shim4.526seconds. Every audit contains only propext,Classical.choice,
Quot.sound. Source scan found no live placeholder proof token. No external
solver, native-only computation, custom desired-result axiom, or unfinished
conjecture occurs in the proof. Source search found no duplicate all-turn
reserve obstruction; the prior PairEntranceShadow equality result concerned
the immediate reserve pick.

Lean4.27.0/mathliba3a10db0e9d66acbebf76c5e6a135066525ac900 were checked
and preserved. PlatformmacOS26.6.2arm64; exact CPU model is unavailable.
Darwin cumulative child peakRSS across the command sequence5,459,705,856bytes
is recorded without claiming isolated per-theorem memory. Interactive proof
generation was not separately timed; no search job ran.

New source6876bytes/152lines,5public theorems,SHA256
`9c695341d699bf698575b2f24af4ce51d32a383e31dfdafd807eaa96de964b2c`.
The9-file local source import closure totals115603bytes, including108727bytes
of previously existing support; Mathlib is separately pinned and excluded
from the local byte count. These are source measurements, not serialized
kernel-term sizes or proof-size minimality claims. `checks.json` records
commands/timing/pins and preservation of the five earlier owned proof sources;
`dependencies.json` records local dependency hashes. The lean/ directory has
the required pinned path-dependency wrapper/import shim; the existing package
is the authoritative verification target.

Parent preliminary mathematical review approved the union-shadow argument;
final independent fresh replay/source review remains the parent's gate.
No C,H,or complete strategy claim is made. No further research or theorem
expansion will be performed by this workstream after this bounded task.
