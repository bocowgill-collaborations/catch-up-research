/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import CatchUp.Earlier.DeficitWinningBound
import CatchUp.Earlier.PartialCertificateSoundness

/-!
# A structural compression rule outside the full-DAG language

An available maximum equal to the protected mover's deficit guarantees nonloss.
This theorem-backed leaf performs no outcome lookup. It uses the existing partial
checker, so compressed node counts are not counts in the full-DAG model.
-/

namespace CatchUpSearch.CertificateComplexityCompression

open CatchUp CertificateChecker

/-- Recognize a protected turn whose deficit is an available maximum counter. -/
def maximumDeficitTarget (N : ℕ) (owner : Player) : TargetPredicate := fun state =>
  let p := toGamePosition N state
  decide (p.toMove = owner ∧ p.deficit ∈ p.remaining ∧ ∀ x ∈ p.remaining, x ≤ p.deficit)

/-- The compression rule is structural and sound independently of any solved table. -/
theorem maximum_deficit_target_sound (dag : StrategyDAG) :
    TargetSound (maximumDeficitTarget dag.gameSize dag.player) dag := by
  intro state _ htarget
  have h : (toGamePosition dag.gameSize state).toMove = dag.player ∧
      (toGamePosition dag.gameSize state).deficit ∈ (toGamePosition dag.gameSize state).remaining ∧
      ∀ x ∈ (toGamePosition dag.gameSize state).remaining,
        x ≤ (toGamePosition dag.gameSize state).deficit := by
    exact of_decide_eq_true htarget
  rw [can_avoid_loss_iff_value, if_pos h.1]
  exact Position.value_ne_loss_of_deficit_is_max _ _ h.2.1 h.2.2

/-- The ordinary partial checker validates every branch and uses only the proved shortcut. -/
theorem compressed_certificate_sound (dag : StrategyDAG)
    (hcheck : checkPartialCertificate (maximumDeficitTarget dag.gameSize dag.player) dag = true) :
    CanAvoidLoss dag.player (toGamePosition dag.gameSize dag.root) :=
  check_partial_certificate_sound _ dag (maximum_deficit_target_sound dag) hcheck

open Lean Elab Command in
run_cmd do
  for declaration in #[``maximum_deficit_target_sound, ``compressed_certificate_sound] do
    let actual ← Lean.collectAxioms declaration
    for axiomName in actual do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom in {declaration}: {axiomName}"
    logInfo m!"Verified axioms for {declaration}: {actual}"

end CatchUpSearch.CertificateComplexityCompression
