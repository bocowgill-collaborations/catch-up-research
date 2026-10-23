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

import CatchUp.Reference

/-!
# An executable classifier for one-sided Catch-Up safety

This module gives a small Boolean recurrence that follows the proof-level definition of
`CatchUp.CanAvoidLoss`. Its soundness theorem lets finite research tools select safe positions
without trusting annotations from the exact solver.
-/

namespace CatchUpSearch.CanAvoidLossClassifier

open CatchUp

/-- Executably decide whether a fixed player can avoid losing from a post-opening position. -/
def check (player : Player) (position : GamePosition) : Bool :=
  if position.IsTerminal then
    decide (position.terminalOutcomeFor player ≠ .loss)
  else if position.toMove = player then
    position.remaining.attach.fold (· || ·) false fun counter =>
      check player (position.afterPick counter.1)
  else
    position.remaining.attach.fold (· && ·) true fun counter =>
      check player (position.afterPick counter.1)
termination_by position.remaining.card
decreasing_by
  all_goals
    apply GamePosition.remaining_card_after_pick_lt
    exact counter.2

/-- The executable classifier is exactly equivalent to proof-level one-sided non-loss. -/
theorem check_eq_true_iff (player : Player) (position : GamePosition) :
    check player position = true ↔ CanAvoidLoss player position := by
  rw [check.eq_def]
  by_cases hterminal : position.IsTerminal
  · simpa [hterminal] using
      (can_avoid_loss_iff_terminal_outcome_ne_loss player position hterminal).symm
  · by_cases htoMove : position.toMove = player
    · rw [ite_eq_right hterminal, ite_eq_left htoMove]
      rw [can_avoid_loss_iff_exists_safe_move player position hterminal htoMove]
      rw [Finset.fold_op_rel_iff_or (r := fun _ value : Bool => value = true) (c := true)
        (by simp)]
      simp only [Bool.false_eq_true, false_or, Finset.mem_attach]
      constructor
      · rintro ⟨⟨counter, hcounter⟩, _, hsafe⟩
        exact ⟨counter, hcounter, (check_eq_true_iff player _).1 hsafe⟩
      · rintro ⟨counter, hcounter, hsafe⟩
        exact ⟨⟨counter, hcounter⟩, True.intro, (check_eq_true_iff player _).2 hsafe⟩
    · rw [ite_eq_right hterminal, ite_eq_right htoMove]
      rw [can_avoid_loss_iff_forall_safe_moves player position hterminal htoMove]
      rw [Finset.fold_op_rel_iff_and (r := fun _ value : Bool => value = true) (c := true)
        (by simp)]
      simp only [true_and, Finset.mem_attach]
      constructor
      · intro hall counter hcounter
        exact (check_eq_true_iff player _).1 (hall ⟨counter, hcounter⟩ True.intro)
      · intro hall counter _
        have hcounter : position.LegalMove counter.1 := counter.2
        exact (check_eq_true_iff player _).2 (hall counter.1 hcounter)
termination_by position.remaining.card
decreasing_by
  all_goals
    apply GamePosition.remaining_card_after_pick_lt
    assumption

end CatchUpSearch.CanAvoidLossClassifier
