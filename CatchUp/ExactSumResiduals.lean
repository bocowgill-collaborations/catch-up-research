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

import CatchUp.ExactSumLossObstruction

/-!
# Exact-deficit residual exclusion

A positive exact-deficit block proves nonloss if every residual opening above a chosen
member of the block is nonlosing. This reusable interface applies the existing exact-sum
loss obstruction and checks every potentially forced larger opening.
-/

namespace CatchUp

/-- An exact-deficit block proves nonloss if every forced larger residual opening is nonlosing. -/
theorem Position.value_ne_loss_of_exact_sum_residuals (S A : Finset ℕ) (d c : ℕ)
    (hc : c ∈ A) (hpos : ∀ x ∈ A, 1 ≤ x) (hsub : A ⊆ S)
    (hsum : A.sum (fun x => x) = d)
    (hnext : ∀ w ∈ S \ A, c < w →
      (afterOpening (S \ A) w).value ≠ .loss) :
    (⟨S,d⟩ : Position).value ≠ .loss := by
  intro hloss
  obtain ⟨w, hw, hl, hgt⟩ :=
    Position.exists_winning_opening_gt_max_of_loss_of_exact_sum S A d
      ⟨c,hc⟩ hpos hsub hsum hloss
  have hcm : c ≤ A.max' ⟨c,hc⟩ := Finset.le_max' _ _ hc
  exact hnext w hw (by omega) hl

end CatchUp
