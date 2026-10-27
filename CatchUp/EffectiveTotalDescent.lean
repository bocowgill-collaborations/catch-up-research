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
# Exact effective-total descent

This module records scalar identities for deleting an exact-deficit block and then a residual
opening. The identities provide a strict well-founded measure, but by themselves do not preserve
the bounded-hole hypotheses used by the dense-position reductions.
-/

namespace CatchUp

/-- Deleting an exact-deficit block and then opening `w` removes exactly twice the old deficit
from `deficit + remaining.sum`. This subtraction-free form is the primary identity. -/
theorem effective_total_add_twice_deficit_after_exact_block_opening
    (remaining block : Finset ℕ) (deficit w : ℕ)
    (hsub : block ⊆ remaining)
    (hsum : block.sum (fun x => x) = deficit)
    (hw : w ∈ remaining \ block) :
    w + ((remaining \ block).erase w).sum (fun x => x) + 2 * deficit =
      deficit + remaining.sum (fun x => x) := by
  have hsplit :
      (remaining \ block).sum (fun x => x) + block.sum (fun x => x) =
        remaining.sum (fun x => x) := by
    simpa only using Finset.sum_sdiff (f := fun x : ℕ => x) hsub
  have hopen :
      ((remaining \ block).erase w).sum (fun x => x) + w =
        (remaining \ block).sum (fun x => x) := by
    simpa only using Finset.sum_erase_add (remaining \ block) (fun x : ℕ => x) hw
  rw [hsum] at hsplit
  omega

/-- The same descent identity in exact natural-subtraction form. -/
theorem effective_total_after_exact_block_opening
    (remaining block : Finset ℕ) (deficit w : ℕ)
    (hsub : block ⊆ remaining)
    (hsum : block.sum (fun x => x) = deficit)
    (hw : w ∈ remaining \ block) :
    w + ((remaining \ block).erase w).sum (fun x => x) =
      deficit + remaining.sum (fun x => x) - 2 * deficit := by
  have hidentity := effective_total_add_twice_deficit_after_exact_block_opening
    remaining block deficit w hsub hsum hw
  omega

/-- For a positive deficit, every exact-block residual step strictly decreases effective total. -/
theorem effective_total_strictly_decreases_after_exact_block_opening
    (remaining block : Finset ℕ) (deficit w : ℕ)
    (hsub : block ⊆ remaining)
    (hsum : block.sum (fun x => x) = deficit)
    (hw : w ∈ remaining \ block)
    (hdeficit : 0 < deficit) :
    w + ((remaining \ block).erase w).sum (fun x => x) <
      deficit + remaining.sum (fun x => x) := by
  have hidentity := effective_total_add_twice_deficit_after_exact_block_opening
    remaining block deficit w hsub hsum hw
  omega

/-- The new residual position is catchable exactly when the old effective total can pay twice the
old deficit and twice the new opening. -/
theorem exact_block_opening_child_catchable_iff
    (remaining block : Finset ℕ) (deficit w : ℕ)
    (hsub : block ⊆ remaining)
    (hsum : block.sum (fun x => x) = deficit)
    (hw : w ∈ remaining \ block) :
    (¬ ((remaining \ block).erase w).sum (fun x => x) < w) ↔
      2 * deficit + 2 * w ≤ deficit + remaining.sum (fun x => x) := by
  have hidentity := effective_total_add_twice_deficit_after_exact_block_opening
    remaining block deficit w hsub hsum hw
  omega

/-- A catchable strict child with `w > deficit` requires at least `4 * deficit + 2` units of old
effective total. -/
theorem four_deficit_add_two_le_effective_total_of_strict_catchable_child
    (remaining block : Finset ℕ) (deficit w : ℕ)
    (hsub : block ⊆ remaining)
    (hsum : block.sum (fun x => x) = deficit)
    (hw : w ∈ remaining \ block)
    (hstrict : deficit < w)
    (hcatch : ¬ ((remaining \ block).erase w).sum (fun x => x) < w) :
    4 * deficit + 2 ≤ deficit + remaining.sum (fun x => x) := by
  have hbudget := (exact_block_opening_child_catchable_iff
    remaining block deficit w hsub hsum hw).1 hcatch
  omega

end CatchUp
