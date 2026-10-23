/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see the repository LICENSE.
-/
import CatchUp.DenseBlockMass
import CatchUp.DenseLossSubsumGap
open Finset
namespace CatchUp.DenseGapMass
theorem three_small_subsum_complete :
    ∀ A ∈ (Icc 1 7).powerset, A.card = 3 → A.sum (fun x ↦ x) ≤ 7 →
      ∀ t ∈ Icc 1 (A.sum (fun x ↦ x) - 1),
        ∃ D ∈ A.powerset, D.sum (fun x ↦ x) = t := by
  decide +kernel
/-- A true original-support gap excludes a four-counter exact block when the residual has at most three counters. -/
theorem small_gap_block_bound
    (N d b w : ℕ) (S B : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hlarge : 2 * (Icc 1 N \ S).card + 1 ≤ d) (hdN : d ≤ N)
    (hB : B ⊆ S) (hsumB : B.sum (fun x ↦ x) = d) (hb : b ∈ B)
    (hnear : d - (Icc 1 N \ S).card ≤ b) (hw : w ∈ S \ B)
    (hbw : b < w) (hwd : w < d)
    (hgap : ∀ D : Finset ℕ, D ⊆ S → D.sum (fun x ↦ x) ≠ d - w)
    (hc : ((S \ B).erase w).card ≤ 3) :
    B.card ≤ 3 ∧ N ≤ 2 * ((S \ B).erase w).card + 7 := by
  obtain ⟨hk4, _⟩ := DenseBlockMass.small_residual_bound N d b w S B hS hlarge hdN hB hsumB hb hnear hw (by omega)
  let A := B.erase b
  have hcardA : A.card + 1 = B.card := Finset.card_erase_add_one hb
  have hsumA : A.sum (fun x ↦ x) + b = d := by simpa only [hsumB] using Finset.sum_erase_add B (fun x : ℕ ↦ x) hb
  have hholes := DenseBlockMass.holes_le_block_add_residual N d w S B hS hB hw hlarge hdN
  have hmassA : A.sum (fun x ↦ x) ≤ B.card + ((S \ B).erase w).card := by omega
  have hpart := DenseBlockMass.residual_partition N w S B hS hB hw
  suffices hk3 : B.card ≤ 3 by omega
  by_contra hnot
  have hAcard : A.card = 3 := by omega
  have hAseven : A.sum (fun x ↦ x) ≤ 7 := by omega
  have hAS : A ⊆ S := fun _ hx ↦ hB (mem_of_mem_erase hx)
  have hApos : ∀ x ∈ A, 1 ≤ x := fun x hx ↦ (mem_Icc.mp (hS (hAS hx))).1
  have hA7 : A ⊆ Icc 1 7 := fun x hx ↦ mem_Icc.mpr ⟨hApos x hx, (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hx).trans hAseven⟩
  have ht : d - w ∈ Icc 1 (A.sum (fun x ↦ x) - 1) := mem_Icc.mpr ⟨by omega, by omega⟩
  obtain ⟨D, hDA, hsumD⟩ := three_small_subsum_complete A (mem_powerset.mpr hA7) hAcard hAseven (d - w) ht
  exact hgap D (fun x hx ↦ hAS ((mem_powerset.mp hDA) hx)) hsumD
end CatchUp.DenseGapMass

