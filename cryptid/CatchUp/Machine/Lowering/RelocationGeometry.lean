import CatchUp.Machine.Lowering.Candidate
import CatchUp.Machine.Lowering.Switch.Entrance

namespace CatchUp.Machine.Lowering.Relocation
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
attribute [local irreducible] Cases.pool

/-- Every placed body owns a disjoint closed interval, including its bridge. -/
theorem place_lower (ss : List Site) (n : Nat) (p : Placement) (h : p∈place ss n) :
    n≤p.base := by
  induction ss generalizing n with
  | nil => simp [place] at h
  | cons s ss ih =>
    simp only [place,List.mem_cons] at h
    rcases h with eq|h
    · subst p;exact Nat.le_refl _
    · have lower := ih _ h
      omega

theorem place_upper (ss : List Site) (n : Nat) (p : Placement) (h : p∈place ss n) :
    p.base+(bankBody p.site.kind).size+1≤
      n+(ss.map (fun s ↦ (bankBody s.kind).size+1)).sum := by
  induction ss generalizing n with
  | nil => simp [place] at h
  | cons s ss ih =>
    simp only [place,List.mem_cons] at h
    rcases h with eq|h
    · subst p
      simp only [List.map_cons,List.sum_cons]
      omega
    · have upper := ih _ h
      simp only [List.map_cons,List.sum_cons]
      omega

theorem place_bounds (ss : List Site) (n limit : Nat)
    (alloc : n+(ss.map (fun s ↦ (bankBody s.kind).size+1)).sum=limit)
    (p : Placement) (h : p∈place ss n) :
    n≤p.base ∧ p.base+(bankBody p.site.kind).size<limit := by
  have lo := place_lower ss n p h
  have hi := place_upper ss n p h
  exact ⟨lo,Nat.lt_of_succ_le (hi.trans_eq alloc)⟩

def concretePlacements : List Placement := place sites 208978778

theorem placements_concrete : placements=concretePlacements := by
  unfold placements
  rw [base_count]
  rfl

theorem placed_bounds_checked : concretePlacements.all (fun p ↦
    decide (208978778≤p.base ∧ p.base+(bankBody p.site.kind).size<totalSize))=true := by
  decide +kernel

theorem placed_bounds (p : Placement) (h : p∈placements) :
    Cases.states projection≤p.base ∧ p.base+(bankBody p.site.kind).size<totalSize := by
  rw [base_count]
  rw [placements_concrete] at h
  exact of_decide_eq_true (List.all_eq_true.mp placed_bounds_checked p h)

/-- The real first-match lookup selects the intended copy at every interior
control and at its entry bridge, without enumerating all its instructions. -/
theorem place_find (ss : List Site) (n : Nat) (p : Placement) (h : p∈place ss n)
    (q : Nat) (lo : p.base≤q) (hi : q≤p.base+(bankBody p.site.kind).size) :
    (place ss n).find? (fun r ↦ r.base≤q ∧ q≤r.base+(bankBody r.site.kind).size)=some p := by
  induction ss generalizing n with
  | nil => simp [place] at h
  | cons s ss ih =>
    simp only [place,List.mem_cons] at h
    rcases h with eq|h
    · subst p
      simp only [place,List.find?,lo,hi,and_self,decide_true]
    · have lower := place_lower ss (n+(bankBody s.kind).size+1) p h
      have outside : ¬(n≤q ∧ q≤n+(bankBody s.kind).size) := by omega
      simpa only [place,List.find?,outside,decide_false,↓reduceIte] using ih _ h

theorem placement_find (p : Placement) (h : p∈placements) (q : Nat)
    (lo : p.base≤q) (hi : q≤p.base+(bankBody p.site.kind).size) :
    placements.find? (fun r ↦ r.base≤q ∧ q≤r.base+(bankBody r.site.kind).size)=some p := by
  rw [placements_concrete] at h ⊢
  exact place_find sites 208978778 p h q lo hi

end CatchUp.Machine.Lowering.Relocation
