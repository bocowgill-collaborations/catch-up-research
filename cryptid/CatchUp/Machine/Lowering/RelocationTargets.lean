import CatchUp.Machine.Lowering.Switch.Entrance

namespace CatchUp.Machine.Lowering.Relocation
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Negative targets are external returns; all other targets must remain local. -/
def LocalTarget (bound : Nat) (q : Int) : Prop := q<0 ∨ q.toNat<bound

instance (bound : Nat) (q : Int) : Decidable (LocalTarget bound q) :=
  inferInstanceAs (Decidable (q<0 ∨ q.toNat<bound))

def safeCell (bound : Nat) (c : Option Cell) : Bool :=
  match c with
  | none => true
  | some (_,_,q) => decide (LocalTarget bound q)

def safeSegment (bound : Nat) : Segment → Bool
  | .row z o => safeCell bound z && safeCell bound o
  | .bit z o empty => decide (z<bound ∧ o<bound) && empty.all (fun n ↦ decide (n<bound))
  | .word _ next => decide (next<bound)

theorem safe_row (bound : Nat) (c : Option Cell) (w : Bit) (d : Dir) (q : Int)
    (h : safeCell bound c=true) (hc : c=some (w,d,q)) : LocalTarget bound q := by
  simpa only [safeCell,hc,decide_eq_true_eq] using h

theorem safe_segment_target (bound offset q : Nat) (s : Segment) (a w : Bit)
    (d : Dir) (out : Int) (within : offset+s.size≤bound)
    (safe : safeSegment bound s=true) (h : s.cell offset q a=some (w,d,out)) :
    LocalTarget bound out := by
  cases s with
  | row z o =>
    simp only [safeSegment,Bool.and_eq_true] at safe
    simp only [Segment.cell] at h
    split at h
    · exact safe_row bound z w d out safe.1 h
    · exact safe_row bound o w d out safe.2 h
  | bit z o empty =>
    simp only [safeSegment,Bool.and_eq_true,decide_eq_true_eq] at safe
    simp only [Segment.cell] at h
    split at h
    · rename_i hq
      cases ht : Separate.machine.transition ⟨q,hq⟩ a with
      | some triple =>
        rcases triple with ⟨write,dir,next⟩
        simp only [ht,Option.some.injEq,Prod.mk.injEq] at h
        have hn := next.isLt
        rcases h with ⟨_,_,rfl⟩
        right
        simp only [Int.ofNat_eq_natCast,Int.toNat_natCast]
        change offset+460≤bound at within
        omega
      | none =>
        simp only [ht] at h
        split at h
        · simp only [Option.some.injEq,Prod.mk.injEq] at h
          rcases h with ⟨_,_,rfl⟩
          right
          simp only [Int.ofNat_eq_natCast,Int.toNat_natCast]
          split <;> omega
        · split at h
          · cases empty with
            | none => simp at h
            | some n =>
              simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨_,_,rfl⟩
              right
              simpa only [Option.all,decide_eq_true_eq,Int.ofNat_eq_natCast,
                Int.toNat_natCast] using safe.2
          · cases h
    · cases h
  | word done next =>
    simp only [safeSegment,decide_eq_true_eq] at safe
    simp only [Segment.cell] at h
    split at h
    · simp only [Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨_,_,rfl⟩
      exact Or.inr (by simpa only [Int.ofNat_eq_natCast,Int.toNat_natCast] using safe)
    · split at h
      · rename_i hq
        cases ht : Words.machine.transition ⟨q,hq⟩ a with
        | none => simp [ht] at h
        | some triple =>
          rcases triple with ⟨write,dir,target⟩
          simp only [ht,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
          rcases h with ⟨_,_,rfl⟩
          right
          simp only [Int.ofNat_eq_natCast,Int.toNat_natCast]
          change offset+3851≤bound at within
          have hn := target.isLt
          omega
      · cases h

theorem safe_cells_target (bound offset q : Nat) (ss : List Segment) (a w : Bit)
    (d : Dir) (out : Int) (within : offset+(ss.map Segment.size).sum≤bound)
    (safe : ss.all (safeSegment bound)=true) (h : cells ss offset q a=some (w,d,out)) :
    LocalTarget bound out := by
  induction ss generalizing offset q with
  | nil => cases h
  | cons s ss ih =>
    simp only [List.all_cons,Bool.and_eq_true] at safe
    simp only [List.map_cons,List.sum_cons] at within
    rw [cells] at h
    split at h
    · exact safe_segment_target bound offset q s a w d out (by omega) safe.1 h
    · exact ih (offset+s.size) (q-s.size) (by omega) safe.2 h

theorem switch_targets_checked :
    switchBody.segments.all (safeSegment switchBody.size)=true := by
  decide +kernel

theorem switch_targets (q : Nat) (a w : Bit) (d : Dir) (out : Int)
    (h : switchBody.cell q a=some (w,d,out)) : LocalTarget switchBody.size out :=
  safe_cells_target switchBody.size 0 q switchBody.segments a w d out
    (by simp only [Micro.size,Nat.zero_add];exact Nat.le_refl _) switch_targets_checked h

end CatchUp.Machine.Lowering.Relocation
