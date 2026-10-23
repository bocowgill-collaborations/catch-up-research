import CatchUp.Machine.Lowering.Switch.ExtractCopy
import CatchUp.Machine.Lowering.Switch.Restore

namespace CatchUp.Machine.Lowering.Save
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev Push := Fin 8
def O (k : Push) : Nat := if k.val<6 then 1+461*k.val else 2799+461*(k.val-6)
def B (k : Push) : Bit := if k.val=1 ∨ k.val=4 then 1 else 0
def P (k : Push) : Nat := O k+50+5*(B k).val
def Bridge (k : Push) : Nat := O k-1
def R (k : Push) : Nat :=
  match k.val with
  | 0 => 2766 | 1 => 51 | 2 => 517 | 3 => 2770 | 4 => 2770
  | 5 => 973 | 6 => 2794 | _ => 2849

theorem push_cells (k : Push) (q : Fin 460) (a : Bit) :
    saveBody.cell (O k+q.val) a=
      (Segment.bit (Bridge k) (Bridge k) none).cell (O k) q.val a := by
  fin_cases k
  all_goals
    first
    | exact Switch.cell_in saveBody (saveBody.segments.take 1)
        (saveBody.segments.drop 2) (.bit 0 0 none) (by rfl) q.val q.isLt a
    | exact Switch.cell_in saveBody (saveBody.segments.take 3)
        (saveBody.segments.drop 4) (.bit 461 461 none) (by rfl) q.val q.isLt a
    | exact Switch.cell_in saveBody (saveBody.segments.take 5)
        (saveBody.segments.drop 6) (.bit 922 922 none) (by rfl) q.val q.isLt a
    | exact Switch.cell_in saveBody (saveBody.segments.take 7)
        (saveBody.segments.drop 8) (.bit 1383 1383 none) (by rfl) q.val q.isLt a
    | exact Switch.cell_in saveBody (saveBody.segments.take 9)
        (saveBody.segments.drop 10) (.bit 1844 1844 none) (by rfl) q.val q.isLt a
    | exact Switch.cell_in saveBody (saveBody.segments.take 11)
        (saveBody.segments.drop 12) (.bit 2305 2305 none) (by rfl) q.val q.isLt a
    | exact Switch.cell_in saveBody (saveBody.segments.take 45)
        (saveBody.segments.drop 46) (.bit 2798 2798 none) (by rfl) q.val q.isLt a
    | exact Switch.cell_in saveBody (saveBody.segments.take 47)
        (saveBody.segments.drop 48) (.bit 3259 3259 none) (by rfl) q.val q.isLt a

theorem push_ports (k : Push) (a : Bit) :
    saveBody.cell (O k+410+5*(B k).val) a=
        some (a,.right,Int.ofNat (Bridge k)) ∧
    saveBody.cell (Bridge k) a=some (a,.left,Int.ofNat (R k)) := by
  fin_cases k <;> fin_cases a <;> exact ⟨rfl,rfl⟩

abbrev Kind := Fin 3
def V (k : Kind) : Bit := if k.val=1 then 1 else 0
def K (k : Kind) : Push := ⟨3+k.val,by omega⟩
def C (k : Kind) : Nat := if k.val=0 then 2779 else if k.val=1 then 2789 else 2784
def Restore (k : Kind) : Nat := if k.val=2 then 2766 else 2770
def Next (k : Kind) : Nat := if k.val=2 then 2774 else 2775
def Q (k : Kind) (i : Nat) : Nat := if i<4 then Restore k+i else C k+(i-4)

def copyRow (k : Kind) (i : Nat) (a : Bit) : Option Cell :=
  let go (w : Bit) (d : Dir) (j : Nat) := some (w,d,Int.ofNat (Q k j))
  match i with
  | 0 => go a .left 1
  | 1 => go a .left 2
  | 2 => if a=0 then go 1 .right 3 else go 1 .left 1
  | 3 => some (a,.right,Int.ofNat (Next k))
  | 4 => go a .right 5
  | 5 => go a .right 6
  | 6 => if a=0 then go a .right 7 else go a .right 8
  | 7 => some (a,.left,Int.ofNat (P (K k)))
  | 8 => go a .right 6
  | _ => none

theorem copy_cell (k : Kind) (i : Nat) (hi : i<9) (a : Bit) :
    saveBody.cell (Q k i) a=copyRow k i a := by
  interval_cases i <;> fin_cases k <;> fin_cases a <;> rfl

def scanRow (i : Nat) (a : Bit) : Option Cell :=
  match i with
  | 0 => some (a,.left,2795)
  | 1 => some (a,.left,2796)
  | 2 => if a=0 then some (0,.right,2797) else some (1,.left,2795)
  | 3 => some (a,.right,2774)
  | _ => none

theorem scan_cell (i : Nat) (hi : i<4) (a : Bit) :
    saveBody.cell (2794+i) a=scanRow i a := by
  interval_cases i <;> fin_cases a <;> rfl

theorem drive_cell (a : Bit) :
    saveBody.cell 2774 a=some (0,if a=0 then .right else .left,
      if a=0 then 2776 else 2777) ∧
    saveBody.cell 2775 a=some (0,if a=0 then .right else .left,
      if a=0 then 2776 else 2778) ∧
    saveBody.cell 2777 0=some (0,.right,2779) ∧
    saveBody.cell 2778 a=some (a,.right,if a=0 then 2784 else 2789) := by
  fin_cases a <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem exit_cell (a : Bit) :
    saveBody.cell 2776 a=some (a,.left,3720) ∧
    saveBody.cell 3720 a=some (a,.right,3721) ∧
    saveBody.cell 3721 a=some (a,.left,-1) := by
  fin_cases a <;> exact ⟨rfl,rfl,rfl⟩

end CatchUp.Machine.Lowering.Save
