import CatchUp.Machine.Lowering.Switch.Extract

namespace CatchUp.Machine.Lowering.Switch.Entrance
open Turing ConjectureMachines Compilation Separate Words
set_option maxRecDepth 4096

def clearRow (i : Nat) (a : Bit) : Option Cell :=
  match i with
  | 0 => some (a,.left,10597)
  | 1 => some (a,.left,10598)
  | 2 => if a=0 then some (0,.right,10599) else some (1,.left,10597)
  | 3 => some (a,.right,10600)
  | 4 => if a=0 then some (0,.right,10601) else some (0,.left,10602)
  | 5 => some (a,.left,8882)
  | 6 => some (0,.right,10603)
  | 7 => some (a,.right,10604)
  | 8 => some (a,.right,10600)
  | _ => none

theorem clear_cell (i : Nat) (hi : i<9) (a : Bit) :
    switchBody.cell (10596+i) a=clearRow i a := by
  interval_cases i <;> fin_cases a <;> rfl

def entryRow (i : Nat) (a : Bit) : Option Cell :=
  match i with
  | 0 => some (a,.left,15380)
  | 1 => some (a,.left,15381)
  | 2 => if a=0 then some (0,.right,15382) else some (1,.right,15383)
  | 3 => some (a,.right,14969)
  | 4 => some (a,.right,10809)
  | _ => none

theorem entry_cell (i : Nat) (hi : i<5) (a : Bit) :
    switchBody.cell (15379+i) a=entryRow i a := by
  interval_cases i <;> fin_cases a <;> rfl

theorem capture_cell (q : Fin 3851) (a : Bit) :
    switchBody.cell (10606+q.val) a=(Segment.word 1926 10605).cell 10606 q.val a := by
  exact cell_in switchBody (switchBody.segments.take 152) (switchBody.segments.drop 153)
    (.word 1926 10605) (by rfl) q.val q.isLt a

theorem headback_cell (q : Fin 3851) (a : Bit) :
    switchBody.cell (6745+q.val) a=(Segment.word 3850 6744).cell 6745 q.val a := by
  exact cell_in switchBody (switchBody.segments.take 141) (switchBody.segments.drop 142)
    (.word 3850 6744) (by rfl) q.val q.isLt a

theorem default_first_cell (q : Fin 460) (a : Bit) :
    switchBody.cell (14919+q.val) a=
      (Segment.bit 14918 14918 none).cell 14919 q.val a := by
  exact cell_in switchBody (switchBody.segments.take 156) (switchBody.segments.drop 157)
    (.bit 14918 14918 none) (by rfl) q.val q.isLt a

theorem default_last_cell (q : Fin 460) (a : Bit) :
    switchBody.cell (14458+q.val) a=
      (Segment.bit 14457 14457 none).cell 14458 q.val a := by
  exact cell_in switchBody (switchBody.segments.take 154) (switchBody.segments.drop 155)
    (.bit 14457 14457 none) (by rfl) q.val q.isLt a

theorem bridge_rows (a : Bit) :
    switchBody.cell 12532 a=some (a,.right,10605) ∧
    switchBody.cell 10605 a=some (a,.left,10596) ∧
    switchBody.cell 10595 a=some (a,.right,6744) ∧
    switchBody.cell 6744 a=some (a,.left,6742) ∧
    switchBody.cell 15329 a=some (a,.right,14918) ∧
    switchBody.cell 14918 a=some (a,.left,14508) ∧
    switchBody.cell 14868 a=some (a,.right,14457) ∧
    switchBody.cell 14457 a=some (a,.left,10596) := by
  fin_cases a <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end CatchUp.Machine.Lowering.Switch.Entrance
