import CatchUp.Machine.Lowering.Switch.Entrance

namespace CatchUp.Machine.Lowering.SourceSucc
open Turing ConjectureMachines Compilation Separate Words Switch
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

def clearRow (i : Nat) (a : Bit) : Option Cell :=
  match i with
  | 0 => some (a,.left,3853)
  | 1 => some (a,.left,3854)
  | 2 => if a=0 then some (0,.right,3855) else some (1,.left,3853)
  | 3 => some (a,.right,3856)
  | 4 => if a=0 then some (0,.right,3857) else some (0,.left,3858)
  | 5 => some (a,.left,2138)
  | 6 => some (0,.right,3859)
  | 7 => some (a,.right,3860)
  | 8 => some (a,.right,3856)
  | _ => none

theorem clear_cell (i : Nat) (hi : i<9) (a : Bit) :
    sourceSuccBody.cell (3852+i) a=clearRow i a := by
  interval_cases i <;> fin_cases a <;> rfl

def entryRow (i : Nat) (a : Bit) : Option Cell :=
  match i with
  | 0 => some (a,.left,8636)
  | 1 => some (a,.left,8637)
  | 2 => if a=0 then some (0,.right,8638) else some (1,.right,8639)
  | 3 => some (a,.right,8215)
  | 4 => some (a,.right,4065)
  | _ => none

theorem entry_cell (i : Nat) (hi : i<5) (a : Bit) :
    sourceSuccBody.cell (8635+i) a=entryRow i a := by
  interval_cases i <;> fin_cases a <;> rfl

theorem capture_cell (q : Fin 3851) (a : Bit) :
    sourceSuccBody.cell (3862+q.val) a=(Segment.word 1926 3861).cell 3862 q.val a := by
  exact cell_in sourceSuccBody (sourceSuccBody.segments.take 12)
    (sourceSuccBody.segments.drop 13) (.word 1926 3861) (by rfl) q.val q.isLt a

theorem headback_cell (q : Fin 3851) (a : Bit) :
    sourceSuccBody.cell (1+q.val) a=(Segment.word 3850 0).cell 1 q.val a := by
  exact cell_in sourceSuccBody (sourceSuccBody.segments.take 1)
    (sourceSuccBody.segments.drop 2) (.word 3850 0) (by rfl) q.val q.isLt a

theorem default_first_cell (q : Fin 460) (a : Bit) :
    sourceSuccBody.cell (8175+q.val) a=(Segment.bit 8174 8174 none).cell 8175 q.val a := by
  exact cell_in sourceSuccBody (sourceSuccBody.segments.take 16)
    (sourceSuccBody.segments.drop 17) (.bit 8174 8174 none) (by rfl) q.val q.isLt a

theorem default_last_cell (q : Fin 460) (a : Bit) :
    sourceSuccBody.cell (7714+q.val) a=(Segment.bit 7713 7713 none).cell 7714 q.val a := by
  exact cell_in sourceSuccBody (sourceSuccBody.segments.take 14)
    (sourceSuccBody.segments.drop 15) (.bit 7713 7713 none) (by rfl) q.val q.isLt a

theorem bridge_rows (a : Bit) :
    sourceSuccBody.cell 5788 a=some (a,.right,3861) ∧
    sourceSuccBody.cell 3861 a=some (a,.left,3852) ∧
    sourceSuccBody.cell 3851 a=some (a,.right,0) ∧
    sourceSuccBody.cell 0 a=some (a,.left,8640) ∧
    sourceSuccBody.cell 8575 a=some (a,.right,8174) ∧
    sourceSuccBody.cell 8174 a=some (a,.left,7754) ∧
    sourceSuccBody.cell 8114 a=some (a,.right,7713) ∧
    sourceSuccBody.cell 7713 a=some (a,.left,8640) ∧
    sourceSuccBody.cell 8640 a=some (a,.right,8641) ∧
    sourceSuccBody.cell 8641 a=some (a,.left,-1) := by
  fin_cases a <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end CatchUp.Machine.Lowering.SourceSucc
