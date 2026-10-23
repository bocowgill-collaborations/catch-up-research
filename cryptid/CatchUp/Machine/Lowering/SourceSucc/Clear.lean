import CatchUp.Machine.Lowering.SourceSucc.Rows

namespace CatchUp.Machine.Lowering.SourceSucc
open Turing ConjectureMachines Compilation Separate Words Switch Switch.Extract Switch.Entrance
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem clear_scan (pre data frames : List Bit) :
    Switch.run sourceSuccBody (2*data.length) (3854,At (wire pre) (wire data) frames)=
      some (3854,At (wire (pre++data)) [] frames) := by
  induction data generalizing pre with
  | nil => simp only [wire_nil,List.append_nil,List.length_nil,Nat.mul_zero,Switch.run]
  | cons b data ih =>
    have first : Switch.run sourceSuccBody 2 (3854,At (wire pre) (wire (b::data)) frames)=
        some (3854,At (wire (pre++[b])) (wire data) frames) := by
      have c1 := clear_cell 2 (by omega)
      have c2 := clear_cell 1 (by omega)
      simp [Switch.run,Switch.step,c1,c2,clearRow,At,wire,view,mirror,
        Tape.mk₂,Tape.mk',Tape.move,Tape.write,List.reverse_append,List.reverse_cons]
    have rest := ih (pre++[b])
    rw [show pre++[b]++data=pre++b::data by simp only [List.append_assoc];rfl] at rest
    have path := run_chain sourceSuccBody first rest
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_comm] using path

theorem clear_turn (data frames : List Bit) :
    Switch.run sourceSuccBody 2 (3854,At (wire data) [] frames)=some (3856,Back data frames) := by
  have c1 := clear_cell 2 (by omega)
  have c2 := clear_cell 3 (by omega)
  simp [Switch.run,Switch.step,c1,c2,clearRow,At,view,mirror,Tape.mk₂,Tape.mk',Back]

theorem clear_pair (data frames : List Bit) (b : Bit) :
    Switch.run sourceSuccBody 4 (3856,Back (data++[b]) frames)=some (3856,Back data frames) := by
  rw [back_cons]
  have c1 := clear_cell 4 (by omega)
  have c2 := clear_cell 6 (by omega)
  have c3 := clear_cell 7 (by omega)
  have c4 := clear_cell 8 (by omega)
  simp [Switch.run,Switch.step,c1,c2,c3,c4,clearRow,Back,At,view,mirror,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write]

/-- All remaining bits are physically erased, not merely skipped. -/
theorem clear_back (data frames : List Bit) :
    Switch.run sourceSuccBody (4*data.length) (3856,Back data frames)=
      some (3856,banks [] frames) := by
  induction data using List.reverseRecOn with
  | nil => simp only [List.length_nil,Nat.mul_zero,Switch.run,back_nil]
  | append_singleton data b ih =>
    have path := run_chain sourceSuccBody (clear_pair data frames b) ih
    simpa only [List.length_append,List.length_singleton,Nat.mul_add,Nat.mul_one,
      Nat.add_comm] using path

theorem clear_entry (data frames : List Bit) :
    Switch.run sourceSuccBody 2 (3852,banks data frames)=some (3854,At [] (wire data) frames) := by
  have c1 := clear_cell 0 (by omega)
  have c2 := clear_cell 1 (by omega)
  simp [Switch.run,Switch.step,c1,c2,clearRow,At,banks,home,view,mirror,
    Tape.mk₂,Tape.mk',Tape.move]

theorem clear_exit (frames : List Bit) :
    Switch.run sourceSuccBody 2 (3856,banks [] frames)=some (2138,banks [] frames) := by
  have c1 := clear_cell 4 (by omega)
  have c2 := clear_cell 5 (by omega)
  simp [Switch.run,Switch.step,c1,c2,clearRow,banks,home,view,
    Tape.mk₂,Tape.mk',Tape.move]

/-- Actual clear routine: arbitrary bit-bank length and arbitrary opposite bank. -/
theorem clear_correct (data frames : List Bit) :
    ∃ steps, Switch.run sourceSuccBody steps (3852,banks data frames)=
      some (2138,banks [] frames) := by
  have scan := clear_scan [] data frames
  simp only [wire_nil,List.nil_append] at scan
  exact ⟨_,run_chain sourceSuccBody
    (run_chain sourceSuccBody
      (run_chain sourceSuccBody
        (run_chain sourceSuccBody (clear_entry data frames) scan) (clear_turn data frames))
      (clear_back data frames)) (clear_exit frames)⟩

end CatchUp.Machine.Lowering.SourceSucc
