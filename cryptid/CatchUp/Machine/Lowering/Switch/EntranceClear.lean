import CatchUp.Machine.Lowering.Switch.EntranceRows

namespace CatchUp.Machine.Lowering.Switch.Entrance
open Turing ConjectureMachines Compilation Separate Words Extract
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Position of the inward clearing cursor after scanning the entire left bank. -/
def Back (data frames : List Bit) : Tape Bit :=
  ((At (wire data) [] frames).move .right).move .right

theorem back_cons (data frames : List Bit) (b : Bit) :
    Back (data++[b]) frames=At (wire data) [1,b] frames := by
  rw [Back,wire_append]
  exact at_in_pair (wire data) [] frames 1 b

theorem back_nil (frames : List Bit) : Back [] frames=banks [] frames := by
  rw [Back,wire_nil,Extract.at_home,←H_wire]
  rfl

theorem clear_scan (pre data frames : List Bit) :
    run switchBody (2*data.length) (10598,At (wire pre) (wire data) frames)=
      some (10598,At (wire (pre++data)) [] frames) := by
  induction data generalizing pre with
  | nil => simp only [wire_nil,List.append_nil,List.length_nil,Nat.mul_zero,run]
  | cons b data ih =>
    have first : run switchBody 2 (10598,At (wire pre) (wire (b::data)) frames)=
        some (10598,At (wire (pre++[b])) (wire data) frames) := by
      have c1 := clear_cell 2 (by omega)
      have c2 := clear_cell 1 (by omega)
      simp [run,Switch.step,c1,c2,clearRow,At,wire,view,mirror,
        Tape.mk₂,Tape.mk',Tape.move,Tape.write,List.reverse_append,List.reverse_cons]
    have rest := ih (pre++[b])
    rw [show pre++[b]++data=pre++b::data by simp only [List.append_assoc];rfl] at rest
    have path := run_chain switchBody first rest
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_comm] using path

theorem clear_turn (data frames : List Bit) :
    run switchBody 2 (10598,At (wire data) [] frames)=some (10600,Back data frames) := by
  have c1 := clear_cell 2 (by omega)
  have c2 := clear_cell 3 (by omega)
  simp [run,Switch.step,c1,c2,clearRow,At,view,mirror,Tape.mk₂,Tape.mk',Back]

theorem clear_pair (data frames : List Bit) (b : Bit) :
    run switchBody 4 (10600,Back (data++[b]) frames)=some (10600,Back data frames) := by
  rw [back_cons]
  have c1 := clear_cell 4 (by omega)
  have c2 := clear_cell 6 (by omega)
  have c3 := clear_cell 7 (by omega)
  have c4 := clear_cell 8 (by omega)
  simp [run,Switch.step,c1,c2,c3,c4,clearRow,Back,At,view,mirror,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write]

/-- All remaining bits are physically erased, not merely skipped. -/
theorem clear_back (data frames : List Bit) :
    run switchBody (4*data.length) (10600,Back data frames)=
      some (10600,banks [] frames) := by
  induction data using List.reverseRecOn with
  | nil => simp only [List.length_nil,Nat.mul_zero,run,back_nil]
  | append_singleton data b ih =>
    have path := run_chain switchBody (clear_pair data frames b) ih
    simpa only [List.length_append,List.length_singleton,Nat.mul_add,Nat.mul_one,
      Nat.add_comm] using path

theorem clear_entry (data frames : List Bit) :
    run switchBody 2 (10596,banks data frames)=some (10598,At [] (wire data) frames) := by
  have c1 := clear_cell 0 (by omega)
  have c2 := clear_cell 1 (by omega)
  simp [run,Switch.step,c1,c2,clearRow,At,banks,home,view,mirror,
    Tape.mk₂,Tape.mk',Tape.move]

theorem clear_exit (frames : List Bit) :
    run switchBody 2 (10600,banks [] frames)=some (8882,banks [] frames) := by
  have c1 := clear_cell 4 (by omega)
  have c2 := clear_cell 5 (by omega)
  simp [run,Switch.step,c1,c2,clearRow,banks,home,view,
    Tape.mk₂,Tape.mk',Tape.move]

/-- Actual clear routine: arbitrary bit-bank length and arbitrary opposite bank. -/
theorem clear_correct (data frames : List Bit) :
    ∃ steps, run switchBody steps (10596,banks data frames)=
      some (8882,banks [] frames) := by
  have scan := clear_scan [] data frames
  simp only [wire_nil,List.nil_append] at scan
  exact ⟨_,run_chain switchBody
    (run_chain switchBody
      (run_chain switchBody
        (run_chain switchBody (clear_entry data frames) scan) (clear_turn data frames))
      (clear_back data frames)) (clear_exit frames)⟩

end CatchUp.Machine.Lowering.Switch.Entrance
