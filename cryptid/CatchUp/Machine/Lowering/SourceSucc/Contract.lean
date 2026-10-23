import CatchUp.Machine.Lowering.SourceSucc.Stage

namespace CatchUp.Machine.Lowering.SourceSucc
open Turing ConjectureMachines Compilation Separate Words Switch
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem enter_empty (frames : List Bit) :
    Switch.run sourceSuccBody 4 (8635,banks [] frames)=some (8215,banks [] frames) := by
  have c0 := entry_cell 0 (by omega)
  have c1 := entry_cell 1 (by omega)
  have c2 := entry_cell 2 (by omega)
  have c3 := entry_cell 3 (by omega)
  simp [Switch.run,Switch.step,c0,c1,c2,c3,entryRow,banks,home,view,
    Tape.mk₂,Tape.mk',Tape.move]

theorem enter_nonempty (b : Bit) (data frames : List Bit) :
    Switch.run sourceSuccBody 4 (8635,banks (b::data) frames)=
      some (4065,banks (b::data) frames) := by
  have c0 := entry_cell 0 (by omega)
  have c1 := entry_cell 1 (by omega)
  have c2 := entry_cell 2 (by omega)
  have c4 := entry_cell 4 (by omega)
  simp [Switch.run,Switch.step,c0,c1,c2,c4,entryRow,banks,home,view,wire,
    Tape.mk₂,Tape.mk',Tape.move]

theorem enter_snoc (data frames : List Bit) (n : Nat) :
    Switch.run sourceSuccBody 4 (8635,banks (data++word n) frames)=
      some (4065,banks (data++word n) frames) := by
  cases data with
  | nil => exact enter_nonempty 0 _ frames
  | cons b data => exact enter_nonempty b (data++word n) frames

/-- The empty path creates default zero directly on data, without popping or
changing any caller bit. Both delimiter pushes and the actual exit are included. -/
theorem source_succ_empty_bits (frames : List Bit) :
    ∃ steps, Switch.run sourceSuccBody steps
      (Int.ofNat sourceSuccBody.entry,banks [] frames)=some (-1,banks (word 0) frames) := by
  rw [show Int.ofNat sourceSuccBody.entry=(8635 : Int) by decide +kernel]
  obtain ⟨staged,hs⟩ := default_word [] frames
  exact ⟨_,run_chain sourceSuccBody
    (run_chain sourceSuccBody (enter_empty frames) hs) (return_exit (banks (word 0) frames))⟩

/-- A complete top word is retained, every earlier data bit is erased, and
all caller bits are preserved. The earlier data prefix need not encode words. -/
theorem source_succ_nonempty_bits (data frames : List Bit) (n : Nat) :
    ∃ steps, Switch.run sourceSuccBody steps
      (Int.ofNat sourceSuccBody.entry,banks (data++word n) frames)=
      some (-1,banks (word n) frames) := by
  rw [show Int.ofNat sourceSuccBody.entry=(8635 : Int) by decide +kernel]
  obtain ⟨staged,hs⟩ := stage_nonempty data frames n
  exact ⟨_,run_chain sourceSuccBody
    (run_chain sourceSuccBody (enter_snoc data frames n) hs) (return_exit (banks (word n) frames))⟩

/-- Actual source-successor input normalization, including empty input.
The shared increment instruction is the separate program continuation. -/
theorem source_succ_bits (data : List Nat) (frames : List Bit) :
    ∃ steps, Switch.run sourceSuccBody steps
      (Int.ofNat sourceSuccBody.entry,banks (encode data) frames)=
      some (-1,banks (word data.getLastI) frames) := by
  cases data using List.reverseRecOn with
  | nil => exact source_succ_empty_bits frames
  | append_singleton data n =>
    simpa only [encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,Switch.Entrance.last_snoc] using
      source_succ_nonempty_bits (encode data) frames n

theorem source_succ_correct (data frames : List Nat) :
    ∃ steps, Switch.run sourceSuccBody steps
      (Int.ofNat sourceSuccBody.entry,natBanks data frames)=
      some (-1,natBanks [data.getLastI] frames) := by
  simpa only [natBanks,encode,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
    source_succ_bits data (encode frames)

end CatchUp.Machine.Lowering.SourceSucc
