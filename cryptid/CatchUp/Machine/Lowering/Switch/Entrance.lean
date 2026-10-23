import CatchUp.Machine.Lowering.Switch.EntranceStage

/-! Complete contract of the frozen actual switch body. Natural banks are bottom
first; the source result head is therefore the last word, defaulting to zero. -/
namespace CatchUp.Machine.Lowering.Switch.Entrance
open Turing ConjectureMachines Compilation Separate Words Extract
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem enter_empty (frames : List Bit) :
    run switchBody 4 (15379,banks [] frames)=some (14969,banks [] frames) := by
  have c0 := entry_cell 0 (by omega)
  have c1 := entry_cell 1 (by omega)
  have c2 := entry_cell 2 (by omega)
  have c3 := entry_cell 3 (by omega)
  simp [run,Switch.step,c0,c1,c2,c3,entryRow,banks,home,view,Tape.mk₂,Tape.mk',Tape.move]

theorem enter_nonempty (b : Bit) (data frames : List Bit) :
    run switchBody 4 (15379,banks (b::data) frames)=some (10809,banks (b::data) frames) := by
  have c0 := entry_cell 0 (by omega)
  have c1 := entry_cell 1 (by omega)
  have c2 := entry_cell 2 (by omega)
  have c4 := entry_cell 4 (by omega)
  simp [run,Switch.step,c0,c1,c2,c4,entryRow,banks,home,view,wire,
    Tape.mk₂,Tape.mk',Tape.move]

theorem enter_snoc (data frames : List Bit) (head : Nat) :
    run switchBody 4 (15379,banks (data++word head) frames)=
      some (10809,banks (data++word head) frames) := by
  cases data with
  | nil => exact enter_nonempty 0 _ frames
  | cons b data => exact enter_nonempty b (data++word head) frames

theorem last_snoc (result : List Nat) (head : Nat) :
    (result++[head]).getLastI=head := by
  rw [List.getLastI_eq_getLast?_getD,List.getLast?_append]
  rfl

/-- Actual entrance, at bit-frame generality: the top result survives; all its
other words are cleared. The arbitrary opposite bank is preserved exactly. -/
theorem entrance_bits (result : List Nat) (frames : List Bit) :
    ∃ steps, run switchBody steps (15379,banks (encode result) frames)=
      some (6742,banks (word result.getLastI) frames) := by
  cases result using List.reverseRecOn with
  | nil =>
    obtain ⟨staged,hs⟩ := stage_empty frames
    exact ⟨_,run_chain switchBody (enter_empty frames) hs⟩
  | append_singleton result head =>
    obtain ⟨staged,hs⟩ := stage_nonempty (encode result) frames head
    have path := run_chain switchBody (enter_snoc (encode result) frames head) hs
    refine ⟨4+staged,?_⟩
    simpa only [encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,last_snoc] using path

/-- Unconditional entrance theorem for arbitrary results and complete frame banks. -/
theorem entrance (result frames : List Nat) :
    ∃ steps, run switchBody steps (15379,natBanks result frames)=
      some (6742,natBanks [result.getLastI] frames) := by
  simpa only [natBanks,encode,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
    entrance_bits result (encode frames)

/-- Full actual switch: retain top/default-zero result, clear its tail, restore
saved input, extract the retained word and take the actual external return. -/
theorem switch_correct (result data frames : List Nat) :
    ∃ steps, run switchBody steps
      (Int.ofNat switchBody.entry,natBanks result (frames++savedFrames data))=
      some (-1,natBanks data (frames++[result.getLastI])) := by
  obtain ⟨first,hf⟩ := entrance result (frames++savedFrames data)
  obtain ⟨last,hl⟩ := restore_then_extract result.getLastI data frames
  exact ⟨_,run_chain switchBody hf hl⟩

/-- The same complete contract for the finite binary transition table, including
its local external-port stopping state. No caller-frame depth bound is imposed. -/
theorem binary_switch (result data frames : List Nat) :
    ∃ steps, FlatInit.runFrom (binary switchBody) steps
      ⟨⟨switchBody.entry,by decide +kernel⟩,
        natBanks result (frames++savedFrames data)⟩=
      some ⟨⟨switchBody.size,by omega⟩,natBanks data (frames++[result.getLastI])⟩ := by
  change ∃ steps, FlatInit.runFrom (binary switchBody) steps
    (embed switchBody (Int.ofNat switchBody.entry,
      natBanks result (frames++savedFrames data)))=
    some (embed switchBody (-1,natBanks data (frames++[result.getLastI])))
  obtain ⟨steps,h⟩ := switch_correct result data frames
  refine ⟨steps,?_⟩
  rw [binary_run,h]
  rfl

end CatchUp.Machine.Lowering.Switch.Entrance
