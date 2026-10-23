import CatchUp.Machine.Lowering.Save.Lift

namespace CatchUp.Machine.Lowering.Save
open Turing ConjectureMachines Compilation Separate Words Relocation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

theorem save_hook_transition (p : Placement) (h : p∈savePlacements) (a : Bit) :
    machine.transition (entryState p.site.pc) a=
      some (a,.right,relocatedState p (saveBody.size : Int)) := by
  have member := (save_mem p).mp h
  have facts := save_hook p h
  have source : program[p.site.pc]?=some (.bank p.site.kind p.site.next) := by
    rw [member.2]
    exact facts.2
  have result := bank_hook p member.1 source facts.1 a
  conv_rhs at result => simp only [member.2,bankBody]
  exact result

theorem save_bridge_transition (p : Placement) (h : p∈savePlacements) (a : Bit) :
    machine.transition (relocatedState p (saveBody.size : Int)) a=
      some (a,.left,relocatedState p (saveBody.entry : Int)) := by
  have member := (save_mem p).mp h
  have small : (bankBody p.site.kind).entry<(bankBody p.site.kind).size := by
    rw [member.2]
    decide +kernel
  have result := bank_bridge p member.1 small a
  conv_lhs at result => simp only [member.2,bankBody]
  conv_rhs at result => simp only [member.2,bankBody]
  exact result

theorem save_bridge (p : Placement) (h : p∈savePlacements) (T : Tape Bit) :
    FlatInit.runFrom machine 2 ⟨entryState p.site.pc,T⟩=
      some ⟨relocatedState p (saveBody.entry : Int),T⟩ := by
  have result := two_moves machine (entryState p.site.pc)
    (relocatedState p (saveBody.size : Int)) (relocatedState p (saveBody.entry : Int))
    (save_hook_transition p h) (save_bridge_transition p h) T
  exact result

/-- All 92 actual save copies, including each paid entry bridge and its exact
continuation. The full input and arbitrary earlier bit frames are preserved. -/
theorem all_saves_bits (p : Placement) (h : p∈savePlacements)
    (data : List Nat) (frames : List Bit) :
    ∃ steps, FlatInit.runFrom machine steps
      ⟨entryState p.site.pc,banks (encode data) frames⟩=
      some ⟨entryState p.site.next,banks (encode data) (frames++Switch.savedPayload data)⟩ := by
  have member := (save_mem p).mp h
  obtain ⟨n,hloc⟩ := save_bits data frames
  have lifted := save_run p member.1 member.2 n _ _ hloc
  simp only [relocated,Int.ofNat_eq_natCast,relocated_return] at lifted
  refine ⟨2+n,?_⟩
  rw [finite_run_add,save_bridge p h,Option.bind_some]
  exact lifted

theorem all_saves (p : Placement) (h : p∈savePlacements) (data frames : List Nat) :
    ∃ steps, FlatInit.runFrom machine steps ⟨entryState p.site.pc,natBanks data frames⟩=
      some ⟨entryState p.site.next,natBanks data (frames++Switch.savedFrames data)⟩ := by
  simpa only [natBanks,Switch.savedPayload,encode,List.flatMap_append] using
    all_saves_bits p h data (encode frames)

theorem initialized_saves_bits (p : Placement) (h : p∈savePlacements)
    (data : List Nat) (frames : List Bit) :
    ∃ steps, FlatInit.runFrom M steps
      (FlatInit.embed bits body ⟨entryState p.site.pc,banks (encode data) frames⟩)=
      some (FlatInit.embed bits body
        ⟨entryState p.site.next,banks (encode data) (frames++Switch.savedPayload data)⟩) := by
  obtain ⟨n,run⟩ := all_saves_bits p h data frames
  refine ⟨n,?_⟩
  rw [initialized_run,run]
  rfl

theorem initialized_saves (p : Placement) (h : p∈savePlacements) (data frames : List Nat) :
    ∃ steps, FlatInit.runFrom M steps
      (FlatInit.embed bits body ⟨entryState p.site.pc,natBanks data frames⟩)=
      some (FlatInit.embed bits body
        ⟨entryState p.site.next,natBanks data (frames++Switch.savedFrames data)⟩) := by
  obtain ⟨n,run⟩ := all_saves p h data frames
  refine ⟨n,?_⟩
  rw [initialized_run,run]
  rfl

/-- Directly stated for every actual program instruction, in the paid,
initialized 211100482-state candidate. No source-to-machine assumption is used. -/
theorem program_save (pc next : Nat)
    (h : program[pc]?=some (.bank Bank.save next)) (data frames : List Nat) :
    ∃ steps, FlatInit.runFrom M steps
      (FlatInit.embed bits body ⟨entryState pc,natBanks data frames⟩)=
      some (FlatInit.embed bits body
        ⟨entryState next,natBanks data (frames++Switch.savedFrames data)⟩) := by
  obtain ⟨p,member,pc_eq,next_eq⟩ := save_coverage pc next h
  have result := initialized_saves p member data frames
  rw [pc_eq,next_eq] at result
  exact result

end CatchUp.Machine.Lowering.Save
