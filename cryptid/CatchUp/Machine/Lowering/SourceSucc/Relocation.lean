import CatchUp.Machine.Lowering.SourceSucc.Lift

namespace CatchUp.Machine.Lowering.SourceSucc
open Turing ConjectureMachines Compilation Separate Words Relocation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

theorem source_succ_hook_transition (p : Placement) (h : p∈sourceSuccPlacements) (a : Bit) :
    machine.transition (entryState p.site.pc) a=
      some (a,.right,relocatedState p (sourceSuccBody.size : Int)) := by
  have member := (source_succ_mem p).mp h
  have facts := source_succ_hook p h
  have source : program[p.site.pc]?=some (.bank p.site.kind p.site.next) := by
    rw [member.2]
    exact facts.2
  have result := bank_hook p member.1 source facts.1 a
  conv_rhs at result => simp only [member.2,bankBody]
  exact result

theorem source_succ_bridge_transition (p : Placement) (h : p∈sourceSuccPlacements) (a : Bit) :
    machine.transition (relocatedState p (sourceSuccBody.size : Int)) a=
      some (a,.left,relocatedState p (sourceSuccBody.entry : Int)) := by
  have member := (source_succ_mem p).mp h
  have small : (bankBody p.site.kind).entry<(bankBody p.site.kind).size := by
    rw [member.2]
    decide +kernel
  have result := bank_bridge p member.1 small a
  conv_lhs at result => simp only [member.2,bankBody]
  conv_rhs at result => simp only [member.2,bankBody]
  exact result

theorem source_succ_bridge (p : Placement) (h : p∈sourceSuccPlacements) (T : Tape Bit) :
    FlatInit.runFrom machine 2 ⟨entryState p.site.pc,T⟩=
      some ⟨relocatedState p (sourceSuccBody.entry : Int),T⟩ := by
  have result := two_moves machine (entryState p.site.pc)
    (relocatedState p (sourceSuccBody.size : Int))
    (relocatedState p (sourceSuccBody.entry : Int))
    (source_succ_hook_transition p h) (source_succ_bridge_transition p h) T
  exact result

/-- The actual single copy, including its paid bridge and exact continuation,
normalizes arbitrary input and preserves every earlier caller bit. -/
theorem all_source_succs_bits (p : Placement) (h : p∈sourceSuccPlacements)
    (data : List Nat) (frames : List Bit) :
    ∃ steps, FlatInit.runFrom machine steps
      ⟨entryState p.site.pc,banks (encode data) frames⟩=
      some ⟨entryState p.site.next,banks (word data.getLastI) frames⟩ := by
  have member := (source_succ_mem p).mp h
  obtain ⟨n,hloc⟩ := source_succ_bits data frames
  have lifted := source_succ_run p member.1 member.2 n _ _ hloc
  simp only [relocated,Int.ofNat_eq_natCast,relocated_return] at lifted
  refine ⟨2+n,?_⟩
  rw [finite_run_add,source_succ_bridge p h,Option.bind_some]
  exact lifted

theorem all_source_succs (p : Placement) (h : p∈sourceSuccPlacements)
    (data frames : List Nat) :
    ∃ steps, FlatInit.runFrom machine steps ⟨entryState p.site.pc,natBanks data frames⟩=
      some ⟨entryState p.site.next,natBanks [data.getLastI] frames⟩ := by
  simpa only [natBanks,encode,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
    all_source_succs_bits p h data (encode frames)

theorem initialized_source_succs_bits (p : Placement) (h : p∈sourceSuccPlacements)
    (data : List Nat) (frames : List Bit) :
    ∃ steps, FlatInit.runFrom M steps
      (FlatInit.embed bits body ⟨entryState p.site.pc,banks (encode data) frames⟩)=
      some (FlatInit.embed bits body
        ⟨entryState p.site.next,banks (word data.getLastI) frames⟩) := by
  obtain ⟨n,run⟩ := all_source_succs_bits p h data frames
  refine ⟨n,?_⟩
  rw [initialized_run,run]
  rfl

theorem initialized_source_succs (p : Placement) (h : p∈sourceSuccPlacements)
    (data frames : List Nat) :
    ∃ steps, FlatInit.runFrom M steps
      (FlatInit.embed bits body ⟨entryState p.site.pc,natBanks data frames⟩)=
      some (FlatInit.embed bits body ⟨entryState p.site.next,natBanks [data.getLastI] frames⟩) := by
  obtain ⟨n,run⟩ := all_source_succs p h data frames
  refine ⟨n,?_⟩
  rw [initialized_run,run]
  rfl

theorem program_source_succ (pc next : Nat)
    (h : program[pc]?=some (.bank Bank.sourceSucc next)) (data frames : List Nat) :
    ∃ steps, FlatInit.runFrom M steps
      (FlatInit.embed bits body ⟨entryState pc,natBanks data frames⟩)=
      some (FlatInit.embed bits body ⟨entryState next,natBanks [data.getLastI] frames⟩) := by
  obtain ⟨p,member,pc_eq,next_eq⟩ := source_succ_coverage pc next h
  have result := initialized_source_succs p member data frames
  rw [pc_eq,next_eq] at result
  exact result

/-- Concrete program site: resume PC6, whose opcode is the shared increment.
Executing that core opcode is not part of this bank-body theorem. -/
theorem actual_source_successor (data frames : List Nat) :
    ∃ steps, FlatInit.runFrom M steps
      (FlatInit.embed bits body ⟨entryState 9,natBanks data frames⟩)=
      some (FlatInit.embed bits body ⟨entryState 6,natBanks [data.getLastI] frames⟩) := by
  have actual : program[9]?=some (.bank Bank.sourceSucc 6) := by decide +kernel
  exact program_source_succ 9 6 actual data frames

end CatchUp.Machine.Lowering.SourceSucc
