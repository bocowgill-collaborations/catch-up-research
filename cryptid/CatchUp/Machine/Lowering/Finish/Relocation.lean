import CatchUp.Machine.Lowering.Finish.Lift

namespace CatchUp.Machine.Lowering.Finish
open Turing ConjectureMachines Compilation Separate Words Relocation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

theorem finish_hook_transition (p : Placement) (h : p∈finishPlacements) (a : Bit) :
    machine.transition (entryState p.site.pc) a=
      some (a,.right,relocatedState p (finishBody.size : Int)) := by
  have member := (finish_mem p).mp h
  have facts := finish_hook p h
  have source : program[p.site.pc]?=some (.bank p.site.kind p.site.next) := by
    rw [member.2]
    exact facts.2
  have result := bank_hook p member.1 source facts.1 a
  conv_rhs at result => simp only [member.2,bankBody]
  exact result

theorem finish_bridge_transition (p : Placement) (h : p∈finishPlacements) (a : Bit) :
    machine.transition (relocatedState p (finishBody.size : Int)) a=
      some (a,.left,relocatedState p (finishBody.entry : Int)) := by
  have member := (finish_mem p).mp h
  have small : (bankBody p.site.kind).entry<(bankBody p.site.kind).size := by
    rw [member.2]
    decide +kernel
  have result := bank_bridge p member.1 small a
  conv_lhs at result => simp only [member.2,bankBody]
  conv_rhs at result => simp only [member.2,bankBody]
  exact result

theorem finish_bridge (p : Placement) (h : p∈finishPlacements) (T : Tape Bit) :
    FlatInit.runFrom machine 2 ⟨entryState p.site.pc,T⟩=
      some ⟨relocatedState p (finishBody.entry : Int),T⟩ := by
  have result := two_moves machine (entryState p.site.pc)
    (relocatedState p (finishBody.size : Int)) (relocatedState p (finishBody.entry : Int))
    (finish_hook_transition p h) (finish_bridge_transition p h) T
  exact result

/-- All actual copies, with arbitrary bit data and caller frames. The six
additional steps include both entry-bridge steps and all four return steps. -/
theorem all_finishes_bits (p : Placement) (h : p∈finishPlacements)
    (data frames : List Bit) (n : Nat) :
    FlatInit.runFrom machine (transferCost frames data n+6)
      ⟨entryState p.site.pc,banks data (frames++word n)⟩=
      some ⟨entryState p.site.next,banks (data++word n) frames⟩ := by
  have member := (finish_mem p).mp h
  have hloc := finish_bits data frames n
  have lifted := finish_run p member.1 member.2 _ _ _ hloc
  simp only [relocated,Int.ofNat_eq_natCast,relocated_return] at lifted
  rw [show transferCost frames data n+6=2+(transferCost frames data n+4) by omega,
    finite_run_add,finish_bridge p h,Option.bind_some]
  exact lifted

theorem all_finishes (p : Placement) (h : p∈finishPlacements)
    (data frames : List Nat) (n : Nat) :
    FlatInit.runFrom machine (transferCost (encode frames) (encode data) n+6)
      ⟨entryState p.site.pc,natBanks data (frames++[n])⟩=
      some ⟨entryState p.site.next,natBanks (data++[n]) frames⟩ := by
  simpa only [natBanks,encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil] using all_finishes_bits p h (encode data) (encode frames) n

theorem initialized_finishes_bits (p : Placement) (h : p∈finishPlacements)
    (data frames : List Bit) (n : Nat) :
    FlatInit.runFrom M (transferCost frames data n+6)
      (FlatInit.embed bits body ⟨entryState p.site.pc,banks data (frames++word n)⟩)=
      some (FlatInit.embed bits body ⟨entryState p.site.next,banks (data++word n) frames⟩) := by
  rw [initialized_run,all_finishes_bits p h]
  rfl

theorem initialized_finishes (p : Placement) (h : p∈finishPlacements)
    (data frames : List Nat) (n : Nat) :
    FlatInit.runFrom M (transferCost (encode frames) (encode data) n+6)
      (FlatInit.embed bits body ⟨entryState p.site.pc,natBanks data (frames++[n])⟩)=
      some (FlatInit.embed bits body ⟨entryState p.site.next,natBanks (data++[n]) frames⟩) := by
  rw [initialized_run,all_finishes p h]
  rfl

/-- Direct coverage of every actual finish instruction in the initialized
candidate. No bound on retained values, data length or caller depth is assumed. -/
theorem program_finish (pc next : Nat)
    (h : program[pc]?=some (.bank Bank.finish next)) (data frames : List Nat) (n : Nat) :
    FlatInit.runFrom M (transferCost (encode frames) (encode data) n+6)
      (FlatInit.embed bits body ⟨entryState pc,natBanks data (frames++[n])⟩)=
      some (FlatInit.embed bits body ⟨entryState next,natBanks (data++[n]) frames⟩) := by
  obtain ⟨p,member,pc_eq,next_eq⟩ := finish_coverage pc next h
  have result := initialized_finishes p member data frames n
  rw [pc_eq,next_eq] at result
  exact result

end CatchUp.Machine.Lowering.Finish
