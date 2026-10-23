import CatchUp.Machine.Lowering.RelocationRun
import CatchUp.Machine.Lowering.RelocationSites

namespace CatchUp.Machine.Lowering.Relocation
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

/-- The intercepted projected entry performs the actual rightward bridge step. -/
theorem hook_transition (p : Placement) (h : p∈switchPlacements) (a : Bit) :
    machine.transition (entryState p.site.pc) a=
      some (a,.right,relocatedState p (switchBody.size : Int)) := by
  have member := (switch_mem p).mp h
  have facts := switch_hook p h
  have source : program[p.site.pc]?=some (.bank p.site.kind p.site.next) := by
    rw [member.2]
    exact facts.2.2.1
  have result := bank_hook p member.1 source facts.2.1 a
  conv_rhs at result => simp only [member.2,bankBody]
  exact result


/-- The paid bridge moves left into the copied switch entrance. -/
theorem bridge_transition (p : Placement) (h : p∈switchPlacements) (a : Bit) :
    machine.transition (relocatedState p (switchBody.size : Int)) a=
      some (a,.left,relocatedState p (switchBody.entry : Int)) := by
  have member := (switch_mem p).mp h
  have small : (bankBody p.site.kind).entry<(bankBody p.site.kind).size := by
    rw [member.2]
    decide +kernel
  have result := bank_bridge p member.1 small a
  conv_lhs at result => simp only [member.2,bankBody]
  conv_rhs at result => simp only [member.2,bankBody]
  exact result


theorem two_moves {n : Nat} (m : Machine n 2) (first mid last : Fin n)
    (hf : ∀ a, m.transition first a=some (a,.right,mid))
    (hl : ∀ a, m.transition mid a=some (a,.left,last)) (T : Tape Bit) :
    FlatInit.runFrom m 2 ⟨first,T⟩=some ⟨last,T⟩ := by
  simp [FlatInit.runFrom,ConjectureMachines.step,hf,hl]

theorem bridge_run (p : Placement) (h : p∈switchPlacements) (T : Tape Bit) :
    FlatInit.runFrom machine 2 ⟨entryState p.site.pc,T⟩=
      some ⟨relocatedState p (switchBody.entry : Int),T⟩ := by
  have result := two_moves machine (entryState p.site.pc)
    (relocatedState p (switchBody.size : Int)) (relocatedState p (switchBody.entry : Int))
    (hook_transition p h) (bridge_transition p h) T
  exact result


theorem finite_run_add {q : Nat} (m : Machine q 2) (n k : Nat) (c : Cfg q 2) :
    FlatInit.runFrom m (n+k) c=(FlatInit.runFrom m n c).bind (FlatInit.runFrom m k) := by
  induction n generalizing c with
  | zero => simp only [Nat.zero_add,FlatInit.runFrom,Option.bind_some]
  | succ n ih => simp only [Nat.succ_add,FlatInit.runFrom,ih,Option.bind_assoc]

/-- Complete actual candidate-body switch contract at every one of the92sites,
from the projected interpreter entry through its exact program continuation. -/
theorem all_switches (p : Placement) (h : p∈switchPlacements)
    (result data frames : List Nat) :
    ∃ steps, FlatInit.runFrom machine steps
      ⟨entryState p.site.pc,natBanks result (frames++Switch.savedFrames data)⟩=
      some ⟨entryState p.site.next,natBanks data (frames++[result.getLastI])⟩ := by
  have member := (switch_mem p).mp h
  obtain ⟨n,hloc⟩ := Switch.Entrance.switch_correct result data frames
  have lifted := successful_run p member.1 member.2 n _ _ hloc
  simp only [relocated,Int.ofNat_eq_natCast,relocated_return] at lifted
  refine ⟨2+n,?_⟩
  rw [finite_run_add,bridge_run p h,Option.bind_some]
  exact lifted


/-- Existing paid initialization preserves every body execution under its
four-state numeric offset. This is not a claim of reaching each site from blank. -/
theorem initialized_run (n : Nat) (c : Cfg totalSize 2) :
    FlatInit.runFrom M n (FlatInit.embed bits body c)=
      (FlatInit.runFrom machine n c).map (FlatInit.embed bits body) := by
  change FlatInit.runFrom (FlatInit.machine bits body) n (FlatInit.embed bits body c)=_
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [FlatInit.runFrom,FlatInit.step_embed]
    cases hs : ConjectureMachines.step machine c with
    | none => simp only [hs,Option.map_none,Option.bind_none,FlatInit.runFrom]
    | some mid =>
      simpa only [hs,Option.map_some,Option.bind_some,FlatInit.runFrom] using ih mid

/-- The same92-site contract for the actual211100482-state initialized binary
candidate. All saved inputs, results and earlier caller frames remain arbitrary. -/
theorem initialized_switches (p : Placement) (h : p∈switchPlacements)
    (result data frames : List Nat) :
    ∃ steps, FlatInit.runFrom M steps
      (FlatInit.embed bits body
        ⟨entryState p.site.pc,natBanks result (frames++Switch.savedFrames data)⟩)=
      some (FlatInit.embed bits body
        ⟨entryState p.site.next,natBanks data (frames++[result.getLastI])⟩) := by
  obtain ⟨n,run⟩ := all_switches p h result data frames
  refine ⟨n,?_⟩
  rw [initialized_run,run]
  rfl

/-- Coverage stated directly for any actual program switch instruction. -/
theorem program_switch (pc next : Nat)
    (h : program[pc]?=some (.bank Bank.switch next)) (result data frames : List Nat) :
    ∃ steps, FlatInit.runFrom M steps
      (FlatInit.embed bits body
        ⟨entryState pc,natBanks result (frames++Switch.savedFrames data)⟩)=
      some (FlatInit.embed bits body
        ⟨entryState next,natBanks data (frames++[result.getLastI])⟩) := by
  obtain ⟨p,member,pc_eq,next_eq⟩ := switch_coverage pc next h
  have result := initialized_switches p member result data frames
  rw [pc_eq,next_eq] at result
  exact result

/-- The original four-step blank initializer remains the one actually allocated. -/
theorem initialization_preserved : FlatInit.runFrom M 4 ConjectureMachines.init=
    some (FlatInit.embed bits body ⟨0,Tape.mk₁ bits.toList⟩) := initializes

end CatchUp.Machine.Lowering.Relocation
