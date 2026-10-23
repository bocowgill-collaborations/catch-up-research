import CatchUp.Machine.Succ.Initialization

namespace CatchUp.Machine.Succ
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem lift_value (p : Program) (old : Fin (Call.states (base p))) :
    (lift p old).val=old.val := rfl

theorem local_value (p : Program) (stage : Fin 3) (slot : Fin 462) :
    (localState p stage slot).val=Call.states (base p)+stage.val*462+slot.val := by
  simp [localState,number,finSumFinEquiv,finProdFinEquiv]
  omega

theorem boot (p : Program) (T : Tape Bit) :
    run p 2 ⟨0,T⟩=some ⟨wordState p (Words.start false false),T⟩ := by
  change run p 2 ⟨global p 0,T⟩=_
  simp [run,FlatInit.runFrom,step,global_transition,Call.global_transition]

theorem successor_full (p : Program) (input data frames : List Nat) (n : Nat) :
    FlatInit.runFrom (generated p input).toMachine (succCost (Words.encode data) n)
      (embed p input ⟨entry p (some .succ),Words.natBanks (data++[n]) frames⟩) =
      some (embed p input
        ⟨wordState p (Words.start true false),Words.natBanks (data++[n+1]) frames⟩) := by
  rw [run_embed,successor_nat,Option.map_some]

theorem call_successor_full (p : Program) (input data frames : List Nat)
    (n target continuation : Nat) (h : p[target]?=some .succ) :
    FlatInit.runFrom (generated p input).toMachine
      (callCost (data++[n]) frames target continuation+
        succCost (Words.encode data) n+returnCost (data++[n+1]) frames continuation)
      (embed p input ⟨wordState p (Words.start false false),
        Words.natBanks (data++[n,target,continuation]) frames⟩) =
      some (embed p input ⟨entry p p[continuation]?,Words.natBanks (data++[n+1]) frames⟩) := by
  rw [run_embed,call_successor_return p data frames n target continuation h,Option.map_some]

def exampleProgram : Program := [.succ,.halt]
def input (n : Nat) : List Nat := [n,0,1]
def exampleData : List Nat := input 3

def programCost (n : Nat) :=
  callCost [n] [] 0 1+succCost [] n+returnCost [n+1] [] 1

theorem program_run (n : Nat) : run exampleProgram (programCost n)
    ⟨wordState exampleProgram (Words.start false false),Words.natBanks (input n) []⟩ =
    some ⟨entry exampleProgram (some .halt),Words.natBanks [n+1] []⟩ := by
  have h := call_successor_return exampleProgram [] [] n 0 1 (by rfl)
  simpa [programCost,input,Words.encode,exampleProgram] using h

theorem body_run (n : Nat) : run exampleProgram (2+programCost n)
    ⟨0,Words.natBanks (input n) []⟩ =
    some ⟨entry exampleProgram (some .halt),Words.natBanks [n+1] []⟩ := by
  rw [run_add,boot,Option.bind_some,program_run]

theorem blank_run (n : Nat) :
    FlatInit.runFrom (generated exampleProgram (input n)).toMachine
      ((4+4*(Words.encode (input n)).length)+(2+programCost n)) ConjectureMachines.init =
      some (embed exampleProgram (input n)
        ⟨entry exampleProgram (some .halt),Words.natBanks [n+1] []⟩) := by
  rw [full_add,initializes,Option.bind_some,run_embed,body_run,Option.map_some]

theorem blank_terminal (n : Nat) :
    step (generated exampleProgram (input n)).toMachine (embed exampleProgram (input n)
      ⟨entry exampleProgram (some .halt),Words.natBanks [n+1] []⟩)=none := by
  rw [step_embed,terminal exampleProgram _ (some .halt) (Or.inr rfl)]
  rfl

theorem blank_halts (n : Nat) : Halts (generated exampleProgram (input n)).toMachine := by
  apply Part.dom_iff_mem.mpr
  exact ⟨_,StateTransition.mem_eval.mpr
    ⟨FlatInit.runFrom_reaches _ _ _ _ (blank_run n),blank_terminal n⟩⟩

theorem family_count (n : Nat) : (generated exampleProgram (input n)).states=7194+4*n := by
  have h := state_count exampleProgram (input n)
  simpa [exampleProgram,input,Words.encode,Words.word,List.replicate_succ,
    Nat.add_mul,Nat.mul_add,Nat.mul_comm,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

def M : Machine 7206 2 := (generated exampleProgram exampleData).toMachine

theorem M_count : (generated exampleProgram exampleData).states=7206 := by
  exact family_count 3

theorem M_run : FlatInit.runFrom M 682 ConjectureMachines.init =
    some (embed exampleProgram exampleData
      ⟨entry exampleProgram (some .halt),Words.natBanks [4] []⟩) := by
  simpa [M,exampleData,input,programCost,callCost,returnCost,succCost,lookupCost,
    Dispatch.lookupCost,Words.transferCost,Words.encode,Words.word] using blank_run 3

theorem M_terminal : step M (embed exampleProgram exampleData
    ⟨entry exampleProgram (some .halt),Words.natBanks [4] []⟩)=none := blank_terminal 3

theorem M_halts : Halts M := blank_halts 3

def rows : List (List (Option (Bit × Dir × Fin 7206))) :=
  (List.finRange 7206).map fun state ↦ (List.finRange 2).map (M.transition state)

theorem table_cells (state : Fin 7206) (bit : Bit) :
    (Machine.ofRows rows).transition state bit=M.transition state bit := by
  fin_cases bit <;> simp [Machine.ofRows,rows,List.getD_eq_getElem?_getD]

theorem table_correct : Machine.ofRows rows=M :=
  congrArg Machine.mk (funext fun state ↦ funext fun bit ↦ table_cells state bit)

end CatchUp.Machine.Succ
