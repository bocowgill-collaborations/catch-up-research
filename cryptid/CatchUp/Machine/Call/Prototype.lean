import CatchUp.Machine.Call.Initialization
import CatchUp.Machine.Call.Semantics

namespace CatchUp.Machine.Call
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem boot (p : Program) (T : Tape Bit) :
    run p 2 ⟨0,T⟩=some ⟨wordState p (Words.start false false),T⟩ := by
  change run p 2 ⟨global p 0,T⟩=_
  simp [run,FlatInit.runFrom,step,global_transition]

theorem call_full (p : Program) (input data frames : List Nat) (target continuation : Nat) :
    FlatInit.runFrom (generated p input).toMachine (callCost data frames target continuation)
      (embed p input ⟨wordState p (Words.start false false),
        Words.natBanks (data++[target,continuation]) frames⟩) =
      some (embed p input ⟨entry p p[target]?,Words.natBanks data (frames++[continuation])⟩) := by
  rw [run_embed,call_correct,Option.map_some]

theorem return_full (p : Program) (input data frames : List Nat) (continuation : Nat) :
    FlatInit.runFrom (generated p input).toMachine (returnCost data frames continuation)
      (embed p input ⟨wordState p (Words.start true false),
        Words.natBanks data (frames++[continuation])⟩) =
      some (embed p input ⟨entry p p[continuation]?,Words.natBanks data frames⟩) := by
  rw [run_embed,return_correct,Option.map_some]

theorem nested_full (p : Program) (input data frames : List Nat)
    (outerTarget outerContinuation innerTarget innerContinuation : Nat)
    (outer : p[outerTarget]?=some .call) (inner : p[innerTarget]?=some .ret)
    (resume : p[innerContinuation]?=some .ret) :
    FlatInit.runFrom (generated p input).toMachine
      (callCost (data++[innerTarget,innerContinuation]) frames outerTarget outerContinuation+
      (callCost data (frames++[outerContinuation]) innerTarget innerContinuation+
      (returnCost data (frames++[outerContinuation]) innerContinuation+
        returnCost data frames outerContinuation)))
      (embed p input ⟨wordState p (Words.start false false),
        Words.natBanks (data++[innerTarget,innerContinuation,outerTarget,outerContinuation]) frames⟩) =
      some (embed p input ⟨entry p p[outerContinuation]?,Words.natBanks data frames⟩) := by
  rw [run_embed,nested_calls p data frames _ _ _ _ outer inner resume,Option.map_some]

def exampleProgram : Program := [.call,.ret,.ret,.halt]
def exampleData : List Nat := [1,2,0,3]

theorem nested_run : run exampleProgram 1416
    ⟨wordState exampleProgram (Words.start false false),Words.natBanks exampleData []⟩ =
    some ⟨entry exampleProgram (some .halt),Words.natBanks [] []⟩ := by
  have h := nested_calls exampleProgram [] [] 0 3 1 2 (by rfl) (by rfl) (by rfl)
  simpa [exampleProgram,exampleData,callCost,returnCost,lookupCost,Dispatch.lookupCost,
    Words.transferCost,Words.encode,Words.word] using h

theorem body_run : run exampleProgram 1418 ⟨0,Words.natBanks exampleData []⟩ =
    some ⟨entry exampleProgram (some .halt),Words.natBanks [] []⟩ := by
  rw [show 1418=2+1416 by rfl,run_add,boot,Option.bind_some,nested_run]

def M : Machine 6796 2 := (generated exampleProgram exampleData).toMachine

theorem M_count : (generated exampleProgram exampleData).states=6796 := by
  simpa [exampleProgram,exampleData,Words.encode,Words.word] using
    state_count exampleProgram exampleData

theorem M_run : FlatInit.runFrom M 1478 ConjectureMachines.init =
    some (embed exampleProgram exampleData
      ⟨entry exampleProgram (some .halt),Words.natBanks [] []⟩) := by
  have h : FlatInit.runFrom (generated exampleProgram exampleData).toMachine
      ((4+4*(Words.encode exampleData).length)+1418) ConjectureMachines.init =
      some (embed exampleProgram exampleData
        ⟨entry exampleProgram (some .halt),Words.natBanks [] []⟩) := by
    rw [full_add,initializes,Option.bind_some,run_embed,body_run,Option.map_some]
  simpa [M,exampleData,Words.encode,Words.word] using h

theorem M_terminal : step M (embed exampleProgram exampleData
    ⟨entry exampleProgram (some .halt),Words.natBanks [] []⟩)=none := by
  change step (generated exampleProgram exampleData).toMachine _=none
  rw [step_embed,terminal exampleProgram _ (some .halt) (Or.inr rfl)]
  rfl

theorem M_halts : Halts M := by
  apply Part.dom_iff_mem.mpr
  refine ⟨_,StateTransition.mem_eval.mpr
    ⟨FlatInit.runFrom_reaches _ _ _ _ M_run,M_terminal⟩⟩

def rows : List (List (Option (Bit × Dir × Fin 6796))) :=
  (List.finRange 6796).map fun state ↦ (List.finRange 2).map (M.transition state)

theorem table_cells (state : Fin 6796) (bit : Bit) :
    (Machine.ofRows rows).transition state bit=M.transition state bit := by
  fin_cases bit <;> simp [Machine.ofRows,rows,List.getD_eq_getElem?_getD]

theorem table_correct : Machine.ofRows rows=M :=
  congrArg Machine.mk (funext fun state ↦ funext fun bit ↦ table_cells state bit)

end CatchUp.Machine.Call
