import CatchUp.Machine.Tail.Initialization

namespace CatchUp.Machine.Tail
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem lift_value (p : Program) (old : Fin (Succ.states (base p))) :
    (lift p old).val=2+old.val := by
  simp [lift,number,layout,finSumFinEquiv]

theorem tail_value (p : Program) (stage : Fin 2) (old : Fin 460) :
    (tailNormal p stage old).val=
      2+prefixStates p+(pool p).length*462+stage.val*463+old.val := by
  simp [tailNormal,number,finSumFinEquiv,finProdFinEquiv]
  omega

theorem boot (p : Program) (T : Tape Bit) :
    run p 2 ⟨0,T⟩=some ⟨entry p 0,T⟩ := by
  change run p 2 ⟨bootState p 0,T⟩=_
  simp [run,FlatInit.runFrom,step,boot_transition]

theorem tail_source_full (p : Program) (initial source frames : List Nat)
    (address : Nat) (h : p[address]?=some .tail) :
    FlatInit.runFrom (generated p initial).toMachine (sourceCost source)
      (embed p initial ⟨entry p address,sourceBanks source frames⟩)=
      some (embed p initial
        ⟨wordState p (Words.start true false),sourceBanks source.tail frames⟩) := by
  rw [run_embed,tail_source p address h source frames,Option.map_some]

/-- Startup creates both call operands. The only initialized words are the
source input, reversed to make source head coincide with stack top. -/
def exampleProgram : Program := [.push 3 1,.push 4 2,.call,.tail,.halt]
def exampleSource : List Nat := [3,0,2]
def exampleData : List Nat := exampleSource.reverse

def programCost (source : List Nat) := literalCost (Words.encode source.reverse) 3+
  (literalCost (Words.encode (source.reverse++[3])) 4+
    (callCost source.reverse [] 3 4+sourceCost source+returnCost source.tail.reverse [] 4))

theorem program_run (source : List Nat) : run exampleProgram (programCost source)
    ⟨entry exampleProgram 0,sourceBanks source []⟩=
    some ⟨entry exampleProgram 4,sourceBanks source.tail []⟩ := by
  exact generated_tail_return exampleProgram source [] 0 1 2 3 4
    (by rfl) (by rfl) (by rfl) (by rfl)

theorem body_run (source : List Nat) : run exampleProgram (2+programCost source)
    ⟨0,sourceBanks source []⟩=
    some ⟨entry exampleProgram 4,sourceBanks source.tail []⟩ := by
  rw [run_add,boot,Option.bind_some,program_run]

theorem blank_run (source : List Nat) :
    FlatInit.runFrom (generated exampleProgram source.reverse).toMachine
      ((4+4*(Words.encode source.reverse).length)+(2+programCost source)) ConjectureMachines.init=
      some (embed exampleProgram source.reverse
        ⟨entry exampleProgram 4,sourceBanks source.tail []⟩) := by
  rw [full_add,initializes,Option.bind_some,run_embed]
  exact congrArg (Option.map (embed exampleProgram source.reverse)) (body_run source)

theorem blank_terminal (source : List Nat) :
    step (generated exampleProgram source.reverse).toMachine (embed exampleProgram source.reverse
      ⟨entry exampleProgram 4,sourceBanks source.tail []⟩)=none := by
  rw [step_embed,terminal exampleProgram _ 4 (Or.inr rfl)]
  rfl

theorem blank_halts (source : List Nat) :
    Halts (generated exampleProgram source.reverse).toMachine := by
  apply Part.dom_iff_mem.mpr
  exact ⟨_,StateTransition.mem_eval.mpr
    ⟨FlatInit.runFrom_reaches _ _ _ _ (blank_run source),blank_terminal source⟩⟩

theorem blank_source_correct (source : List Nat) :
    Turing.ToPartrec.Code.tail.eval source=pure source.tail ∧
      Halts (generated exampleProgram source.reverse).toMachine ∧
      FlatInit.runFrom (generated exampleProgram source.reverse).toMachine
        ((4+4*(Words.encode source.reverse).length)+(2+programCost source))
        ConjectureMachines.init=some (embed exampleProgram source.reverse
          ⟨entry exampleProgram 4,sourceBanks source.tail []⟩) := by
  exact ⟨rfl,blank_halts source,blank_run source⟩

theorem family_count (source : List Nat) :
    (generated exampleProgram source.reverse).states=
      39564+4*(Words.encode source.reverse).length := by
  rw [state_count]
  change 4638*5+462*11+4*(Words.encode source.reverse).length+11292=_
  omega

def M : Machine 39608 2 := (generated exampleProgram exampleData).toMachine

theorem M_count : (generated exampleProgram exampleData).states=39608 := by
  simpa [exampleData,exampleSource,Words.encode,Words.word] using family_count exampleSource

theorem M_run : FlatInit.runFrom M 2772 ConjectureMachines.init=
    some (embed exampleProgram exampleData
      ⟨entry exampleProgram 4,sourceBanks [0,2] []⟩) := by
  simpa [M,exampleData,exampleSource,programCost,literalCost,bitCost,sourceCost,discardCost,
    callCost,Call.callCost,returnCost,Call.returnCost,Call.lookupCost,Dispatch.lookupCost,
    Words.transferCost,Words.encode,Words.word] using blank_run exampleSource

theorem M_terminal : step M (embed exampleProgram exampleData
    ⟨entry exampleProgram 4,sourceBanks [0,2] []⟩)=none := blank_terminal exampleSource

theorem M_halts : Halts M := blank_halts exampleSource

theorem empty_count : (generated exampleProgram []).states=39564 := family_count []

theorem empty_blank_run : FlatInit.runFrom (generated exampleProgram []).toMachine
    1250 ConjectureMachines.init=some (embed exampleProgram []
      ⟨entry exampleProgram 4,sourceBanks [] []⟩) := by
  simpa [programCost,literalCost,bitCost,sourceCost,callCost,Call.callCost,returnCost,
    Call.returnCost,Call.lookupCost,Dispatch.lookupCost,Words.transferCost,Words.encode,Words.word]
    using blank_run []

def loopProgram : Program := [.push 3 1,.push 0 2,.call,.tail]

theorem blank_repeated_source (source : List Nat) (k : Nat) :
    FlatInit.runFrom (generated loopProgram source.reverse).toMachine
      ((4+4*(Words.encode source.reverse).length)+(2+repeatedCost source [] 3 0 k))
      ConjectureMachines.init=some (embed loopProgram source.reverse
        ⟨entry loopProgram 0,sourceBanks (source.drop k) []⟩) := by
  rw [full_add,initializes,Option.bind_some,run_embed,run_add,boot,Option.bind_some]
  exact congrArg (Option.map (embed loopProgram source.reverse))
    (repeated_source_tail loopProgram source [] 0 1 2 3 (by rfl) (by rfl) (by rfl) (by rfl) k)

def rows : List (List (Option (Bit × Dir × Fin 39608))) :=
  (List.finRange 39608).map fun state ↦ (List.finRange 2).map (M.transition state)

theorem table_cells (state : Fin 39608) (bit : Bit) :
    (Machine.ofRows rows).transition state bit=M.transition state bit :=
  Pred.table_cells_generic 39608 M state bit

theorem table_correct : Machine.ofRows rows=M := Pred.table_correct_generic 39608 M

end CatchUp.Machine.Tail
