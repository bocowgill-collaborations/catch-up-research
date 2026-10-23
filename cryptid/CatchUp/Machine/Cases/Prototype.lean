import CatchUp.Machine.Cases.Initialization

namespace CatchUp.Machine.Cases
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem boot (p : Program) (T : Tape Bit) :
    run p 2 ⟨0,T⟩=some ⟨entry p 0,T⟩ := by
  change run p 2 ⟨bootState p 0,T⟩=_
  simp [run,FlatInit.runFrom,step,boot_transition]

theorem case_source_full (p : Program) (initial source frames : List Nat)
    (address z s : Nat) (h : p[address]?=some (.caseOf z s)) :
    FlatInit.runFrom (generated p initial).toMachine (caseCost source)
      (embed p initial ⟨entry p address,sourceBanks source frames⟩)=
      some (embed p initial
        ⟨entry p (caseTarget z s source),sourceBanks (caseArgument source) frames⟩) := by
  rw [run_embed,case_source p address z s h source frames,Option.map_some]

theorem source_zero_push (p : Program) (address next : Nat)
    (h : p[address]?=some (.push 0 next)) (source frames : List Nat) :
    run p (literalCost (Words.encode source.reverse) 0)
      ⟨entry p address,sourceBanks source frames⟩=
      some ⟨entry p next,sourceBanks (0::source) frames⟩ := by
  simpa [sourceBanks,List.reverse_cons] using
    literal_push_nat p address 0 next h source.reverse frames

/-- Zero arm is source zero'; successor arm is source zero' after zero'.
The two branch bodies are concrete and share the real return routine. -/
def exampleProgram : Program :=
  [.push 3 1,.push 8 2,.call,.caseOf 4 5,.push 0 7,.push 0 6,.push 0 7,.ret,.halt]
def exampleCode : Turing.ToPartrec.Code := .case .zero' (.comp .zero' .zero')
def exampleResult (source : List Nat) :=
  if source.headI=0 then 0::caseArgument source else 0::0::caseArgument source
def branchCost (source : List Nat) :=
  if source.headI=0 then literalCost (Words.encode (caseArgument source).reverse) 0
  else literalCost (Words.encode (caseArgument source).reverse) 0+
    literalCost (Words.encode (0::caseArgument source).reverse) 0

theorem example_eval (source : List Nat) :
    exampleCode.eval source=pure (exampleResult source) := by
  rw [exampleCode,case_source_eval]
  by_cases h : source.headI=0 <;>
    simp [h,exampleResult,Turing.ToPartrec.Code.eval]

theorem branch_run (source frames : List Nat) :
    run exampleProgram (branchCost source)
      ⟨entry exampleProgram (caseTarget 4 5 source),sourceBanks (caseArgument source) frames⟩=
      some ⟨wordState exampleProgram (Words.start true false),
        sourceBanks (exampleResult source) frames⟩ := by
  by_cases h : source.headI=0
  · have a := source_zero_push exampleProgram 4 7 (by rfl) (caseArgument source) frames
    rw [entry_return exampleProgram 7 (by rfl)] at a
    simpa [branchCost,caseTarget,exampleResult,h] using a
  · have a := source_zero_push exampleProgram 5 6 (by rfl) (caseArgument source) frames
    have b := source_zero_push exampleProgram 6 7 (by rfl) (0::caseArgument source) frames
    rw [entry_return exampleProgram 7 (by rfl)] at b
    simp only [branchCost,caseTarget,exampleResult,h,↓reduceIte]
    rw [run_add,a,Option.bind_some,b]

theorem example_constructor (source frames : List Nat) :
    exampleResult source ∈ exampleCode.eval source ∧
      run exampleProgram (caseCost source+branchCost source)
        ⟨entry exampleProgram 3,sourceBanks source frames⟩=
        some ⟨wordState exampleProgram (Words.start true false),
          sourceBanks (exampleResult source) frames⟩ := by
  apply case_compose exampleProgram 3 4 5 (by rfl) .zero' (.comp .zero' .zero')
    source (exampleResult source) frames (branchCost source)
  · rw [←case_source_eval]
    change exampleResult source ∈ exampleCode.eval source
    rw [example_eval]
    exact Part.mem_some_iff.mpr rfl
  · exact branch_run source frames

def programCost (source : List Nat) (frames : List Nat) :=
  literalCost (Words.encode source.reverse) 3+
    (literalCost (Words.encode (source.reverse++[3])) 8+
      (callCost source.reverse frames 3 8+(caseCost source+branchCost source)+
        returnCost (exampleResult source).reverse frames 8))

theorem program_run (source frames : List Nat) :
    run exampleProgram (programCost source frames)
      ⟨entry exampleProgram 0,sourceBanks source frames⟩=
      some ⟨entry exampleProgram 8,sourceBanks (exampleResult source) frames⟩ := by
  exact generated_case_return exampleProgram source (exampleResult source) frames
    0 1 2 3 8 4 5 (branchCost source) (by rfl) (by rfl) (by rfl) (by rfl)
    (branch_run source (frames++[8]))

theorem body_run (source : List Nat) : run exampleProgram (2+programCost source [])
    ⟨0,sourceBanks source []⟩=
    some ⟨entry exampleProgram 8,sourceBanks (exampleResult source) []⟩ := by
  rw [run_add,boot,Option.bind_some,program_run]

theorem blank_run (source : List Nat) :
    FlatInit.runFrom (generated exampleProgram source.reverse).toMachine
      ((4+4*(Words.encode source.reverse).length)+(2+programCost source []))
      ConjectureMachines.init=some (embed exampleProgram source.reverse
        ⟨entry exampleProgram 8,sourceBanks (exampleResult source) []⟩) := by
  rw [full_add,initializes,Option.bind_some,run_embed]
  exact congrArg (Option.map (embed exampleProgram source.reverse)) (body_run source)

theorem blank_terminal (source : List Nat) :
    step (generated exampleProgram source.reverse).toMachine (embed exampleProgram source.reverse
      ⟨entry exampleProgram 8,sourceBanks (exampleResult source) []⟩)=none := by
  rw [step_embed,terminal exampleProgram _ 8 (Or.inr rfl)]
  rfl

theorem blank_halts (source : List Nat) :
    Halts (generated exampleProgram source.reverse).toMachine := by
  apply Part.dom_iff_mem.mpr
  exact ⟨_,StateTransition.mem_eval.mpr
    ⟨FlatInit.runFrom_reaches _ _ _ _ (blank_run source),blank_terminal source⟩⟩

theorem blank_source_correct (source : List Nat) :
    exampleCode.eval source=pure (exampleResult source) ∧
      Halts (generated exampleProgram source.reverse).toMachine ∧
      FlatInit.runFrom (generated exampleProgram source.reverse).toMachine
        ((4+4*(Words.encode source.reverse).length)+(2+programCost source []))
        ConjectureMachines.init=some (embed exampleProgram source.reverse
          ⟨entry exampleProgram 8,sourceBanks (exampleResult source) []⟩) := by
  exact ⟨example_eval source,blank_halts source,blank_run source⟩

theorem family_count (source : List Nat) :
    (generated exampleProgram source.reverse).states=
      62736+4*(Words.encode source.reverse).length := by
  rw [state_count]
  change 4638*9+462*21+4*(Words.encode source.reverse).length+11292=_
  omega

def exampleSource : List Nat := [3,0,2]
def exampleData : List Nat := exampleSource.reverse
def M : Machine 62780 2 := (generated exampleProgram exampleData).toMachine

theorem M_count : (generated exampleProgram exampleData).states=62780 := by
  simpa [exampleData,exampleSource,Words.encode,Words.word] using family_count exampleSource

theorem M_run : FlatInit.runFrom M 5268 ConjectureMachines.init=
    some (embed exampleProgram exampleData
      ⟨entry exampleProgram 8,sourceBanks [0,0,2,0,2] []⟩) := by
  simpa [M,exampleData,exampleSource,programCost,literalCost,bitCost,caseCost,predCost,
    caseArgument,exampleResult,branchCost,callCost,Call.callCost,returnCost,Call.returnCost,
    Call.lookupCost,Dispatch.lookupCost,Words.transferCost,Words.encode,Words.word] using
    blank_run exampleSource

theorem M_halts : Halts M := blank_halts exampleSource

theorem empty_count : (generated exampleProgram []).states=62736 := family_count []

theorem empty_blank_run : FlatInit.runFrom (generated exampleProgram []).toMachine
    2602 ConjectureMachines.init=some (embed exampleProgram []
      ⟨entry exampleProgram 8,sourceBanks [0] []⟩) := by
  simpa [programCost,literalCost,bitCost,caseCost,caseArgument,exampleResult,branchCost,
    callCost,Call.callCost,returnCost,Call.returnCost,Call.lookupCost,Dispatch.lookupCost,
    Words.transferCost,Words.encode,Words.word] using blank_run []

theorem zero_blank_run : FlatInit.runFrom (generated exampleProgram [2,0,0]).toMachine
    4194 ConjectureMachines.init=some (embed exampleProgram [2,0,0]
      ⟨entry exampleProgram 8,sourceBanks [0,0,2] []⟩) := by
  have h := blank_run [0,0,2]
  change FlatInit.runFrom (generated exampleProgram [2,0,0]).toMachine _
    ConjectureMachines.init=some (embed exampleProgram [2,0,0]
      ⟨entry exampleProgram 8,sourceBanks [0,0,2] []⟩) at h
  simpa [programCost,literalCost,bitCost,caseCost,caseArgument,exampleResult,branchCost,
    callCost,Call.callCost,returnCost,Call.returnCost,Call.lookupCost,Dispatch.lookupCost,
    Words.transferCost,Words.encode,Words.word] using h

def rows : List (List (Option (Bit × Dir × Fin 62780))) :=
  (List.finRange 62780).map fun state ↦ (List.finRange 2).map (M.transition state)

theorem table_cells (state : Fin 62780) (bit : Bit) :
    (Machine.ofRows rows).transition state bit=M.transition state bit :=
  Pred.table_cells_generic 62780 M state bit

theorem table_correct : Machine.ofRows rows=M := Pred.table_correct_generic 62780 M

end CatchUp.Machine.Cases
