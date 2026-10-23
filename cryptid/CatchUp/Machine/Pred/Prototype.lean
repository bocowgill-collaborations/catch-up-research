import CatchUp.Machine.Pred.Initialization

namespace CatchUp.Machine.Pred
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem lift_value (p : Program) (old : Fin (Succ.states (base p))) :
    (lift p old).val=old.val := rfl

theorem local_value (p : Program) (site : Fin (p.length+1)) (stage : Fin 9) (slot : Fin 462) :
    (localState p site stage slot).val=
      Succ.states (base p)+site.val*4158+stage.val*462+slot.val := by
  simp [localState,number,finSumFinEquiv,finProdFinEquiv]
  omega

theorem boot (p : Program) (T : Tape Bit) :
    run p 2 ⟨0,T⟩=some ⟨wordState p (Words.start false false),T⟩ := by
  change run p 2 ⟨global p 0,T⟩=_
  simp [run,FlatInit.runFrom,step,global_transition,Succ.global_transition,Call.global_transition]

theorem predecessor_full (p : Program) (initial data frames : List Nat) (address z s n : Nat)
    (h : p[address]?=some (.pred z s)) :
    FlatInit.runFrom (generated p initial).toMachine (predCost (Words.encode data) n)
      (embed p initial ⟨entry p address,Words.natBanks (data++[n]) frames⟩) =
      some (embed p initial
        ⟨entry p (if n=0 then z else s),Words.natBanks (data++[n-1]) frames⟩) := by
  rw [run_embed,predecessor_nat p address z s h,Option.map_some]

theorem zero_test_full (p : Program) (initial data frames : List Nat) (address z s n : Nat)
    (h : p[address]?=some (.test z s)) :
    FlatInit.runFrom (generated p initial).toMachine (testCost (Words.encode data) n)
      (embed p initial ⟨entry p address,Words.natBanks (data++[n]) frames⟩) =
      some (embed p initial
        ⟨entry p (if n=0 then z else s),Words.natBanks (data++[n]) frames⟩) := by
  rw [run_embed,zero_test_nat p address z s h,Option.map_some]

/-- Zero returns directly; positives decrement, test the result, then return.
The two test branches use distinct return instructions. -/
def exampleProgram : Program := [.pred 1 2,.ret,.test 1 3,.ret,.halt]
def input (n : Nat) : List Nat := [n,0,4]
def exampleData : List Nat := input 3

def programCost (n : Nat) :=
  (callCost [n] [] 0 4+predCost [] n)+
    ((if n=0 then 0 else testCost [] (n-1))+returnCost [n-1] [] 4)

theorem program_run (n : Nat) : run exampleProgram (programCost n)
    ⟨wordState exampleProgram (Words.start false false),Words.natBanks (input n) []⟩ =
    some ⟨entry exampleProgram 4,Words.natBanks [n-1] []⟩ := by
  have first := call_predecessor_branch exampleProgram [] [] n 0 4 1 2 (by rfl)
  simp only [List.nil_append,Words.encode,List.flatMap_nil] at first
  change run exampleProgram (programCost n)
    ⟨wordState exampleProgram (Words.start false false),Words.natBanks [n,0,4] []⟩=_
  cases n with
  | zero =>
    simp only [programCost,↓reduceIte,Nat.zero_add]
    rw [run_add]
    simp only [↓reduceIte] at first
    rw [first,Option.bind_some,entry_return exampleProgram 1 (by rfl)]
    exact return_correct exampleProgram [0] [] 4
  | succ n =>
    have test := zero_test_nat exampleProgram 2 1 3 (by rfl) [] [4] n
    simp only [List.nil_append,Words.encode,List.flatMap_nil] at test
    have selected : exampleProgram[if n=0 then 1 else 3]?=some .ret := by split <;> rfl
    simp only [programCost,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel] at *
    rw [run_add,first,Option.bind_some,run_add,test,Option.bind_some,
      entry_return exampleProgram _ selected]
    exact return_correct exampleProgram [n] [] 4

theorem body_run (n : Nat) : run exampleProgram (2+programCost n)
    ⟨0,Words.natBanks (input n) []⟩ =
    some ⟨entry exampleProgram 4,Words.natBanks [n-1] []⟩ := by
  rw [run_add,boot,Option.bind_some,program_run]

theorem blank_run (n : Nat) :
    FlatInit.runFrom (generated exampleProgram (input n)).toMachine
      ((4+4*(Words.encode (input n)).length)+(2+programCost n)) ConjectureMachines.init =
      some (embed exampleProgram (input n)
        ⟨entry exampleProgram 4,Words.natBanks [n-1] []⟩) := by
  rw [full_add,initializes,Option.bind_some,run_embed,body_run,Option.map_some]

theorem blank_terminal (n : Nat) :
    step (generated exampleProgram (input n)).toMachine (embed exampleProgram (input n)
      ⟨entry exampleProgram 4,Words.natBanks [n-1] []⟩)=none := by
  rw [step_embed,terminal exampleProgram _ 4 (Or.inr rfl)]
  rfl

theorem blank_halts (n : Nat) : Halts (generated exampleProgram (input n)).toMachine := by
  apply Part.dom_iff_mem.mpr
  exact ⟨_,StateTransition.mem_eval.mpr
    ⟨FlatInit.runFrom_reaches _ _ _ _ (blank_run n),blank_terminal n⟩⟩

theorem family_count (n : Nat) : (generated exampleProgram (input n)).states=33594+4*n := by
  have h := state_count exampleProgram (input n)
  simpa [exampleProgram,input,Words.encode,Words.word,List.replicate_succ,
    Nat.add_mul,Nat.mul_add,Nat.mul_comm,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

def M : Machine 33606 2 := (generated exampleProgram exampleData).toMachine

theorem M_count : (generated exampleProgram exampleData).states=33606 := family_count 3

theorem M_run : FlatInit.runFrom M 1332 ConjectureMachines.init =
    some (embed exampleProgram exampleData
      ⟨entry exampleProgram 4,Words.natBanks [2] []⟩) := by
  simpa [M,exampleData,input,programCost,callCost,Call.callCost,returnCost,Call.returnCost,
    predCost,testCost,Call.lookupCost,Dispatch.lookupCost,Words.transferCost,
    Words.encode,Words.word] using blank_run 3

theorem M_terminal : step M (embed exampleProgram exampleData
    ⟨entry exampleProgram 4,Words.natBanks [2] []⟩)=none := blank_terminal 3

theorem M_halts : Halts M := blank_halts 3

theorem table_cells_generic (n : Nat) (m : Machine n 2) (state : Fin n) (bit : Bit) :
    (Machine.ofRows ((List.finRange n).map fun q ↦
      (List.finRange 2).map (m.transition q))).transition state bit=m.transition state bit := by
  fin_cases bit <;> simp [Machine.ofRows,List.getD_eq_getElem?_getD]

theorem table_correct_generic (n : Nat) (m : Machine n 2) :
    Machine.ofRows ((List.finRange n).map fun q ↦
      (List.finRange 2).map (m.transition q))=m :=
  congrArg Machine.mk (funext fun q ↦ funext fun b ↦ table_cells_generic n m q b)

def rows : List (List (Option (Bit × Dir × Fin 33606))) :=
  (List.finRange 33606).map fun state ↦ (List.finRange 2).map (M.transition state)

theorem table_cells (state : Fin 33606) (bit : Bit) :
    (Machine.ofRows rows).transition state bit=M.transition state bit := by
  exact table_cells_generic 33606 M state bit

theorem table_correct : Machine.ofRows rows=M :=
  table_correct_generic 33606 M

end CatchUp.Machine.Pred
