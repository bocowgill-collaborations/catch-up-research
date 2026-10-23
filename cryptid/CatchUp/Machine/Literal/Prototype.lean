import CatchUp.Machine.Literal.Initialization

namespace CatchUp.Machine.Literal
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem lift_value (p : Program) (old : Fin (Succ.states (base p))) :
    (lift p old).val=2+old.val := by
  simp [lift,number,layout,finSumFinEquiv]

theorem local_value (p : Program) (site : Fin (p.length+1)) (stage : Fin 9) (slot : Fin 462) :
    (localState p site stage slot).val=
      2+Succ.states (base p)+site.val*4158+stage.val*462+slot.val := by
  simp [localState,number,layout,finSumFinEquiv,finProdFinEquiv]
  omega

theorem literal_value (p : Program) (i : Fin (pool p).length) (old : Fin 460) :
    (literalNormal p i old).val=2+prefixStates p+i.val*462+old.val := by
  simp [literalNormal,number,finSumFinEquiv,finProdFinEquiv]
  omega

theorem boot (p : Program) (T : Tape Bit) :
    run p 2 ⟨0,T⟩=some ⟨entry p 0,T⟩ := by
  change run p 2 ⟨bootState p 0,T⟩=_
  simp [run,FlatInit.runFrom,step,boot_transition]

theorem literal_push_full (p : Program) (initial data frames : List Nat)
    (address n continuation : Nat) (h : p[address]?=some (.push n continuation)) :
    FlatInit.runFrom (generated p initial).toMachine (literalCost (Words.encode data) n)
      (embed p initial ⟨entry p address,Words.natBanks data frames⟩)=
      some (embed p initial ⟨entry p continuation,Words.natBanks (data++[n]) frames⟩) := by
  rw [run_embed,literal_push_nat p address n continuation h,Option.map_some]

theorem call_literal_full (p : Program) (initial data frames : List Nat)
    (target continuation n next : Nat) (hpush : p[target]?=some (.push n next))
    (hreturn : p[next]?=some .ret) :
    FlatInit.runFrom (generated p initial).toMachine
      (callCost data frames target continuation+literalCost (Words.encode data) n+
        returnCost (data++[n]) frames continuation)
      (embed p initial ⟨wordState p (Words.start false false),
        Words.natBanks (data++[target,continuation]) frames⟩)=
      some (embed p initial ⟨entry p continuation,Words.natBanks (data++[n]) frames⟩) := by
  rw [run_embed,call_literal_return p data frames target continuation n next hpush hreturn,
    Option.map_some]

/-- Only the working operand is initialized. The two call operands are created
by executed literal instructions after startup. -/
def exampleProgram : Program := [.push 3 1,.push 4 2,.call,.succ,.halt]
def input (n : Nat) : List Nat := [n]
def exampleData : List Nat := input 3

def programCost (n : Nat) := literalCost (Words.encode [n]) 3+
  (literalCost (Words.encode [n,3]) 4+
    (callCost [n] [] 3 4+succCost [] n+returnCost [n+1] [] 4))

theorem program_run (n : Nat) : run exampleProgram (programCost n)
    ⟨entry exampleProgram 0,Words.natBanks (input n) []⟩=
    some ⟨entry exampleProgram 4,Words.natBanks [n+1] []⟩ := by
  have h := pushes_call_successor_return exampleProgram [] [] n 0 1 2 3 4
    (by rfl) (by rfl) (by rfl) (by rfl)
  simpa [programCost,input,Words.encode] using h

theorem body_run (n : Nat) : run exampleProgram (2+programCost n)
    ⟨0,Words.natBanks (input n) []⟩=
    some ⟨entry exampleProgram 4,Words.natBanks [n+1] []⟩ := by
  rw [run_add,boot,Option.bind_some,program_run]

theorem blank_run (n : Nat) :
    FlatInit.runFrom (generated exampleProgram (input n)).toMachine
      ((4+4*(Words.encode (input n)).length)+(2+programCost n)) ConjectureMachines.init=
      some (embed exampleProgram (input n)
        ⟨entry exampleProgram 4,Words.natBanks [n+1] []⟩) := by
  rw [full_add,initializes,Option.bind_some,run_embed,body_run,Option.map_some]

theorem blank_terminal (n : Nat) :
    step (generated exampleProgram (input n)).toMachine (embed exampleProgram (input n)
      ⟨entry exampleProgram 4,Words.natBanks [n+1] []⟩)=none := by
  rw [step_embed,terminal exampleProgram _ 4 (Or.inr rfl)]
  rfl

theorem blank_halts (n : Nat) : Halts (generated exampleProgram (input n)).toMachine := by
  apply Part.dom_iff_mem.mpr
  exact ⟨_,StateTransition.mem_eval.mpr
    ⟨FlatInit.runFrom_reaches _ _ _ _ (blank_run n),blank_terminal n⟩⟩

theorem family_count (n : Nat) : (generated exampleProgram (input n)).states=38646+4*n := by
  have h := state_count exampleProgram (input n)
  simpa [exampleProgram,input,Words.encode,Words.word,pool,chunk,fragment,
    Nat.add_mul,Nat.mul_add,Nat.mul_comm,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

/-- The same fixed program emits another word on each visit. -/
def loopProgram (n : Nat) : Program := [.push n 0]

theorem blank_repeated (n k : Nat) :
    FlatInit.runFrom (generated (loopProgram n) []).toMachine (4+(2+bitCost [] (k*(n+2))))
      ConjectureMachines.init=
      some (embed (loopProgram n) []
        ⟨entry (loopProgram n) 0,Words.natBanks (List.replicate k n) []⟩) := by
  have repeated := repeated_push (loopProgram n) 0 n (by rfl) [] [] k
  have init := initializes (loopProgram n) []
  simp only [Words.encode,List.flatMap_nil,List.length_nil,Nat.mul_zero,Nat.add_zero] at init
  rw [full_add,init,Option.bind_some,run_embed,run_add,boot,Option.bind_some]
  simpa [Words.encode] using congrArg (Option.map (embed (loopProgram n) [])) repeated

def M : Machine 38658 2 := (generated exampleProgram exampleData).toMachine

theorem M_count : (generated exampleProgram exampleData).states=38658 := family_count 3

theorem M_run : FlatInit.runFrom M 2076 ConjectureMachines.init=
    some (embed exampleProgram exampleData
      ⟨entry exampleProgram 4,Words.natBanks [4] []⟩) := by
  simpa [M,exampleData,input,programCost,literalCost,bitCost,callCost,Call.callCost,
    returnCost,Call.returnCost,succCost,Call.lookupCost,Dispatch.lookupCost,
    Words.transferCost,Words.encode,Words.word] using blank_run 3

theorem M_terminal : step M (embed exampleProgram exampleData
    ⟨entry exampleProgram 4,Words.natBanks [4] []⟩)=none := blank_terminal 3

theorem M_halts : Halts M := blank_halts 3

def rows : List (List (Option (Bit × Dir × Fin 38658))) :=
  (List.finRange 38658).map fun state ↦ (List.finRange 2).map (M.transition state)

theorem table_cells (state : Fin 38658) (bit : Bit) :
    (Machine.ofRows rows).transition state bit=M.transition state bit :=
  Pred.table_cells_generic 38658 M state bit

theorem table_correct : Machine.ofRows rows=M := Pred.table_correct_generic 38658 M

end CatchUp.Machine.Literal
