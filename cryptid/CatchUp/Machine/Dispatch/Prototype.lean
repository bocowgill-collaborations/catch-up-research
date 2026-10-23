import CatchUp.Machine.Dispatch.Lookup

namespace CatchUp.Machine.Dispatch
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem global_value (length : Nat) (q : Fin 5) : (global length q).val=q.val := rfl
theorem word_value (length : Nat) (q : Fin 3851) : (wordState length q).val=5+q.val := by
  simp [wordState,number,finSumFinEquiv]
theorem local_value (length : Nat) (phase : Fin (length+2)) (q : Fin 480) :
    (localState length phase q).val=3856+phase.val*480+q.val := by
  simp [localState,number,finSumFinEquiv,finProdFinEquiv]
  omega

abbrev body (p : Program) : BundledMachine 2 := ⟨states p.length,machine p⟩
abbrev inputBits := Words.inputBits
abbrev generated (p : Program) (address : Nat) := FlatInit.initialise (inputBits address) (body p)

/-- Every program-table control is paid in the body; no program tape is preloaded. -/
theorem state_count (p : Program) (address : Nat) :
    (generated p address).states=480*p.length+4*address+4828 := by
  rw [FlatInit.initialise_states,Words.input_size]
  change (5+(3851+(p.length+2)*480))+2*(2*address+6)=_
  ring

theorem initializes (p : Program) (address : Nat) :
    FlatInit.runFrom (generated p address).toMachine (4*address+12)
      ConjectureMachines.init =
      some (FlatInit.embed (inputBits address) (body p)
        ⟨0,home true (Words.word address) []⟩) := by
  have h := FlatInit.initialise_run (inputBits address) (body p)
  have count : 2*(inputBits address).size=4*address+12 := by rw [Words.input_size];omega
  conv at h => lhs; arg 2; rw [count]
  rw [Words.input_tape] at h
  exact h

theorem boot (p : Program) (T : Tape Bit) :
    run p 2 ⟨0,T⟩=some ⟨wordState p.length (Words.start true false),T⟩ := by
  change run p 2 ⟨global p.length 0,T⟩=_
  simp [run,FlatInit.runFrom,step,global_transition]

def bodySteps (address : Nat) :=
  2+(Words.transferCost [] [] address+(2+lookupCost [] address))

theorem body_run (p : Program) (address : Nat) :
    run p (bodySteps address) ⟨0,home true (Words.word address) []⟩ =
      some ⟨entry p.length p[address]?,Words.natBanks [] []⟩ := by
  rw [bodySteps,run_add,boot,Option.bind_some]
  simpa [Words.natBanks,Words.encode,banks] using return_dispatch p [] [] address

theorem run_embed (p : Program) (address steps : Nat) (c : Cfg (states p.length) 2) :
    FlatInit.runFrom (generated p address).toMachine steps
      (FlatInit.embed (inputBits address) (body p) c) =
      (run p steps c).map (FlatInit.embed (inputBits address) (body p)) := by
  induction steps generalizing c with
  | zero => rfl
  | succ steps ih =>
    change (step (FlatInit.machine (inputBits address) (body p))
      (FlatInit.embed (inputBits address) (body p) c)).bind _=_
    rw [FlatInit.step_embed]
    cases h : step (machine p) c with
    | none => simp [h,run,FlatInit.runFrom]
    | some c' => simpa [h,run,FlatInit.runFrom] using ih c'

theorem full_add (p : Program) (address m n : Nat) (c : Cfg (generated p address).states 2) :
    FlatInit.runFrom (generated p address).toMachine (m+n) c =
      (FlatInit.runFrom (generated p address).toMachine m c).bind
        (FlatInit.runFrom (generated p address).toMachine n) := by
  induction m generalizing c with
  | zero => simp [FlatInit.runFrom]
  | succ m ih => simp only [Nat.succ_add,FlatInit.runFrom,ih,Option.bind_assoc]

theorem full_run (p : Program) (address : Nat) :
    FlatInit.runFrom (generated p address).toMachine ((4*address+12)+bodySteps address)
      ConjectureMachines.init =
      some (FlatInit.embed (inputBits address) (body p)
        ⟨entry p.length p[address]?,Words.natBanks [] []⟩) := by
  rw [full_add,initializes,Option.bind_some,run_embed,body_run,Option.map_some]

theorem lookup_full (p : Program) (input : Nat) (u v : List Bit) (address : Nat) :
    FlatInit.runFrom (generated p input).toMachine (lookupCost u address)
      (FlatInit.embed (inputBits input) (body p)
        ⟨readStart p.length 0,home false (u++Words.word address) v⟩) =
      some (FlatInit.embed (inputBits input) (body p)
        ⟨entry p.length p[address]?,home false u v⟩) := by
  rw [run_embed,lookup_correct,Option.map_some]

theorem return_dispatch_full (p : Program) (input : Nat) (data frames : List Nat) (address : Nat) :
    FlatInit.runFrom (generated p input).toMachine
      (Words.transferCost (Words.encode frames) (Words.encode data) address+
        (2+lookupCost (Words.encode data) address))
      (FlatInit.embed (inputBits input) (body p)
        ⟨wordState p.length (Words.start true false),
          Words.natBanks data (frames++[address])⟩) =
      some (FlatInit.embed (inputBits input) (body p)
        ⟨entry p.length p[address]?,Words.natBanks data frames⟩) := by
  rw [run_embed,return_dispatch,Option.map_some]

theorem unwind_returns_full (p : Program) (input : Nat) (data frames : List Nat)
    (address : Nat) (pending : List Nat) (h : ∀ a ∈ pending,p[a]?=some .ret) :
    ∃ steps, FlatInit.runFrom (generated p input).toMachine steps
      (FlatInit.embed (inputBits input) (body p)
        ⟨wordState p.length (Words.start true false),
          Words.natBanks data (frames++[address]++pending.reverse)⟩) =
      some (FlatInit.embed (inputBits input) (body p)
        ⟨entry p.length p[address]?,Words.natBanks data frames⟩) := by
  obtain ⟨steps,hsteps⟩ := unwind_returns p data frames address pending h
  exact ⟨steps,by rw [run_embed,hsteps,Option.map_some]⟩

def exampleProgram : Program := [.ret,.push,.ret,.halt]
def M : Machine 6760 2 := (generated exampleProgram 3).toMachine

theorem M_count : (generated exampleProgram 3).states=6760 := by
  simpa [exampleProgram] using state_count exampleProgram 3

theorem M_run : FlatInit.runFrom M 338 ConjectureMachines.init =
    some (FlatInit.embed (inputBits 3) (body exampleProgram)
      ⟨entry exampleProgram.length (some .halt),Words.natBanks [] []⟩) := by
  simpa [M,bodySteps,Words.transferCost,lookupCost,exampleProgram] using full_run exampleProgram 3

theorem M_terminal : step M
    (FlatInit.embed (inputBits 3) (body exampleProgram)
      ⟨entry exampleProgram.length (some .halt),Words.natBanks [] []⟩)=none := by
  change step (FlatInit.machine (inputBits 3) (body exampleProgram)) _=none
  rw [FlatInit.step_embed]
  simp [body,halt_terminal]

theorem M_halts : Halts M := by
  apply Part.dom_iff_mem.mpr
  refine ⟨_,StateTransition.mem_eval.mpr
    ⟨FlatInit.runFrom_reaches _ _ _ _ M_run,M_terminal⟩⟩

def rows : List (List (Option (Bit × Dir × Fin 6760))) :=
  (List.finRange 6760).map fun state ↦ (List.finRange 2).map (M.transition state)

theorem table_cells (state : Fin 6760) (bit : Bit) :
    (Machine.ofRows rows).transition state bit=M.transition state bit := by
  fin_cases bit <;> simp [Machine.ofRows,rows,List.getD_eq_getElem?_getD]

theorem table_correct : Machine.ofRows rows=M :=
  congrArg Machine.mk (funext fun state ↦ funext fun bit ↦ table_cells state bit)

end CatchUp.Machine.Dispatch
