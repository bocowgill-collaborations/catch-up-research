import CatchUp.Machine.Words.Calls

namespace CatchUp.Machine.Words
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem wire_length (w : List Bit) : (wire w).length=2*w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [ih];omega

abbrev body : BundledMachine 2 := ⟨3851,machine⟩
/-- The input natural address, both word delimiters, bit markers and zero
origin/separator cells are all emitted by the paid blank-tape initializer. -/
abbrev inputBits (n : Nat) : Array Bit := (0::0::wire (word n)).toArray
abbrev generated (n : Nat) := FlatInit.initialise (inputBits n) body

theorem input_size (n : Nat) : (inputBits n).size=2*n+6 := by
  simp [inputBits,wire_length];omega

theorem state_count (n : Nat) : (generated n).states=4*n+3863 := by
  rw [FlatInit.initialise_states,input_size]
  change 3851+2*(2*n+6)=_
  omega

theorem input_tape (n : Nat) : Tape.mk₁ (inputBits n).toList=home true (word n) [] := by
  simp [home,view,Tape.mk₁,Tape.mk₂,Tape.mk']

theorem initializes (n : Nat) : FlatInit.runFrom (generated n).toMachine (4*n+12)
    ConjectureMachines.init =
      some (FlatInit.embed (inputBits n) body ⟨0,home true (word n) []⟩) := by
  have h := FlatInit.initialise_run (inputBits n) body
  have count : 2*(inputBits n).size=4*n+12 := by rw [input_size];omega
  conv at h => lhs; arg 2; rw [count]
  rw [input_tape] at h
  exact h

theorem boot (T : Tape Bit) :
    run 2 ⟨0,T⟩=some ⟨start true false,T⟩ := by
  have zero (a : Bit) : machine.transition 0 a=some (a,.right,1) := rfl
  have one (a : Bit) : machine.transition 1 a=some (a,.left,start true false) := rfl
  simp [run,FlatInit.runFrom,step,zero,one]

theorem body_run (n : Nat) :
    run (2+transferCost [] [] n) ⟨0,home true (word n) []⟩ =
      some ⟨doneState (ctx true true true),home true [] (word n)⟩ := by
  rw [run_add,boot,Option.bind_some]
  simpa using word_transfer true [] [] n

theorem run_embed (n steps : Nat) (c : Cfg 3851 2) :
    FlatInit.runFrom (generated n).toMachine steps (FlatInit.embed (inputBits n) body c) =
      (run steps c).map (FlatInit.embed (inputBits n) body) := by
  induction steps generalizing c with
  | zero => rfl
  | succ steps ih =>
    change (step (FlatInit.machine (inputBits n) body) (FlatInit.embed (inputBits n) body c)).bind _ = _
    rw [FlatInit.step_embed]
    cases h : step machine c with
    | none => simp [h,run,FlatInit.runFrom]
    | some c' => simpa [h,run,FlatInit.runFrom] using ih c'

theorem full_add (n m k : Nat) (c : Cfg (generated n).states 2) :
    FlatInit.runFrom (generated n).toMachine (m+k) c =
      (FlatInit.runFrom (generated n).toMachine m c).bind
        (FlatInit.runFrom (generated n).toMachine k) := by
  induction m generalizing c with
  | zero => simp [FlatInit.runFrom]
  | succ m ih => simp only [Nat.succ_add,FlatInit.runFrom,ih,Option.bind_assoc]

theorem full_run (n : Nat) : FlatInit.runFrom (generated n).toMachine
    ((4*n+12)+(2+transferCost [] [] n)) ConjectureMachines.init =
      some (FlatInit.embed (inputBits n) body
        ⟨doneState (ctx true true true),home true [] (word n)⟩) := by
  rw [full_add,initializes,Option.bind_some,run_embed,body_run,Option.map_some]

theorem terminal (n : Nat) : step (generated n).toMachine
    (FlatInit.embed (inputBits n) body
      ⟨doneState (ctx true true true),home true [] (word n)⟩)=none := by
  change step (FlatInit.machine (inputBits n) body) _ = _
  rw [FlatInit.step_embed]
  simp [body,step,done_transition]

theorem generated_halts (n : Nat) : (generated n).Halts := by
  apply Part.dom_iff_mem.mpr
  refine ⟨_,StateTransition.mem_eval.mpr
    ⟨FlatInit.runFrom_reaches _ _ _ _ (full_run n),terminal n⟩⟩

def M : Machine 3875 2 := (generated 3).toMachine
theorem M_count : (generated 3).states=3875 := state_count 3
theorem M_run : FlatInit.runFrom M 226 ConjectureMachines.init =
    some (FlatInit.embed (inputBits 3) body
      ⟨doneState (ctx true true true),home true [] (word 3)⟩) := by
  simpa [M,transferCost] using full_run 3
theorem M_halts : Halts M := generated_halts 3

theorem word_transfer_full (input : Nat) (s : Bool) (u v : List Bit) (n : Nat) :
    FlatInit.runFrom (generated input).toMachine (transferCost u v n)
      (FlatInit.embed (inputBits input) body ⟨start s false,home s (u++word n) v⟩) =
      some (FlatInit.embed (inputBits input) body
        ⟨doneState (ctx s true true),home s u (v++word n)⟩) := by
  rw [run_embed,word_transfer,Option.map_some]

theorem call_return_full (input : Nat) (data frames : List Nat) (address : Nat) :
    FlatInit.runFrom (generated input).toMachine
      (2*transferCost (encode data) (encode frames) address+2)
      (FlatInit.embed (inputBits input) body
        ⟨start false false,natBanks (data++[address]) frames⟩) =
      some (FlatInit.embed (inputBits input) body
        ⟨doneState (ctx true true true),natBanks (data++[address]) frames⟩) := by
  rw [run_embed,call_return_correct,Option.map_some]

def rows : List (List (Option (Bit × Dir × Fin 3875))) :=
  (List.finRange 3875).map fun state ↦ (List.finRange 2).map (M.transition state)

theorem table_cells (state : Fin 3875) (bit : Bit) :
    (Machine.ofRows rows).transition state bit=M.transition state bit := by
  fin_cases bit <;> simp [Machine.ofRows,rows,List.getD_eq_getElem?_getD]

theorem table_correct : Machine.ofRows rows=M :=
  congrArg Machine.mk (funext fun state ↦ funext fun bit ↦ table_cells state bit)

end CatchUp.Machine.Words
