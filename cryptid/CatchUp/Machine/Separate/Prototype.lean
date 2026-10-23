import CatchUp.Machine.Separate.Calls

namespace CatchUp.Machine.Separate
open Turing ConjectureMachines Compilation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem q_value (p : Fin 23) (s : Side) (b : Bit) (k : Fin 5) :
    (q p s b k).val = p.val*20+(if s then 10 else 0)+b.val*5+k.val := by
  cases s <;> simp [q,number,finProdFinEquiv,finTwoEquiv] <;> omega

theorem banks_nil : banks [] [] = Tape.mk₁ [] := by
  simp [banks,home,view,Tape.mk₂,Tape.mk',Tape.mk₁]

theorem boot (data frames : List Bit) :
    run 2 ⟨0,banks data frames⟩ = some ⟨q 2 false 1 1,banks data frames⟩ := by
  change run 2 ⟨q 0 false 0 0,banks data frames⟩ = _
  simp [run,FlatInit.runFrom,step,machine,q,banks,home,view,Tape.mk₂,Tape.mk',
    Tape.move,Tape.write]

theorem data_entry_step (s : Side) (b : Bit) (k : Fin 5) (T : Tape Bit) :
    step machine ⟨q 21 s b k,T⟩ = step machine ⟨q 10 false 0 0,T⟩ := by
  simp [step,machine,q,outward]

theorem data_from_entry (data frames : List Bit) (a : Bit)
    (s : Side) (b : Bit) (k : Fin 5) :
    run (4*data.length+12) ⟨q 21 s b k,banks (data++[a]) frames⟩ =
      some ⟨q 20 false a 0,banks data frames⟩ := by
  have result := pop_correct false data frames a 0 0
  simp only [home_swap,destination,show (0:Fin 5) ≠ 1 by decide,
    show (0:Fin 5) ≠ 2 by decide,show (0:Fin 5) ≠ 3 by decide,
    show (0:Fin 5) ≠ 4 by decide,↓reduceIte] at result
  rw [show 4*data.length+12 = (4*data.length+11)+1 by omega]
  change (step machine ⟨q 21 s b k,banks (data++[a]) frames⟩).bind
    (run (4*data.length+11)) = _
  rw [data_entry_step]
  exact result

/-- The finite demonstration pushes data, calls a returning subroutine, pops
the data and stops. The operational lemmas above do not bound stack lengths. -/
theorem body_run : run 42 ConjectureMachines.init =
    some ⟨q 20 false 1 0,banks [] []⟩ := by
  change run 42 ⟨0,Tape.mk₁ []⟩ = _
  rw [← banks_nil,show 42=2+(8+(20+12)) by rfl,run_add,boot,Option.bind_some]
  have pushed := push_correct false [] [] 1 1
  simp only [List.length_nil,Nat.mul_zero,Nat.zero_add,List.nil_append,
    home_swap,destination,↓reduceIte] at pushed
  have returned : run 20 ⟨q 2 true 0 3,banks [1] []⟩ =
      some ⟨q 21 true 0 4,banks [1] []⟩ := by
    simpa [entry] using call_return_correct [1] [] 0
  rw [run_add,pushed,Option.bind_some,run_add,returned,Option.bind_some]
  exact data_from_entry [] [] 1 true 0 4

abbrev body : BundledMachine 2 := ⟨460,machine⟩
/-- Explicitly write both zero separator cells and return to the origin.
The empty regions already consist of blanks; no nonzero data are assumed. -/
abbrev bits : Array Bit := #[0,0]
abbrev generated := FlatInit.initialise bits body
def M : Machine 464 2 := generated.toMachine

theorem state_count : generated.states = 464 := rfl

theorem initializes : FlatInit.runFrom M 4 ConjectureMachines.init =
    some (FlatInit.embed bits body ⟨0,banks [] []⟩) := by
  simpa [M,banks_nil,bits,Tape.mk₁,Tape.mk₂,Tape.mk'] using FlatInit.initialise_run bits body

theorem run_embed (n : Nat) (c : Cfg 460 2) :
    FlatInit.runFrom M n (FlatInit.embed bits body c) =
      (run n c).map (FlatInit.embed bits body) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    change (step (FlatInit.machine bits body) (FlatInit.embed bits body c)).bind _ = _
    rw [FlatInit.step_embed]
    cases h : step machine c with
    | none => simp [h,run,FlatInit.runFrom]
    | some c' => simpa [h,run,FlatInit.runFrom] using ih c'

theorem push_full (s : Side) (w other : List Bit) (b : Bit) (k : Fin 5) :
    FlatInit.runFrom M (4*w.length+8) (FlatInit.embed bits body ⟨q 2 s b k,home s w other⟩) =
      some (FlatInit.embed bits body ⟨destination s b k,home s (w++[b]) other⟩) := by
  rw [run_embed,push_correct,Option.map_some]

theorem pop_full (s : Side) (w other : List Bit) (a b : Bit) (k : Fin 5) :
    FlatInit.runFrom M (4*w.length+12)
      (FlatInit.embed bits body ⟨q 10 s b k,home s (w++[a]) other⟩) =
      some (FlatInit.embed bits body ⟨destination s a k,home s w other⟩) := by
  rw [run_embed,pop_correct,Option.map_some]

theorem call_return_full (data frames : List Bit) (address : Bit) :
    FlatInit.runFrom M (8*frames.length+20)
      (FlatInit.embed bits body ⟨q 2 true address 3,banks data frames⟩) =
      some (FlatInit.embed bits body ⟨entry address true address 4,banks data frames⟩) := by
  rw [run_embed,call_return_correct,Option.map_some]

theorem nested_returns_full (data frames : List Bit) (depth : Nat)
    (s : Side) (b : Bit) (k : Fin 5) :
    ∃ steps, FlatInit.runFrom M steps (FlatInit.embed bits body
      ⟨q 22 s b k,banks data (frames++[0]++List.replicate depth 1)⟩) =
      some (FlatInit.embed bits body ⟨q 21 true 0 4,banks data frames⟩) := by
  obtain ⟨steps,h⟩ := nested_returns data frames depth s b k
  exact ⟨steps,by rw [run_embed,h,Option.map_some]⟩

theorem full_add (m n : Nat) (c : Cfg 464 2) :
    FlatInit.runFrom M (m+n) c =
      (FlatInit.runFrom M m c).bind (FlatInit.runFrom M n) := by
  induction m generalizing c with
  | zero => simp [FlatInit.runFrom]
  | succ m ih => simp only [Nat.succ_add,FlatInit.runFrom,ih,Option.bind_assoc]

theorem full_run : FlatInit.runFrom M 46 ConjectureMachines.init =
    some (FlatInit.embed bits body ⟨q 20 false 1 0,banks [] []⟩) := by
  rw [show 46=4+42 by rfl,full_add,initializes,Option.bind_some,run_embed]
  rw [banks_nil]
  simpa only [banks_nil,ConjectureMachines.init,Option.map_some] using
    congrArg (Option.map (FlatInit.embed bits body)) body_run

theorem terminal : step M (FlatInit.embed bits body ⟨q 20 false 1 0,banks [] []⟩) = none := by
  change step (FlatInit.machine bits body) _ = _
  rw [FlatInit.step_embed]
  simp [body,step,machine,q]

theorem M_halts : Halts M := by
  apply Part.dom_iff_mem.mpr
  refine ⟨_,StateTransition.mem_eval.mpr ⟨FlatInit.runFrom_reaches M 46 _ _ full_run,terminal⟩⟩

/-- All 928 binary transition cells, including unused control combinations. -/
def rows : List (List (Option (Bit × Dir × Fin 464))) :=
  (List.finRange 464).map fun state ↦ (List.finRange 2).map (M.transition state)

theorem table_cells (state : Fin 464) (bit : Bit) :
    (Machine.ofRows rows).transition state bit = M.transition state bit := by
  decide +kernel +revert

theorem table_correct : Machine.ofRows rows = M :=
  congrArg Machine.mk (funext fun state ↦ funext fun bit ↦ table_cells state bit)

theorem table_length : rows.length = 464 := by simp [rows]

end CatchUp.Machine.Separate
