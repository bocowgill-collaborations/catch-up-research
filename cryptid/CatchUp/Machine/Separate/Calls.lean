import CatchUp.Machine.Separate.Operations

namespace CatchUp.Machine.Separate
open Turing ConjectureMachines Compilation
set_option backward.isDefEq.respectTransparency false

/-- Both banks are bottom first. Data grows left; saved return addresses grow right. -/
def banks (data frames : List Bit) := home true frames data

theorem home_swap (data frames : List Bit) : home false data frames = banks data frames := by
  simp [home,banks,view,mirror,Tape.mk₂,Tape.mk']

def entry (target : Bit) (s : Side) (b : Bit) (k : Fin 5) : Fin 460 :=
  if target=0 then q 21 s b k else q 22 s b k
def callTag (target : Bit) : Fin 5 := if target=0 then 2 else 3

theorem call_correct (data frames : List Bit) (address target : Bit) :
    run (4*frames.length+8) ⟨q 2 true address (callTag target),banks data frames⟩ =
      some ⟨entry target true address (callTag target),banks data (frames++[address])⟩ := by
  have h := push_correct true frames data address (callTag target)
  by_cases ht : target=0 <;> simpa [banks,destination,entry,callTag,ht] using h

theorem return_correct (data frames : List Bit) (address : Bit) :
    run (4*frames.length+12) ⟨q 10 true 0 4,banks data (frames++[address])⟩ =
      some ⟨entry address true address 4,banks data frames⟩ := by
  simpa [banks,destination,entry] using pop_correct true frames data address 0 4

theorem return_entry_step (s : Side) (b : Bit) (k : Fin 5) (T : Tape Bit) :
    step machine ⟨q 22 s b k,T⟩ = step machine ⟨q 10 true 0 4,T⟩ := by
  simp [step,machine,q,outward]

theorem return_from_entry (data frames : List Bit) (address : Bit)
    (s : Side) (b : Bit) (k : Fin 5) :
    run (4*frames.length+12) ⟨q 22 s b k,banks data (frames++[address])⟩ =
      some ⟨entry address true address 4,banks data frames⟩ := by
  rw [show 4*frames.length+12 = (4*frames.length+11)+1 by omega]
  simp only [run,FlatInit.runFrom,return_entry_step]
  exact return_correct data frames address

theorem call_return_correct (data frames : List Bit) (address : Bit) :
    run (8*frames.length+20) ⟨q 2 true address 3,banks data frames⟩ =
      some ⟨entry address true address 4,banks data frames⟩ := by
  have hcall := call_correct data frames address 1
  simp only [callTag,entry,show (1:Bit) ≠ 0 by decide,↓reduceIte] at hcall
  rw [show 8*frames.length+20 = (4*frames.length+8)+(4*frames.length+12) by omega,
    run_add,hcall,Option.bind_some,return_from_entry]

/-- Every number of nested pending returns is unwound in LIFO order. Existing
frames and the entire data region are preserved, with no bound on either. -/
theorem nested_returns (data frames : List Bit) (depth : Nat)
    (s : Side) (b : Bit) (k : Fin 5) :
    ∃ steps, run steps
      ⟨q 22 s b k,banks data (frames++[0]++List.replicate depth 1)⟩ =
      some ⟨q 21 true 0 4,banks data frames⟩ := by
  induction depth generalizing s b k with
  | zero =>
    refine ⟨4*frames.length+12,?_⟩
    simpa [entry] using return_from_entry data frames 0 s b k
  | succ depth ih =>
    obtain ⟨steps,hsteps⟩ := ih true 1 4
    let pending := frames++[0]++List.replicate depth 1
    refine ⟨(4*pending.length+12)+steps,?_⟩
    have unwind := return_from_entry data pending 1 s b k
    simp only [entry,show (1:Bit) ≠ 0 by decide,↓reduceIte] at unwind
    simpa only [pending,List.replicate_succ',List.append_assoc] using
      (show run ((4*pending.length+12)+steps)
        ⟨q 22 s b k,banks data (pending++[1])⟩ =
          some ⟨q 21 true 0 4,banks data frames⟩ by
        rw [run_add,unwind,Option.bind_some]
        exact hsteps)

end CatchUp.Machine.Separate
