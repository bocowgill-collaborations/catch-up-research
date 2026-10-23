import CatchUp.Machine.Tail.Routines

namespace CatchUp.Machine.Tail
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev lookupCost := Dispatch.lookupCost

theorem after_header (p : Program) :
    after p 0 0=readStart p (Dispatch.payload (oldLength p) 0) := by
  simp [after]

theorem after_one (p : Program) (k : Nat) :
    after p (Dispatch.payload (oldLength p) k) 1=
      readStart p (Dispatch.payload (oldLength p) (k+1)) := by
  have h : min (min k (oldLength p)+1) (oldLength p)=
      min (k+1) (oldLength p) := by omega
  simp [after,Dispatch.payload,h]

theorem entry_saturated (p : Program) (k : Nat) : entry p (min k p.length)=entry p k := by
  by_cases h : k<p.length
  · rw [Nat.min_eq_left (by omega)]
  · simp [entry,Nat.min_eq_right (by omega : p.length≤k),
      List.getElem?_eq_none (by omega : p.length≤k)]

theorem after_zero (p : Program) (k : Nat) :
    after p (Dispatch.payload (oldLength p) k) 0=entry p k := by
  simp [after,Dispatch.payload,base_length,entry_saturated]

theorem ones_loop (p : Program) (u v : List Bit) (k n : Nat) :
    run p (Dispatch.onesCost u n)
      ⟨readStart p (Dispatch.payload (oldLength p) k),
        home false (u++[0]++List.replicate n 1) v⟩ =
      some ⟨entry p (k+n),home false u v⟩ := by
  induction n generalizing k with
  | zero =>
    simpa [Dispatch.onesCost,after_zero] using
      pop_bit p (Dispatch.payload (oldLength p) k) u v 0
  | succ n ih =>
    have first := pop_bit p (Dispatch.payload (oldLength p) k)
      (u++[0]++List.replicate n 1) v 1
    have len : (u++[0]++List.replicate n 1).length=u.length+1+n := by simp;omega
    rw [len,after_one] at first
    have cost : Dispatch.onesCost u (n+1) =
        (4*(u.length+1+n)+14)+Dispatch.onesCost u n := by
      simp only [Dispatch.onesCost]
      ring
    rw [cost,run_add]
    simp only [List.replicate_succ',List.append_assoc] at *
    rw [first,Option.bind_some]
    simpa only [show k+1+n=k+(n+1) by omega] using ih (k+1)

theorem lookup_correct (p : Program) (u v : List Bit) (address : Nat) :
    run p (lookupCost u address)
      ⟨readStart p 0,home false (u++Words.word address) v⟩ =
      some ⟨entry p address,home false u v⟩ := by
  have first := pop_bit p 0 (u++[0]++List.replicate address 1) v 0
  have first' : run p (4*(u.length+address+1)+14)
      ⟨readStart p 0,home false (u++Words.word address) v⟩ =
      some ⟨readStart p (Dispatch.payload (oldLength p) 0),
        home false (u++[0]++List.replicate address 1) v⟩ := by
    have len : (u++[0]++List.replicate address 1).length=u.length+address+1 := by simp;omega
    rw [len,after_header] at first
    simpa only [Words.word,List.append_assoc,List.cons_append,List.nil_append] using first
  have cost : lookupCost u address =
      (4*(u.length+address+1)+14)+Dispatch.onesCost u address := by
    simp only [lookupCost,Dispatch.lookupCost,Dispatch.onesCost]
    ring
  rw [cost,run_add,first',Option.bind_some]
  have finish := ones_loop p u v 0 address
  rw [Nat.zero_add] at finish
  exact finish

theorem lookup_nat (p : Program) (data frames : List Nat) (address : Nat) :
    run p (lookupCost (Words.encode data) address)
      ⟨readStart p 0,Words.natBanks (data++[address]) frames⟩ =
      some ⟨entry p address,Words.natBanks data frames⟩ := by
  simpa [Words.natBanks,Words.encode,List.flatMap_append,home_swap] using
    lookup_correct p (Words.encode data) (Words.encode frames) address

theorem lookup_invalid (p : Program) (u v : List Bit) (address : Nat) (h : p.length≤address) :
    run p (lookupCost u address)
      ⟨readStart p 0,home false (u++Words.word address) v⟩ =
      some ⟨global p 3,home false u v⟩ := by
  rw [lookup_correct]
  simp [entry,List.getElem?_eq_none h]

theorem terminal (p : Program) (T : Tape Bit) (address : Nat)
    (h : p[address]?=none ∨ p[address]?=some .halt) :
    step (machine p) ⟨entry p address,T⟩=none := by
  rcases h with h|h <;>
    simp [entry,h,step,global_transition,Succ.global_transition,Call.global_transition]

theorem call_handoff (p : Program) (T : Tape Bit) :
    run p 2 ⟨wordState p (Words.doneState (Words.ctx false true true)),T⟩ =
      some ⟨readStart p 0,T⟩ := by
  have neq : Words.doneState (Words.ctx false true true)≠(2:Fin 3851) := by decide
  simp [run,FlatInit.runFrom,step,word_transition,Succ.word_transition,
    Call.word_transition (Succ.base (base p)) _ _ neq,Dispatch.word_transition,
    Words.done_transition,Call.word_two]

theorem return_handoff (p : Program) (T : Tape Bit) :
    run p 2 ⟨wordState p (Words.doneState (Words.ctx true true true)),T⟩ =
      some ⟨readStart p 0,T⟩ := by
  have neq : Words.doneState (Words.ctx true true true)≠(2:Fin 3851) := by decide
  simp [run,FlatInit.runFrom,step,word_transition,Succ.word_transition,
    Call.word_transition (Succ.base (base p)) _ _ neq,Dispatch.word_transition,
    Words.done_transition,global_transition,Succ.global_transition,Call.global_transition]

end CatchUp.Machine.Tail
