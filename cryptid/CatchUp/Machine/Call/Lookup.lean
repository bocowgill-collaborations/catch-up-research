import CatchUp.Machine.Call.Routines

namespace CatchUp.Machine.Call
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev lookupCost := Dispatch.lookupCost

theorem ones_loop (p : Program) (u v : List Bit) (k n : Nat) :
    run p (Dispatch.onesCost u n)
      ⟨readStart p (Dispatch.payload (base p).length k),
        home false (u++[0]++List.replicate n 1) v⟩ =
      some ⟨Dispatch.entry (base p).length (base p)[k+n]?,home false u v⟩ := by
  induction n generalizing k with
  | zero =>
    simpa [Dispatch.onesCost,Dispatch.after_zero] using
      pop_bit p (Dispatch.payload (base p).length k) u v 0
  | succ n ih =>
    have first := pop_bit p (Dispatch.payload (base p).length k)
      (u++[0]++List.replicate n 1) v 1
    have len : (u++[0]++List.replicate n 1).length=u.length+1+n := by simp;omega
    rw [len,Dispatch.after_one] at first
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
      some ⟨entry p p[address]?,home false u v⟩ := by
  have first := pop_bit p 0 (u++[0]++List.replicate address 1) v 0
  have first' : run p (4*(u.length+address+1)+14)
      ⟨readStart p 0,home false (u++Words.word address) v⟩ =
      some ⟨readStart p (Dispatch.payload (base p).length 0),
        home false (u++[0]++List.replicate address 1) v⟩ := by
    have len : (u++[0]++List.replicate address 1).length=u.length+address+1 := by simp;omega
    rw [len,Dispatch.after_header] at first
    simpa only [Words.word,List.append_assoc,List.cons_append,List.nil_append] using first
  have cost : lookupCost u address =
      (4*(u.length+address+1)+14)+Dispatch.onesCost u address := by
    simp only [lookupCost,Dispatch.lookupCost,Dispatch.onesCost]
    ring
  rw [cost,run_add,first',Option.bind_some]
  have finish := ones_loop p u v 0 address
  rw [Nat.zero_add,base_get] at finish
  exact finish

theorem lookup_nat (p : Program) (data frames : List Nat) (address : Nat) :
    run p (lookupCost (Words.encode data) address)
      ⟨readStart p 0,Words.natBanks (data++[address]) frames⟩ =
      some ⟨entry p p[address]?,Words.natBanks data frames⟩ := by
  simpa [Words.natBanks,Words.encode,List.flatMap_append,home_swap] using
    lookup_correct p (Words.encode data) (Words.encode frames) address

theorem lookup_invalid (p : Program) (u v : List Bit) (address : Nat) (h : p.length≤address) :
    run p (lookupCost u address)
      ⟨readStart p 0,home false (u++Words.word address) v⟩ =
      some ⟨global p 3,home false u v⟩ := by
  rw [lookup_correct,List.getElem?_eq_none h]
  rfl

theorem terminal (p : Program) (T : Tape Bit) (op : Option Instruction)
    (h : op=none ∨ op=some .halt) : step (machine p) ⟨entry p op,T⟩=none := by
  rcases h with rfl|rfl
  · change step (machine p) ⟨global p 3,T⟩=none
    simp [step,global_transition]
  · change step (machine p) ⟨global p 4,T⟩=none
    simp [step,global_transition]

theorem call_handoff (p : Program) (T : Tape Bit) :
    run p 2 ⟨wordState p (Words.doneState (Words.ctx false true true)),T⟩ =
      some ⟨readStart p 0,T⟩ := by
  have neq : Words.doneState (Words.ctx false true true)≠(2:Fin 3851) := by decide
  simp [run,FlatInit.runFrom,step,word_transition p _ _ neq,Dispatch.word_transition,
    Words.done_transition,word_two]

theorem return_handoff (p : Program) (T : Tape Bit) :
    run p 2 ⟨wordState p (Words.doneState (Words.ctx true true true)),T⟩ =
      some ⟨readStart p 0,T⟩ := by
  have neq : Words.doneState (Words.ctx true true true)≠(2:Fin 3851) := by decide
  simp [run,FlatInit.runFrom,step,word_transition p _ _ neq,Dispatch.word_transition,
    Words.done_transition,global_transition]

end CatchUp.Machine.Call
