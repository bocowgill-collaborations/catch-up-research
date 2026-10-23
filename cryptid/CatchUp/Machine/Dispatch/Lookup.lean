import CatchUp.Machine.Dispatch.Routines

namespace CatchUp.Machine.Dispatch
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem after_header (p : Program) :
    after p 0 0=readStart p.length (payload p.length 0) := by
  simp [after]

theorem after_one (p : Program) (k : Nat) :
    after p (payload p.length k) 1=readStart p.length (payload p.length (k+1)) := by
  have h : min (min k p.length+1) p.length=min (k+1) p.length := by omega
  simp [after,payload,h]

theorem get_saturated (p : Program) (k : Nat) : p[min k p.length]?=p[k]? := by
  by_cases h : k<p.length
  · rw [Nat.min_eq_left (by omega)]
  · rw [Nat.min_eq_right (by omega),List.getElem?_eq_none (by omega),
      List.getElem?_eq_none (by omega)]

theorem after_zero (p : Program) (k : Nat) :
    after p (payload p.length k) 0=entry p.length p[k]? := by
  simp [after,payload,get_saturated]

def onesCost (u : List Bit) (n : Nat) := (n+1)*(4*u.length+2*n+14)
def lookupCost (u : List Bit) (n : Nat) := (n+2)*(4*u.length+2*n+16)

theorem ones_loop (p : Program) (u v : List Bit) (k n : Nat) :
    run p (onesCost u n)
      ⟨readStart p.length (payload p.length k),home false (u++[0]++List.replicate n 1) v⟩ =
      some ⟨entry p.length p[k+n]?,home false u v⟩ := by
  induction n generalizing k with
  | zero => simpa [onesCost,after_zero] using pop_bit p (payload p.length k) u v 0
  | succ n ih =>
    have first : run p (4*(u.length+1+n)+14)
        ⟨readStart p.length (payload p.length k),
          home false (u++[0]++List.replicate (n+1) 1) v⟩ =
        some ⟨readStart p.length (payload p.length (k+1)),
          home false (u++[0]++List.replicate n 1) v⟩ := by
      have h := pop_bit p (payload p.length k) (u++[0]++List.replicate n 1) v 1
      have len : (u++[0]++List.replicate n 1).length=u.length+1+n := by simp;omega
      rw [len,after_one] at h
      simpa only [List.replicate_succ',List.append_assoc] using h
    have cost : onesCost u (n+1)=(4*(u.length+1+n)+14)+onesCost u n := by
      simp only [onesCost]
      ring
    rw [cost,run_add,first,Option.bind_some]
    simpa only [show k+1+n=k+(n+1) by omega] using ih (k+1)

/-- Consume the recovered PC and select the actual entry for its instruction.
Every natural is handled: out-of-range addresses select the error control. -/
theorem lookup_correct (p : Program) (u v : List Bit) (address : Nat) :
    run p (lookupCost u address)
      ⟨readStart p.length 0,home false (u++Words.word address) v⟩ =
      some ⟨entry p.length p[address]?,home false u v⟩ := by
  have first : run p (4*(u.length+address+1)+14)
      ⟨readStart p.length 0,home false (u++Words.word address) v⟩ =
      some ⟨readStart p.length (payload p.length 0),
        home false (u++[0]++List.replicate address 1) v⟩ := by
    have h := pop_bit p 0 (u++[0]++List.replicate address 1) v 0
    have len : (u++[0]++List.replicate address 1).length=u.length+address+1 := by
      simp;omega
    rw [len,after_header] at h
    simpa only [Words.word,List.append_assoc,List.cons_append,List.nil_append] using h
  have cost : lookupCost u address=(4*(u.length+address+1)+14)+onesCost u address := by
    simp only [lookupCost,onesCost]
    ring
  rw [cost,run_add,first,Option.bind_some]
  simpa using ones_loop p u v 0 address

theorem lookup_nat (p : Program) (data frames : List Nat) (address : Nat) :
    run p (lookupCost (Words.encode data) address)
      ⟨readStart p.length 0,Words.natBanks (data++[address]) frames⟩ =
      some ⟨entry p.length p[address]?,Words.natBanks data frames⟩ := by
  simpa [Words.natBanks,Words.encode,List.flatMap_append,home_swap] using
    lookup_correct p (Words.encode data) (Words.encode frames) address

theorem lookup_valid (p : Program) (u v : List Bit) (address : Nat) (op : Instruction)
    (h : p[address]?=some op) :
    run p (lookupCost u address)
      ⟨readStart p.length 0,home false (u++Words.word address) v⟩ =
      some ⟨entry p.length (some op),home false u v⟩ := by
  rw [lookup_correct,h]

theorem lookup_out_of_range (p : Program) (u v : List Bit) (address : Nat)
    (h : p.length≤address) :
    run p (lookupCost u address)
      ⟨readStart p.length 0,home false (u++Words.word address) v⟩ =
      some ⟨global p.length 3,home false u v⟩ := by
  rw [lookup_correct,List.getElem?_eq_none h]
  rfl

theorem error_terminal (p : Program) (T : Tape Bit) :
    step (machine p) ⟨global p.length 3,T⟩=none := by
  simp [step,global_transition]

theorem halt_terminal (p : Program) (T : Tape Bit) :
    step (machine p) ⟨entry p.length (some .halt),T⟩=none := by
  simp [step,entry,global_transition]

theorem return_dispatch (p : Program) (data frames : List Nat) (address : Nat) :
    run p (Words.transferCost (Words.encode frames) (Words.encode data) address+
      (2+lookupCost (Words.encode data) address))
      ⟨wordState p.length (Words.start true false),
        Words.natBanks data (frames++[address])⟩ =
      some ⟨entry p.length p[address]?,Words.natBanks data frames⟩ := by
  have h := word_run p _ _ _ (Words.return_correct data frames address)
  simp only [wordEmbed] at h
  rw [run_add,h,Option.bind_some,run_add,return_handoff,Option.bind_some,lookup_nat]

theorem push_return_dispatch (p : Program) (data frames : List Nat) (address : Nat) :
    run p (2*Words.transferCost (Words.encode data) (Words.encode frames) address+2+
      (2+lookupCost (Words.encode data) address))
      ⟨wordState p.length (Words.start false false),
        Words.natBanks (data++[address]) frames⟩ =
      some ⟨entry p.length p[address]?,Words.natBanks data frames⟩ := by
  have h := word_run p _ _ _ (Words.call_return_correct data frames address)
  simp only [wordEmbed] at h
  rw [run_add,h,Option.bind_some,run_add,return_handoff,Option.bind_some,lookup_nat]

/-- Execute any finite sequence of return instructions selected by arbitrary
natural PCs. The final address can select any entry, including an error. -/
theorem unwind_returns (p : Program) (data frames : List Nat) (address : Nat)
    (pending : List Nat) (h : ∀ a ∈ pending, p[a]?=some .ret) :
    ∃ steps, run p steps
      ⟨wordState p.length (Words.start true false),
        Words.natBanks data (frames++[address]++pending.reverse)⟩ =
      some ⟨entry p.length p[address]?,Words.natBanks data frames⟩ := by
  induction pending with
  | nil =>
    exact ⟨_,by simpa using return_dispatch p data frames address⟩
  | cons next pending ih =>
    have hn : p[next]?=some .ret := h next (by simp)
    obtain ⟨steps,rest⟩ := ih (fun a ha ↦ h a (by simp [ha]))
    have first := return_dispatch p data (frames++[address]++pending.reverse) next
    rw [hn] at first
    refine ⟨(Words.transferCost (Words.encode (frames++[address]++pending.reverse))
      (Words.encode data) next+(2+lookupCost (Words.encode data) next))+steps,?_⟩
    simp only [List.append_assoc,entry] at first
    rw [run_add]
    simp only [List.reverse_cons,List.append_assoc]
    rw [first,Option.bind_some]
    simpa only [List.append_assoc] using rest

end CatchUp.Machine.Dispatch
