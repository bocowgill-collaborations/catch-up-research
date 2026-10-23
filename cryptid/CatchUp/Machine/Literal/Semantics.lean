import CatchUp.Machine.Literal.Lookup

namespace CatchUp.Machine.Literal
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

theorem entry_call (p : Program) (address : Nat) (h : p[address]?=some .call) :
    entry p address=wordState p (Words.start false false) := by simp [entry,h]
theorem entry_return (p : Program) (address : Nat) (h : p[address]?=some .ret) :
    entry p address=wordState p (Words.start true false) := by simp [entry,h]
theorem entry_successor (p : Program) (address : Nat) (h : p[address]?=some .succ) :
    entry p address=succNormal p 0 (q 10 false 0 0) := by simp [entry,h]
theorem entry_pred (p : Program) (address z s : Nat) (h : p[address]?=some (.pred z s)) :
    entry p address=normal p (index p address) 0 (q 10 false 0 0) := by simp [entry,h]
theorem entry_test (p : Program) (address z s : Nat) (h : p[address]?=some (.test z s)) :
    entry p address=normal p (index p address) 2 (q 10 false 0 0) := by simp [entry,h]

theorem index_lookup (p : Program) (address : Nat) (op : Instruction)
    (h : p[address]?=some op) : p[(index p address).val]?=some op := by
  have ha : address<p.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at h
    contradiction
  simpa [index,Nat.min_eq_left (Nat.le_of_lt ha)] using h

theorem branch_pred (p : Program) (address z s : Nat) (b : Bool)
    (h : p[address]?=some (.pred z s)) :
    branch p (index p address) b=entry p (if b then s else z) := by
  simp [branch,targets,index_lookup p address _ h]

theorem branch_test (p : Program) (address z s : Nat) (b : Bool)
    (h : p[address]?=some (.test z s)) :
    branch p (index p address) b=entry p (if b then s else z) := by
  simp [branch,targets,index_lookup p address _ h]

abbrev callCost := Call.callCost
abbrev returnCost := Call.returnCost

theorem call_correct (p : Program) (data frames : List Nat) (target continuation : Nat) :
    run p (callCost data frames target continuation)
      ⟨wordState p (Words.start false false),Words.natBanks (data++[target,continuation]) frames⟩ =
      some ⟨entry p target,Words.natBanks data (frames++[continuation])⟩ := by
  have outside : ¬Call.afterReturn (Words.doneState (Words.ctx false true true)) := by
    simp [Call.afterReturn,Call.rightContext,Words.doneState,Words.ctx]
  have transfer := word_run_before p _ _ _ (Words.push_nat (data++[target]) frames continuation) outside
  simp only [wordEmbed] at transfer
  rw [callCost,Call.callCost,run_add]
  simp only [List.append_assoc,List.cons_append,List.nil_append] at transfer
  rw [transfer,Option.bind_some,run_add,call_handoff,Option.bind_some,lookup_nat]

theorem return_correct (p : Program) (data frames : List Nat) (continuation : Nat) :
    run p (returnCost data frames continuation)
      ⟨wordState p (Words.start true false),Words.natBanks data (frames++[continuation])⟩ =
      some ⟨entry p continuation,Words.natBanks data frames⟩ := by
  have inside : Call.rightContext (Words.start true false) := by
    change 1927≤(Words.start true false).val
    decide
  have transfer := word_run_right p _ _ _ (Words.return_correct data frames continuation) inside
  simp only [wordEmbed] at transfer
  rw [returnCost,Call.returnCost,run_add,transfer,Option.bind_some,run_add,return_handoff,
    Option.bind_some,lookup_nat]

/-- Only actual finite callee execution is composed; frame preservation and
termination are premises for arbitrary callees, proved below for the new operations. -/
theorem call_callee_return (p : Program) (data result frames : List Nat)
    (target continuation steps : Nat)
    (callee : run p steps ⟨entry p target,Words.natBanks data (frames++[continuation])⟩ =
      some ⟨wordState p (Words.start true false),Words.natBanks result (frames++[continuation])⟩) :
    run p (callCost data frames target continuation+steps+returnCost result frames continuation)
      ⟨wordState p (Words.start false false),Words.natBanks (data++[target,continuation]) frames⟩ =
      some ⟨entry p continuation,Words.natBanks result frames⟩ := by
  rw [run_add,run_add,call_correct,Option.bind_some,callee,Option.bind_some,return_correct]

theorem call_return (p : Program) (data frames : List Nat) (target continuation : Nat)
    (h : p[target]?=some .ret) :
    run p (callCost data frames target continuation+returnCost data frames continuation)
      ⟨wordState p (Words.start false false),Words.natBanks (data++[target,continuation]) frames⟩ =
      some ⟨entry p continuation,Words.natBanks data frames⟩ := by
  rw [run_add,call_correct,Option.bind_some,entry_return p target h]
  exact return_correct p data frames continuation

theorem call_invalid (p : Program) (data frames : List Nat) (target continuation : Nat)
    (h : p.length≤target) :
    run p (callCost data frames target continuation)
      ⟨wordState p (Words.start false false),Words.natBanks (data++[target,continuation]) frames⟩ =
      some ⟨global p 3,Words.natBanks data (frames++[continuation])⟩ := by
  rw [call_correct]
  simp [entry,List.getElem?_eq_none h]

theorem return_invalid (p : Program) (data frames : List Nat) (continuation : Nat)
    (h : p.length≤continuation) :
    run p (returnCost data frames continuation)
      ⟨wordState p (Words.start true false),Words.natBanks data (frames++[continuation])⟩ =
      some ⟨global p 3,Words.natBanks data frames⟩ := by
  rw [return_correct]
  simp [entry,List.getElem?_eq_none h]

end CatchUp.Machine.Literal
