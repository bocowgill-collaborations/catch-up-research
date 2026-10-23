import CatchUp.Machine.Call.Lookup

namespace CatchUp.Machine.Call
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

theorem entry_call (p : Program) :
    entry p (some .call)=wordState p (Words.start false false) := rfl
theorem entry_return (p : Program) :
    entry p (some .ret)=wordState p (Words.start true false) := rfl

def callCost (data frames : List Nat) (target continuation : Nat) :=
  Words.transferCost (Words.encode (data++[target])) (Words.encode frames) continuation+
    (2+lookupCost (Words.encode data) target)
def returnCost (data frames : List Nat) (continuation : Nat) :=
  Words.transferCost (Words.encode frames) (Words.encode data) continuation+
    (2+lookupCost (Words.encode data) continuation)

/-- Save the whole continuation, consume both operands and dispatch the target.
All program lengths, operands and earlier data/frames are arbitrary. -/
theorem call_correct (p : Program) (data frames : List Nat) (target continuation : Nat) :
    run p (callCost data frames target continuation)
      ⟨wordState p (Words.start false false),Words.natBanks (data++[target,continuation]) frames⟩ =
      some ⟨entry p p[target]?,Words.natBanks data (frames++[continuation])⟩ := by
  have outside : ¬afterReturn (Words.doneState (Words.ctx false true true)) := by
    simp [afterReturn,rightContext,Words.doneState,Words.ctx]
  have transfer := word_run_before p _ _ _ (Words.push_nat (data++[target]) frames continuation) outside
  simp only [wordEmbed] at transfer
  rw [callCost,run_add]
  simp only [List.append_assoc,List.cons_append,List.nil_append] at transfer
  rw [transfer,Option.bind_some,run_add,call_handoff,Option.bind_some,lookup_nat]

/-- Return can preserve an arbitrary callee-produced data stack, rather than
requiring it to equal the caller's data. Only the top saved continuation is consumed. -/
theorem return_correct (p : Program) (data frames : List Nat) (continuation : Nat) :
    run p (returnCost data frames continuation)
      ⟨wordState p (Words.start true false),Words.natBanks data (frames++[continuation])⟩ =
      some ⟨entry p p[continuation]?,Words.natBanks data frames⟩ := by
  have inside : rightContext (Words.start true false) := by
    change 1927≤(Words.start true false).val
    decide
  have transfer := word_run_right p _ _ _ (Words.return_correct data frames continuation) inside
  simp only [wordEmbed] at transfer
  rw [returnCost,run_add,transfer,Option.bind_some,run_add,return_handoff,Option.bind_some,lookup_nat]

/-- Arbitrary callee execution is permitted. The explicit hypothesis is its
actual finite run to return with the saved frame intact; callee termination
or frame preservation is not assumed for all arbitrary programs. -/
theorem call_callee_return (p : Program) (data result frames : List Nat)
    (target continuation calleeSteps : Nat)
    (callee : run p calleeSteps
      ⟨entry p p[target]?,Words.natBanks data (frames++[continuation])⟩ =
      some ⟨wordState p (Words.start true false),Words.natBanks result (frames++[continuation])⟩) :
    run p (callCost data frames target continuation+calleeSteps+returnCost result frames continuation)
      ⟨wordState p (Words.start false false),Words.natBanks (data++[target,continuation]) frames⟩ =
      some ⟨entry p p[continuation]?,Words.natBanks result frames⟩ := by
  rw [run_add,run_add,call_correct,Option.bind_some,callee,Option.bind_some,return_correct]

theorem call_return (p : Program) (data frames : List Nat) (target continuation : Nat)
    (h : p[target]?=some .ret) :
    run p (callCost data frames target continuation+returnCost data frames continuation)
      ⟨wordState p (Words.start false false),Words.natBanks (data++[target,continuation]) frames⟩ =
      some ⟨entry p p[continuation]?,Words.natBanks data frames⟩ := by
  rw [run_add,call_correct,Option.bind_some,h]
  exact return_correct p data frames continuation

theorem call_invalid (p : Program) (data frames : List Nat) (target continuation : Nat)
    (h : p.length≤target) :
    run p (callCost data frames target continuation)
      ⟨wordState p (Words.start false false),Words.natBanks (data++[target,continuation]) frames⟩ =
      some ⟨global p 3,Words.natBanks data (frames++[continuation])⟩ := by
  rw [call_correct,List.getElem?_eq_none h]
  rfl

theorem return_invalid (p : Program) (data frames : List Nat) (continuation : Nat)
    (h : p.length≤continuation) :
    run p (returnCost data frames continuation)
      ⟨wordState p (Words.start true false),Words.natBanks data (frames++[continuation])⟩ =
      some ⟨global p 3,Words.natBanks data frames⟩ := by
  rw [return_correct,List.getElem?_eq_none h]
  rfl

/-- Execute two real nested calls, the inner return and the outer return.
The inner continuation executes ret; the final outer continuation is unrestricted. -/
theorem nested_calls (p : Program) (data frames : List Nat)
    (outerTarget outerContinuation innerTarget innerContinuation : Nat)
    (outer : p[outerTarget]?=some .call) (inner : p[innerTarget]?=some .ret)
    (resume : p[innerContinuation]?=some .ret) :
    run p (callCost (data++[innerTarget,innerContinuation]) frames outerTarget outerContinuation+
      (callCost data (frames++[outerContinuation]) innerTarget innerContinuation+
      (returnCost data (frames++[outerContinuation]) innerContinuation+
        returnCost data frames outerContinuation)))
      ⟨wordState p (Words.start false false),
        Words.natBanks (data++[innerTarget,innerContinuation,outerTarget,outerContinuation]) frames⟩ =
      some ⟨entry p p[outerContinuation]?,Words.natBanks data frames⟩ := by
  have first := call_correct p (data++[innerTarget,innerContinuation]) frames outerTarget outerContinuation
  simp only [List.append_assoc,List.cons_append,List.nil_append] at first
  rw [run_add,first,Option.bind_some,outer,entry_call]
  rw [run_add,call_correct,Option.bind_some,inner,entry_return]
  rw [run_add,return_correct,Option.bind_some,resume,entry_return,return_correct]

end CatchUp.Machine.Call
