import CatchUp.Machine.Pred.Inherited

namespace CatchUp.Machine.Pred
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

theorem predecessor_nat (p : Program) (address z s : Nat)
    (h : p[address]?=some (.pred z s)) (data frames : List Nat) (n : Nat) :
    run p (predCost (Words.encode data) n)
      ⟨entry p address,Words.natBanks (data++[n]) frames⟩ =
      some ⟨entry p (if n=0 then z else s),Words.natBanks (data++[n-1]) frames⟩ := by
  simpa [Words.natBanks,Words.encode,List.flatMap_append,home_swap] using
    predecessor_bits p address z s h (Words.encode data) (Words.encode frames) n

theorem zero_test_nat (p : Program) (address z s : Nat)
    (h : p[address]?=some (.test z s)) (data frames : List Nat) (n : Nat) :
    run p (testCost (Words.encode data) n)
      ⟨entry p address,Words.natBanks (data++[n]) frames⟩ =
      some ⟨entry p (if n=0 then z else s),Words.natBanks (data++[n]) frames⟩ := by
  simpa [Words.natBanks,Words.encode,List.flatMap_append,home_swap] using
    zero_test_bits p address z s h (Words.encode data) (Words.encode frames) n

/-- Conditional branching keeps the saved caller frame in place. The selected
branch executes next; it is not assumed to be a return or to terminate. -/
theorem call_predecessor_branch (p : Program) (data frames : List Nat)
    (n target continuation z s : Nat) (h : p[target]?=some (.pred z s)) :
    run p (callCost (data++[n]) frames target continuation+predCost (Words.encode data) n)
      ⟨wordState p (Words.start false false),
        Words.natBanks (data++[n,target,continuation]) frames⟩ =
      some ⟨entry p (if n=0 then z else s),
        Words.natBanks (data++[n-1]) (frames++[continuation])⟩ := by
  have first := call_correct p (data++[n]) frames target continuation
  simp only [List.append_assoc,List.cons_append,List.nil_append] at first
  rw [run_add,first,Option.bind_some,predecessor_nat p target z s h]

theorem call_zero_test_branch (p : Program) (data frames : List Nat)
    (n target continuation z s : Nat) (h : p[target]?=some (.test z s)) :
    run p (callCost (data++[n]) frames target continuation+testCost (Words.encode data) n)
      ⟨wordState p (Words.start false false),
        Words.natBanks (data++[n,target,continuation]) frames⟩ =
      some ⟨entry p (if n=0 then z else s),
        Words.natBanks (data++[n]) (frames++[continuation])⟩ := by
  have first := call_correct p (data++[n]) frames target continuation
  simp only [List.append_assoc,List.cons_append,List.nil_append] at first
  rw [run_add,first,Option.bind_some,zero_test_nat p target z s h]

theorem call_predecessor_return (p : Program) (data frames : List Nat)
    (n target continuation z s : Nat) (h : p[target]?=some (.pred z s))
    (resume : p[if n=0 then z else s]?=some .ret) :
    run p (callCost (data++[n]) frames target continuation+predCost (Words.encode data) n+
      returnCost (data++[n-1]) frames continuation)
      ⟨wordState p (Words.start false false),
        Words.natBanks (data++[n,target,continuation]) frames⟩ =
      some ⟨entry p continuation,Words.natBanks (data++[n-1]) frames⟩ := by
  rw [run_add,call_predecessor_branch p data frames n target continuation z s h,
    Option.bind_some,entry_return p _ resume,return_correct]

theorem call_zero_test_return (p : Program) (data frames : List Nat)
    (n target continuation z s : Nat) (h : p[target]?=some (.test z s))
    (resume : p[if n=0 then z else s]?=some .ret) :
    run p (callCost (data++[n]) frames target continuation+testCost (Words.encode data) n+
      returnCost (data++[n]) frames continuation)
      ⟨wordState p (Words.start false false),
        Words.natBanks (data++[n,target,continuation]) frames⟩ =
      some ⟨entry p continuation,Words.natBanks (data++[n]) frames⟩ := by
  rw [run_add,call_zero_test_branch p data frames n target continuation z s h,
    Option.bind_some,entry_return p _ resume,return_correct]

theorem predecessor_invalid_branch (p : Program) (address z s : Nat)
    (h : p[address]?=some (.pred z s)) (data frames : List Nat) (n : Nat)
    (bad : p.length≤(if n=0 then z else s)) :
    run p (predCost (Words.encode data) n)
      ⟨entry p address,Words.natBanks (data++[n]) frames⟩ =
      some ⟨global p 3,Words.natBanks (data++[n-1]) frames⟩ := by
  rw [predecessor_nat p address z s h]
  simp [entry,List.getElem?_eq_none bad]

theorem test_invalid_branch (p : Program) (address z s : Nat)
    (h : p[address]?=some (.test z s)) (data frames : List Nat) (n : Nat)
    (bad : p.length≤(if n=0 then z else s)) :
    run p (testCost (Words.encode data) n)
      ⟨entry p address,Words.natBanks (data++[n]) frames⟩ =
      some ⟨global p 3,Words.natBanks (data++[n]) frames⟩ := by
  rw [zero_test_nat p address z s h]
  simp [entry,List.getElem?_eq_none bad]

/-- Compose a nested conditional call, selected return and outer return.
All earlier frames, including the outer continuation during the inner call,
are arbitrary and are preserved until their corresponding return. -/
theorem nested_predecessor (p : Program) (data frames : List Nat)
    (n outerTarget outerContinuation innerTarget innerContinuation z s : Nat)
    (outer : p[outerTarget]?=some .call) (inner : p[innerTarget]?=some (.pred z s))
    (resume : p[if n=0 then z else s]?=some .ret)
    (unwind : p[innerContinuation]?=some .ret) :
    run p (callCost (data++[n,innerTarget,innerContinuation]) frames outerTarget outerContinuation+
      ((callCost (data++[n]) (frames++[outerContinuation]) innerTarget innerContinuation+
        predCost (Words.encode data) n+
        returnCost (data++[n-1]) (frames++[outerContinuation]) innerContinuation)+
        returnCost (data++[n-1]) frames outerContinuation))
      ⟨wordState p (Words.start false false),
        Words.natBanks (data++[n,innerTarget,innerContinuation,outerTarget,outerContinuation]) frames⟩ =
      some ⟨entry p outerContinuation,Words.natBanks (data++[n-1]) frames⟩ := by
  have first := call_correct p (data++[n,innerTarget,innerContinuation]) frames
    outerTarget outerContinuation
  have second := call_predecessor_return p data (frames++[outerContinuation]) n
    innerTarget innerContinuation z s inner resume
  simp only [List.append_assoc,List.cons_append,List.nil_append] at first
  rw [run_add,first,Option.bind_some,entry_call p _ outer,run_add,second,Option.bind_some,
    entry_return p _ unwind,return_correct]

theorem malformed_pred_closer (p : Program) (site : Fin (p.length+1)) (u v : List Bit) :
    run p (4*u.length+14)
      ⟨normal p site 0 (q 10 false 0 0),home false (u++[1]) v⟩=
      some ⟨global p 3,home false u v⟩ := by
  simpa [next] using pop_local p site 0 u v 1

theorem malformed_test_closer (p : Program) (site : Fin (p.length+1)) (u v : List Bit) :
    run p (4*u.length+14)
      ⟨normal p site 2 (q 10 false 0 0),home false (u++[1]) v⟩=
      some ⟨global p 3,home false u v⟩ := by
  simpa [next] using pop_local p site 2 u v 1

end CatchUp.Machine.Pred
