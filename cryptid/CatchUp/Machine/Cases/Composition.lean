import CatchUp.Machine.Cases.Push

namespace CatchUp.Machine.Cases
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

/-- Neither call operand is preloaded: two executed literal instructions create
both complete natural words, then the real call saves and dispatches them. -/
theorem pushes_dynamic_call (p : Program) (first second callSite target continuation : Nat)
    (hfirst : p[first]?=some (.push target second))
    (hsecond : p[second]?=some (.push continuation callSite))
    (hcall : p[callSite]?=some .call) (data frames : List Nat) :
    run p (literalCost (Words.encode data) target+
      (literalCost (Words.encode (data++[target])) continuation+
        callCost data frames target continuation))
      ⟨entry p first,Words.natBanks data frames⟩=
      some ⟨entry p target,Words.natBanks data (frames++[continuation])⟩ := by
  have a := literal_push_nat p first target second hfirst data frames
  have b := literal_push_nat p second continuation callSite hsecond (data++[target]) frames
  simp only [List.append_assoc,List.cons_append,List.nil_append] at b
  rw [run_add,a,Option.bind_some,run_add,b,Option.bind_some,
    entry_call p callSite hcall,call_correct]

/-- A literal may execute inside a dynamically selected callee and return its
new word through a saved continuation; earlier words/frames remain arbitrary. -/
theorem call_literal_return (p : Program) (data frames : List Nat)
    (target continuation n next : Nat) (hpush : p[target]?=some (.push n next))
    (hreturn : p[next]?=some .ret) :
    run p (callCost data frames target continuation+literalCost (Words.encode data) n+
      returnCost (data++[n]) frames continuation)
      ⟨wordState p (Words.start false false),
        Words.natBanks (data++[target,continuation]) frames⟩=
      some ⟨entry p continuation,Words.natBanks (data++[n]) frames⟩ := by
  have callee := literal_push_nat p target n next hpush data (frames++[continuation])
  rw [entry_return p next hreturn] at callee
  exact call_callee_return p data (data++[n]) frames target continuation
    (literalCost (Words.encode data) n) callee

theorem nested_literal (p : Program) (data frames : List Nat)
    (outerTarget outerContinuation innerTarget innerContinuation n next : Nat)
    (outer : p[outerTarget]?=some .call) (inner : p[innerTarget]?=some (.push n next))
    (resume : p[next]?=some .ret) (unwind : p[innerContinuation]?=some .ret) :
    run p (callCost (data++[innerTarget,innerContinuation]) frames outerTarget outerContinuation+
      ((callCost data (frames++[outerContinuation]) innerTarget innerContinuation+
        literalCost (Words.encode data) n+
        returnCost (data++[n]) (frames++[outerContinuation]) innerContinuation)+
        returnCost (data++[n]) frames outerContinuation))
      ⟨wordState p (Words.start false false),
        Words.natBanks (data++[innerTarget,innerContinuation,outerTarget,outerContinuation])
          frames⟩=
      some ⟨entry p outerContinuation,Words.natBanks (data++[n]) frames⟩ := by
  have first := call_correct p (data++[innerTarget,innerContinuation]) frames
    outerTarget outerContinuation
  have second := call_literal_return p data (frames++[outerContinuation]) innerTarget
    innerContinuation n next inner resume
  simp only [List.append_assoc,List.cons_append,List.nil_append] at first
  rw [run_add,first,Option.bind_some,entry_call p _ outer,run_add,second,Option.bind_some,
    entry_return p _ unwind,return_correct]

theorem pushes_call_successor_return (p : Program) (data frames : List Nat)
    (value first second callSite target continuation : Nat)
    (hfirst : p[first]?=some (.push target second))
    (hsecond : p[second]?=some (.push continuation callSite))
    (hcall : p[callSite]?=some .call) (hsucc : p[target]?=some .succ) :
    run p (literalCost (Words.encode (data++[value])) target+
      (literalCost (Words.encode (data++[value,target])) continuation+
        (callCost (data++[value]) frames target continuation+succCost (Words.encode data) value+
          returnCost (data++[value+1]) frames continuation)))
      ⟨entry p first,Words.natBanks (data++[value]) frames⟩=
      some ⟨entry p continuation,Words.natBanks (data++[value+1]) frames⟩ := by
  have a := literal_push_nat p first target second hfirst (data++[value]) frames
  have b := literal_push_nat p second continuation callSite hsecond (data++[value,target]) frames
  simp only [List.append_assoc,List.cons_append,List.nil_append] at a b
  rw [run_add,a,Option.bind_some,run_add,b,Option.bind_some,entry_call p _ hcall]
  exact call_successor_return p data frames value target continuation hsucc

/-- One fixed instruction can reach arbitrarily large data stacks. No extra
control or preloaded word is supplied for the repetition count k. -/
theorem repeated_push (p : Program) (address n : Nat) (h : p[address]?=some (.push n address))
    (data frames : List Nat) (k : Nat) :
    run p (bitCost (Words.encode data) (k*(n+2))) ⟨entry p address,Words.natBanks data frames⟩=
      some ⟨entry p address,Words.natBanks (data++List.replicate k n) frames⟩ := by
  induction k generalizing data with
  | zero => simp [bitCost,run,FlatInit.runFrom]
  | succ k ih =>
    have len : (Words.encode (data++[n])).length=(Words.encode data).length+n+2 := by
      simp [Words.encode,Words.word,List.flatMap_append]
      omega
    have cost : bitCost (Words.encode data) ((k+1)*(n+2))=
        literalCost (Words.encode data) n+bitCost (Words.encode (data++[n])) (k*(n+2)) := by
      simp only [literalCost,bitCost,len]
      ring
    rw [cost,run_add,literal_push_nat p address n address h,Option.bind_some,ih]
    simp [List.replicate_succ,List.append_assoc]

end CatchUp.Machine.Cases
