import CatchUp.Machine.Cases.Source

namespace CatchUp.Machine.Cases
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

theorem entry_case (p : Program) (address z s : Nat)
    (h : p[address]?=some (.caseOf z s)) :
    entry p address=normal p (index p address) 0 (q 10 false 0 0) := by simp [entry,h]

theorem site_case (p : Program) (address z s : Nat)
    (h : p[address]?=some (.caseOf z s)) : caseSite p (index p address)=true := by
  simp [caseSite,index_lookup p address _ h]

theorem branch_case (p : Program) (address z s : Nat) (b : Bool)
    (h : p[address]?=some (.caseOf z s)) :
    branch p (index p address) b=entry p (if b then s else z) := by
  simp [branch,targets,index_lookup p address _ h]

theorem case_empty_boundary (p : Program) (site : Fin (p.length+1))
    (h : caseSite p site=true) (s : Side) (b : Bit) (k : Fin 5) (T : Tape Bit) :
    run p 2 ⟨normal p site 0 (q 19 s b k),T⟩=some ⟨branch p site false,T⟩ := by
  simp [run,FlatInit.runFrom,step,normal_transition,oldInstruction,Separate.machine,
    Separate.q,h,bridge_transition,next]

theorem case_empty_bits (p : Program) (address z s : Nat)
    (h : p[address]?=some (.caseOf z s)) (v : List Bit) :
    run p 8 ⟨entry p address,home false [] v⟩=some ⟨entry p z,home false [] v⟩ := by
  rw [entry_case p address z s h]
  have first := local_run p (index p address) 0 _ _ _ (Separate.pop_empty false v 0 0)
  simp only [primitiveEmbed] at first
  change run p (6+2) _=_
  rw [run_add,first,Option.bind_some,
    case_empty_boundary p (index p address) (site_case p address z s h),
    branch_case p address z s false h]
  rfl

theorem case_zero_bits (p : Program) (address z s : Nat)
    (h : p[address]?=some (.caseOf z s)) (u v : List Bit) :
    run p (8*u.length+32) ⟨entry p address,home false (u++Words.word 0) v⟩=
      some ⟨entry p z,home false u v⟩ := by
  have first := pop_local p (index p address) 0 (u++[0]) v 0
  have second := pop_local p (index p address) 1 u v 0
  simp only [next,↓reduceIte] at first
  have dest : next p (index p address) 1 0=entry p z := by
    simp [next,site_case p address z s h,branch_case p address z s false h]
  rw [dest] at second
  rw [show 8*u.length+32=(4*(u++[0]).length+14)+(4*u.length+14) by simp;omega,
    run_add,entry_case p address z s h]
  have bits : u++Words.word 0=(u++[0])++[0] := by simp [Words.word,List.append_assoc]
  rw [bits,first,Option.bind_some,second]

theorem case_positive_bits (p : Program) (address z s : Nat)
    (h : p[address]?=some (.caseOf z s)) (u v : List Bit) (n : Nat) :
    run p (predCost u (n+1)) ⟨entry p address,home false (u++Words.word (n+1)) v⟩=
      some ⟨entry p s,home false (u++Words.word n) v⟩ := by
  rw [entry_case p address z s h]
  simpa [branch_case p address z s true h] using
    positive_pred_bits p (index p address) u v n

def caseArgument : List Nat → List Nat
  | [] => []
  | 0::rest => rest
  | (n+1)::rest => n::rest
def caseTarget (z s : Nat) (source : List Nat) := if source.headI=0 then z else s
def caseCost : List Nat → Nat
  | [] => 8
  | 0::rest => 8*(Words.encode rest.reverse).length+32
  | (n+1)::rest => predCost (Words.encode rest.reverse) (n+1)

/-- Dispatch performs the source's argument transformation, including empty
input, before entering the actual selected branch. Every saved frame remains. -/
theorem case_source (p : Program) (address z s : Nat)
    (h : p[address]?=some (.caseOf z s)) (source frames : List Nat) :
    run p (caseCost source) ⟨entry p address,sourceBanks source frames⟩=
      some ⟨entry p (caseTarget z s source),sourceBanks (caseArgument source) frames⟩ := by
  cases source with
  | nil =>
    simpa [caseCost,caseTarget,caseArgument,sourceBanks,Words.natBanks,Words.encode,home_swap]
      using case_empty_bits p address z s h (Words.encode frames)
  | cons n rest =>
    cases n with
    | zero =>
      simpa [caseCost,caseTarget,caseArgument,sourceBanks,Words.natBanks,List.reverse_cons,
        Words.encode,List.flatMap_append,home_swap] using
        case_zero_bits p address z s h (Words.encode rest.reverse) (Words.encode frames)
    | succ n =>
      simpa [caseCost,caseTarget,caseArgument,sourceBanks,Words.natBanks,List.reverse_cons,
        Words.encode,List.flatMap_append,home_swap] using
        case_positive_bits p address z s h (Words.encode rest.reverse) (Words.encode frames) n

theorem case_source_eval (f g : Turing.ToPartrec.Code) (source : List Nat) :
    (Turing.ToPartrec.Code.case f g).eval source=
      (if source.headI=0 then f else g).eval (caseArgument source) := by
  cases source with
  | nil => rfl
  | cons n rest => cases n <;> rfl

theorem case_source_correct (p : Program) (address z s : Nat)
    (h : p[address]?=some (.caseOf z s)) (f g : Turing.ToPartrec.Code)
    (source frames : List Nat) :
    (Turing.ToPartrec.Code.case f g).eval source=
        (if source.headI=0 then f else g).eval (caseArgument source) ∧
      run p (caseCost source) ⟨entry p address,sourceBanks source frames⟩=
        some ⟨entry p (caseTarget z s source),sourceBanks (caseArgument source) frames⟩ := by
  exact ⟨case_source_eval f g source,case_source p address z s h source frames⟩

/-- Compose an actual selected-branch run with source case dispatch. Only the
selected partial source computation and callee need witnesses; the other branch
may be undefined. This is a constructor contract, not an assumed compiler. -/
theorem case_compose (p : Program) (address z s : Nat)
    (h : p[address]?=some (.caseOf z s)) (f g : Turing.ToPartrec.Code)
    (source result frames : List Nat) (steps : Nat)
    (value : result ∈ (if source.headI=0 then f else g).eval (caseArgument source))
    (callee : run p steps
      ⟨entry p (caseTarget z s source),sourceBanks (caseArgument source) frames⟩=
        some ⟨wordState p (Words.start true false),sourceBanks result frames⟩) :
    result ∈ (Turing.ToPartrec.Code.case f g).eval source ∧
      run p (caseCost source+steps) ⟨entry p address,sourceBanks source frames⟩=
        some ⟨wordState p (Words.start true false),sourceBanks result frames⟩ := by
  constructor
  · rwa [case_source_eval]
  · rw [run_add,case_source p address z s h source frames,Option.bind_some,callee]

theorem case_call_return (p : Program) (source result frames : List Nat)
    (target continuation z s steps : Nat) (h : p[target]?=some (.caseOf z s))
    (callee : run p steps
      ⟨entry p (caseTarget z s source),
        sourceBanks (caseArgument source) (frames++[continuation])⟩=
        some ⟨wordState p (Words.start true false),
          sourceBanks result (frames++[continuation])⟩) :
    run p (callCost source.reverse frames target continuation+(caseCost source+steps)+
      returnCost result.reverse frames continuation)
      ⟨wordState p (Words.start false false),
        Words.natBanks (source.reverse++[target,continuation]) frames⟩=
      some ⟨entry p continuation,sourceBanks result frames⟩ := by
  apply call_callee_return p source.reverse result.reverse frames target continuation
    (caseCost source+steps)
  rw [run_add]
  change (run p (caseCost source) ⟨entry p target,sourceBanks source _⟩).bind _=_
  rw [case_source p target z s h source (frames++[continuation]),Option.bind_some,callee]
  rfl

theorem generated_case_return (p : Program) (source result frames : List Nat)
    (first second callSite target continuation z s steps : Nat)
    (hfirst : p[first]?=some (.push target second))
    (hsecond : p[second]?=some (.push continuation callSite))
    (hcall : p[callSite]?=some .call) (hcase : p[target]?=some (.caseOf z s))
    (callee : run p steps
      ⟨entry p (caseTarget z s source),
        sourceBanks (caseArgument source) (frames++[continuation])⟩=
        some ⟨wordState p (Words.start true false),
          sourceBanks result (frames++[continuation])⟩) :
    run p (literalCost (Words.encode source.reverse) target+
      (literalCost (Words.encode (source.reverse++[target])) continuation+
        (callCost source.reverse frames target continuation+(caseCost source+steps)+
          returnCost result.reverse frames continuation)))
      ⟨entry p first,sourceBanks source frames⟩=
      some ⟨entry p continuation,sourceBanks result frames⟩ := by
  have first := literal_push_nat p first target second hfirst source.reverse frames
  have second := literal_push_nat p second continuation callSite hsecond
    (source.reverse++[target]) frames
  simp only [List.append_assoc,List.cons_append,List.nil_append] at second
  rw [run_add]
  change (run p _ ⟨entry p _,Words.natBanks source.reverse frames⟩).bind _=_
  rw [first,Option.bind_some,run_add,second,Option.bind_some,entry_call p callSite hcall,
    case_call_return p source result frames target continuation z s steps hcase callee]

theorem case_invalid_branch (p : Program) (address z s : Nat)
    (h : p[address]?=some (.caseOf z s)) (source frames : List Nat)
    (bad : p.length≤caseTarget z s source) :
    run p (caseCost source) ⟨entry p address,sourceBanks source frames⟩=
      some ⟨global p 3,sourceBanks (caseArgument source) frames⟩ := by
  rw [case_source p address z s h source frames]
  simp [entry,List.getElem?_eq_none bad]

theorem case_bad_closer (p : Program) (address z s : Nat)
    (h : p[address]?=some (.caseOf z s)) (u v : List Bit) :
    run p (4*u.length+14) ⟨entry p address,home false (u++[1]) v⟩=
      some ⟨global p 3,home false u v⟩ := by
  rw [entry_case p address z s h]
  simpa [next] using pop_local p (index p address) 0 u v 1

theorem case_payload_underflow (p : Program) (site : Fin (p.length+1)) (a : Bit) :
    (machine p).transition (normal p site 1 (q 19 false 0 0)) a=none := by
  simp [normal_transition,oldInstruction,Separate.machine,Separate.q]

theorem ordinary_empty_boundary (p : Program) (site : Fin (p.length+1))
    (ordinary : caseSite p site=false) (a : Bit) :
    (machine p).transition (normal p site 0 (q 19 false 0 0)) a=none := by
  simp [normal_transition,oldInstruction,Separate.machine,Separate.q,ordinary]

theorem case_return_empty (p : Program) (frames : List Nat) (target continuation z s : Nat)
    (h : p[target]?=some (.caseOf z s)) (resume : p[z]?=some .ret) :
    run p (callCost [] frames target continuation+(8+0)+returnCost [] frames continuation)
      ⟨wordState p (Words.start false false),Words.natBanks [target,continuation] frames⟩=
      some ⟨entry p continuation,sourceBanks [] frames⟩ := by
  apply case_call_return p [] [] frames target continuation z s 0 h
  simp [caseTarget,caseArgument,run,FlatInit.runFrom,entry_return p z resume]

theorem case_return_zero (p : Program) (rest frames : List Nat) (target continuation z s : Nat)
    (h : p[target]?=some (.caseOf z s)) (resume : p[z]?=some .ret) :
    run p (callCost (0::rest).reverse frames target continuation+(caseCost (0::rest)+0)+
      returnCost rest.reverse frames continuation)
      ⟨wordState p (Words.start false false),
        Words.natBanks ((0::rest).reverse++[target,continuation]) frames⟩=
      some ⟨entry p continuation,sourceBanks rest frames⟩ := by
  apply case_call_return p (0::rest) rest frames target continuation z s 0 h
  simp [caseTarget,caseArgument,run,FlatInit.runFrom,entry_return p z resume]

theorem case_return_positive (p : Program) (rest frames : List Nat)
    (n target continuation z s : Nat) (h : p[target]?=some (.caseOf z s))
    (resume : p[s]?=some .ret) :
    run p (callCost ((n+1)::rest).reverse frames target continuation+
      (caseCost ((n+1)::rest)+0)+returnCost (n::rest).reverse frames continuation)
      ⟨wordState p (Words.start false false),
        Words.natBanks (((n+1)::rest).reverse++[target,continuation]) frames⟩=
      some ⟨entry p continuation,sourceBanks (n::rest) frames⟩ := by
  apply case_call_return p ((n+1)::rest) (n::rest) frames target continuation z s 0 h
  simp [caseTarget,caseArgument,run,FlatInit.runFrom,entry_return p s resume]

end CatchUp.Machine.Cases
