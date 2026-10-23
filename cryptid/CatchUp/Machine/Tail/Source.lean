import CatchUp.Machine.Tail.Discard
import Mathlib.Computability.TuringMachine.Config

namespace CatchUp.Machine.Tail
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

/-- Source head is stack top. Frames retain the established bottom-first order. -/
def sourceBanks (source frames : List Nat) := Words.natBanks source.reverse frames
def sourceCost : List Nat → Nat
  | [] => 8
  | n::rest => discardCost (Words.encode rest.reverse) n

theorem source_banks_injective (source frames source' frames' : List Nat)
    (h : sourceBanks source frames=sourceBanks source' frames') :
    source=source' ∧ frames=frames' := by
  obtain ⟨hd,hf⟩ := Words.nat_banks_injective _ _ _ _ h
  exact ⟨List.reverse_injective hd,hf⟩

theorem tail_source (p : Program) (address : Nat) (h : p[address]?=some .tail)
    (source frames : List Nat) :
    run p (sourceCost source) ⟨entry p address,sourceBanks source frames⟩=
      some ⟨wordState p (Words.start true false),sourceBanks source.tail frames⟩ := by
  cases source with
  | nil => exact discard_empty_nat p address h frames
  | cons n rest =>
    simpa [sourceCost,sourceBanks,List.reverse_cons] using
      discard_nat p address h rest.reverse frames n

/-- Literal source semantics, including empty input, paired with the actual
binary run. This is a primitive compiler contract, not a full-source simulation. -/
theorem tail_source_correct (p : Program) (address : Nat) (h : p[address]?=some .tail)
    (source frames : List Nat) :
    Turing.ToPartrec.Code.tail.eval source=pure source.tail ∧
      run p (sourceCost source) ⟨entry p address,sourceBanks source frames⟩=
        some ⟨wordState p (Words.start true false),sourceBanks source.tail frames⟩ := by
  exact ⟨rfl,tail_source p address h source frames⟩

theorem call_tail_return (p : Program) (source frames : List Nat) (target continuation : Nat)
    (h : p[target]?=some .tail) :
    run p (callCost source.reverse frames target continuation+sourceCost source+
      returnCost source.tail.reverse frames continuation)
      ⟨wordState p (Words.start false false),
        Words.natBanks (source.reverse++[target,continuation]) frames⟩=
      some ⟨entry p continuation,sourceBanks source.tail frames⟩ := by
  exact call_callee_return p source.reverse source.tail.reverse frames target continuation
    (sourceCost source) (tail_source p target h source (frames++[continuation]))

theorem generated_tail_return (p : Program) (source frames : List Nat)
    (first second callSite target continuation : Nat)
    (hfirst : p[first]?=some (.push target second))
    (hsecond : p[second]?=some (.push continuation callSite))
    (hcall : p[callSite]?=some .call) (htail : p[target]?=some .tail) :
    run p (literalCost (Words.encode source.reverse) target+
      (literalCost (Words.encode (source.reverse++[target])) continuation+
        (callCost source.reverse frames target continuation+sourceCost source+
          returnCost source.tail.reverse frames continuation)))
      ⟨entry p first,sourceBanks source frames⟩=
      some ⟨entry p continuation,sourceBanks source.tail frames⟩ := by
  have a := literal_push_nat p first target second hfirst source.reverse frames
  have b := literal_push_nat p second continuation callSite hsecond
    (source.reverse++[target]) frames
  simp only [List.append_assoc,List.cons_append,List.nil_append] at b
  rw [run_add]
  change (run p _ ⟨entry p first,Words.natBanks source.reverse frames⟩).bind _=_
  rw [a,Option.bind_some,run_add,b,Option.bind_some,entry_call p callSite hcall,
    call_tail_return p source frames target continuation htail]

def repeatedCost (source : List Nat) (frames : List Nat)
    (target continuation : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => literalCost (Words.encode source.reverse) target+
      (literalCost (Words.encode (source.reverse++[target])) continuation+
        (callCost source.reverse frames target continuation+sourceCost source+
          returnCost source.tail.reverse frames continuation))+
      repeatedCost source.tail frames target continuation k

/-- One fixed program repeatedly calls the shared callee. The theorem includes
more calls than source elements: `.tail []=[]`, without consuming a frame. -/
theorem repeated_source_tail (p : Program) (source frames : List Nat)
    (first second callSite target : Nat)
    (hfirst : p[first]?=some (.push target second))
    (hsecond : p[second]?=some (.push first callSite))
    (hcall : p[callSite]?=some .call) (htail : p[target]?=some .tail) (k : Nat) :
    run p (repeatedCost source frames target first k) ⟨entry p first,sourceBanks source frames⟩=
      some ⟨entry p first,sourceBanks (source.drop k) frames⟩ := by
  induction k generalizing source with
  | zero => rfl
  | succ k ih =>
    rw [repeatedCost,run_add,
      generated_tail_return p source frames first second callSite target first
      hfirst hsecond hcall htail,Option.bind_some,ih]
    congr 3
    cases source <;> simp

end CatchUp.Machine.Tail
