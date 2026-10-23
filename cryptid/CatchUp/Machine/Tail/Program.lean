import CatchUp.Machine.Literal.Prototype

namespace CatchUp.Machine.Tail
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

inductive Instruction where
  | halt | call | ret | succ | tail
  | pred (zeroTarget positiveTarget : Nat)
  | test (zeroTarget positiveTarget : Nat)
  | push (value continuation : Nat)
  deriving DecidableEq, Repr

def Instruction.lower : Instruction → Succ.Instruction
  | .halt => .halt | .call => .call | .ret => .ret | .succ => .succ
  | .tail | .pred _ _ | .test _ _ | .push _ _ => .halt
abbrev Program := List Instruction
def base (p : Program) : Succ.Program := p.map Instruction.lower
abbrev oldLength (p : Program) := (Call.base (Succ.base (base p))).length

abbrev Cell := Bit × Option Nat
/-- The final zero records the actual continuation. Earlier bits advance in
this finite pool. Every cell receives a counted primitive-control context. -/
def fragment (n continuation : Nat) : List Cell :=
  (0::List.replicate n 1).map (fun b ↦ (b,none))++[(0,some continuation)]
def chunk : Instruction → List Cell
  | .push n continuation => fragment n continuation
  | _ => []
def pool (p : Program) : List Cell := p.flatMap chunk
def offset (p : Program) (address : Nat) := (pool (p.take address)).length

theorem fragment_length (n continuation : Nat) : (fragment n continuation).length=n+2 := by
  simp [fragment]

theorem pool_at (p : Program) (address : Nat) (op : Instruction) (h : p[address]?=some op) :
    pool p=pool (p.take address)++chunk op++pool (p.drop (address+1)) := by
  induction p generalizing address with
  | nil => simp at h
  | cons head tail ih =>
    cases address with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at h
      subst op
      simp [pool]
    | succ address =>
      have htail : tail[address]?=some op := by simpa using h
      have rest := ih address htail
      simpa [pool,List.take_succ_cons,List.drop_succ_cons,List.append_assoc] using
        congrArg (fun w ↦ chunk head++w) rest

end CatchUp.Machine.Tail
