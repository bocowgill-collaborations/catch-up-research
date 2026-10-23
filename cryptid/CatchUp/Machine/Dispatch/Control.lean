import CatchUp.Machine.Words.Prototype

namespace CatchUp.Machine.Dispatch
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

/-- The table names actual entries in the existing word machine. `push` keeps
that machine's immediate-return continuation; it is not a general call. -/
inductive Instruction where
  | halt | push | ret
  deriving DecidableEq, Repr

abbrev Program := List Instruction
abbrev states (length : Nat) := 5+(3851+(length+2)*480)
abbrev Control (length : Nat) := Fin 5 ⊕ (Fin 3851 ⊕ (Fin (length+2) × Fin 480))

def number (length : Nat) : Control length ≃ Fin (states length) :=
  ((Equiv.refl _).sumCongr
    (((Equiv.refl _).sumCongr finProdFinEquiv).trans finSumFinEquiv)).trans
      finSumFinEquiv

def global (length : Nat) (q : Fin 5) : Fin (states length) := number length (.inl q)
def wordState (length : Nat) (q : Fin 3851) : Fin (states length) :=
  number length (.inr (.inl q))
def localState (length : Nat) (phase : Fin (length+2)) (q : Fin 480) :
    Fin (states length) := number length (.inr (.inr (phase,q)))
def normal (length : Nat) (phase : Fin (length+2)) (old : Fin 460) :
    Fin (states length) := localState length phase ⟨old.val,by have := old.isLt;omega⟩
def bounce (length : Nat) (phase : Fin (length+2)) (attr : Fin 20) :
    Fin (states length) := localState length phase ⟨460+attr.val,by have := attr.isLt;omega⟩

/-- Phase zero consumes the last delimiter; phase k+1 counts k payload ones. -/
def payload (length k : Nat) : Fin (length+2) :=
  ⟨min k length+1,by omega⟩
def readStart (length : Nat) (phase : Fin (length+2)) : Fin (states length) :=
  normal length phase (q 10 false 0 0)

def entry (length : Nat) : Option Instruction → Fin (states length)
  | none => global length 3
  | some .halt => global length 4
  | some .push => wordState length (Words.start false false)
  | some .ret => wordState length (Words.start true false)

def after (p : Program) (phase : Fin (p.length+2)) (b : Bit) : Fin (states p.length) :=
  if phase.val=0 then
    if b=0 then readStart p.length (payload p.length 0) else global p.length 3
  else if b=1 then readStart p.length (payload p.length phase.val)
  else entry p.length p[phase.val-1]?

def oldInstruction (p : Program) (phase : Fin (p.length+2)) (old : Fin 460) (a : Bit) :
    Option (Bit × Dir × Fin (states p.length)) :=
  match Separate.machine.transition old a with
  | some (w,d,n) => some (w,d,normal p.length phase n)
  | none =>
    let (part,s,b,k) := Separate.number.symm old
    if part=20 then some (a,.right,bounce p.length phase (Words.attrs (s,b,k))) else none

/-- Program instructions are stored in counted finite control, not an oracle.
The complete natural PC is read from tape with a saturating in-range counter. -/
def machine (p : Program) : Machine (states p.length) 2 where
  transition state a :=
    match (number p.length).symm state with
    | .inl q =>
      if q=0 then some (a,.right,global p.length 1)
      else if q=1 then some (a,.left,wordState p.length (Words.start true false))
      else if q=2 then some (a,.left,readStart p.length 0)
      else none
    | .inr (.inl old) =>
      match Words.machine.transition old a with
      | some (w,d,n) => some (w,d,wordState p.length n)
      | none =>
        if old=Words.doneState (Words.ctx true true true) then
          some (a,.right,global p.length 2) else none
    | .inr (.inr (phase,slot)) =>
      if h : slot.val<460 then oldInstruction p phase ⟨slot.val,h⟩ a
      else
        let attr : Fin 20 := ⟨slot.val-460,by have := slot.isLt;omega⟩
        let (_,b,_) := Words.attrs.symm attr
        some (a,.left,after p phase b)

abbrev run (p : Program) := FlatInit.runFrom (machine p)

theorem normal_transition (p : Program) (phase : Fin (p.length+2)) (old : Fin 460) (a : Bit) :
    (machine p).transition (normal p.length phase old) a=oldInstruction p phase old a := by
  simp [machine,normal,localState,old.isLt]

theorem bounce_transition (p : Program) (phase : Fin (p.length+2)) (attr : Fin 20) (a : Bit) :
    (machine p).transition (bounce p.length phase attr) a =
      some (a,.left,after p phase (Words.attrs.symm attr).2.1) := by
  simp [machine,bounce,localState,show ¬460+attr.val<460 by omega]

theorem word_transition (p : Program) (old : Fin 3851) (a : Bit) :
    (machine p).transition (wordState p.length old) a =
      match Words.machine.transition old a with
      | some (w,d,n) => some (w,d,wordState p.length n)
      | none => if old=Words.doneState (Words.ctx true true true) then
          some (a,.right,global p.length 2) else none := by
  simp [machine,wordState]

theorem global_transition (p : Program) (q : Fin 5) (a : Bit) :
    (machine p).transition (global p.length q) a =
      if q=0 then some (a,.right,global p.length 1)
      else if q=1 then some (a,.left,wordState p.length (Words.start true false))
      else if q=2 then some (a,.left,readStart p.length 0) else none := by
  simp [machine,global]

end CatchUp.Machine.Dispatch
