import CatchUp.Machine.Call.Prototype

namespace CatchUp.Machine.Succ
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

/-- Successor is a real callee: increment the top natural, then enter return. -/
inductive Instruction where
  | halt | call | ret | succ
  deriving DecidableEq, Repr

def Instruction.lower : Instruction → Call.Instruction
  | .halt => .halt | .call => .call | .ret => .ret | .succ => .halt
abbrev Program := List Instruction
def base (p : Program) : Call.Program := p.map Instruction.lower
abbrev states (p : Program) := Call.states (base p)+1386

def number (p : Program) : (Fin (Call.states (base p)) ⊕ (Fin 3 × Fin 462)) ≃
    Fin (states p) :=
  ((Equiv.refl _).sumCongr finProdFinEquiv).trans finSumFinEquiv

def lift (p : Program) (old : Fin (Call.states (base p))) : Fin (states p) :=
  number p (.inl old)
def localState (p : Program) (stage : Fin 3) (slot : Fin 462) : Fin (states p) :=
  number p (.inr (stage,slot))
def normal (p : Program) (stage : Fin 3) (old : Fin 460) : Fin (states p) :=
  localState p stage ⟨old.val,by have := old.isLt;omega⟩
def bridge (p : Program) (stage : Fin 3) (bit : Bit) : Fin (states p) :=
  localState p stage ⟨460+bit.val,by have := bit.isLt;omega⟩
abbrev wordState (p : Program) (q : Fin 3851) := lift p (Call.wordState (base p) q)
abbrev global (p : Program) (q : Fin 5) := lift p (Call.global (base p) q)
abbrev readStart (p : Program) := fun phase ↦ lift p (Call.readStart (base p) phase)
abbrev bitState (p : Program) := fun phase q ↦
  lift p (Dispatch.normal (Call.base (base p)).length phase q)

def entry (p : Program) : Option Instruction → Fin (states p)
  | none => global p 3
  | some .halt => global p 4
  | some .call => wordState p (Words.start false false)
  | some .ret => wordState p (Words.start true false)
  | some .succ => normal p 0 (q 10 false 0 0)

def after (p : Program) (phase : Fin ((Call.base (base p)).length+2)) (b : Bit) :
    Fin (states p) :=
  if phase.val=0 then
    if b=0 then readStart p (Dispatch.payload (Call.base (base p)).length 0) else global p 3
  else if b=1 then readStart p (Dispatch.payload (Call.base (base p)).length phase.val)
  else entry p p[phase.val-1]?

def next (p : Program) (stage : Fin 3) (b : Bit) : Fin (states p) :=
  if stage=0 then
    if b=0 then normal p 1 (q 2 false 1 0) else global p 3
  else if stage=1 then normal p 2 (q 2 false 0 0)
  else wordState p (Words.start true false)

def oldInstruction (p : Program) (stage : Fin 3) (old : Fin 460) (a : Bit) :
    Option (Bit × Dir × Fin (states p)) :=
  match Separate.machine.transition old a with
  | some (w,d,n) => some (w,d,normal p stage n)
  | none =>
    let (part,_,b,_) := Separate.number.symm old
    if part=20 then some (a,.right,bridge p stage b) else none

/-- Existing word/call controls and successful bit operations are copied. Only
lookup's completed-PC bounce selects the new opcode. Three paid bit contexts
implement pop-zero, push-one and push-zero, with six head-restoration bridges. -/
def machine (p : Program) : Machine (states p) 2 where
  transition state a :=
    match (number p).symm state with
    | .inl old =>
      match (Dispatch.number (Call.base (base p)).length).symm old with
      | .inr (.inr (phase,slot)) =>
        if slot.val < 460 then
          ((Call.machine (base p)).transition old a).map fun (w,d,n) ↦ (w,d,lift p n)
        else
          let attr : Fin 20 := ⟨slot.val-460,by have := slot.isLt;omega⟩
          some (a,.left,after p phase (Words.attrs.symm attr).2.1)
      | _ => ((Call.machine (base p)).transition old a).map fun (w,d,n) ↦ (w,d,lift p n)
    | .inr (stage,slot) =>
      if h : slot.val<460 then oldInstruction p stage ⟨slot.val,h⟩ a
      else some (a,.left,next p stage ⟨slot.val-460,by have := slot.isLt;omega⟩)

abbrev run (p : Program) := FlatInit.runFrom (machine p)
def wordEmbed (p : Program) (c : Cfg 3851 2) : Cfg (states p) 2 :=
  ⟨wordState p c.state,c.tape⟩
def bitEmbed (p : Program) (phase : Fin ((Call.base (base p)).length+2)) (c : Cfg 460 2) :
    Cfg (states p) 2 := ⟨bitState p phase c.state,c.tape⟩
def localEmbed (p : Program) (stage : Fin 3) (c : Cfg 460 2) : Cfg (states p) 2 :=
  ⟨normal p stage c.state,c.tape⟩

theorem base_length (p : Program) : (Call.base (base p)).length=p.length := by
  simp [base,Call.base]

theorem word_transition (p : Program) (old : Fin 3851) (a : Bit) :
    (machine p).transition (wordState p old) a =
      ((Call.machine (base p)).transition (Call.wordState (base p) old) a).map
        (fun (w,d,n) ↦ (w,d,lift p n)) := by
  simp [machine,lift,Call.wordState,Dispatch.wordState]

theorem global_transition (p : Program) (old : Fin 5) (a : Bit) :
    (machine p).transition (global p old) a =
      ((Call.machine (base p)).transition (Call.global (base p) old) a).map
        (fun (w,d,n) ↦ (w,d,lift p n)) := by
  simp [machine,lift,Call.global,Dispatch.global]

theorem bit_transition (p : Program) (phase : Fin ((Call.base (base p)).length+2))
    (old : Fin 460) (a : Bit) :
    (machine p).transition (bitState p phase old) a =
      (Dispatch.oldInstruction (Call.base (base p)) phase old a).map
        (fun (w,d,n) ↦ (w,d,lift p n)) := by
  simp only [machine,lift,Dispatch.normal,Dispatch.localState,Equiv.symm_apply_apply,
    old.isLt,↓reduceIte]
  exact congrArg (Option.map (fun (w,d,n) ↦ (w,d,lift p n)))
    (Call.bit_transition (base p) phase old a)

theorem bounce_transition (p : Program) (phase : Fin ((Call.base (base p)).length+2))
    (attr : Fin 20) (a : Bit) :
    (machine p).transition (lift p (Dispatch.bounce (Call.base (base p)).length phase attr)) a =
      some (a,.left,after p phase (Words.attrs.symm attr).2.1) := by
  simp [machine,lift,Dispatch.bounce,Dispatch.localState,show ¬460+attr.val<460 by omega]

theorem normal_transition (p : Program) (stage : Fin 3) (old : Fin 460) (a : Bit) :
    (machine p).transition (normal p stage old) a=oldInstruction p stage old a := by
  simp [machine,normal,localState,old.isLt]

theorem bridge_transition (p : Program) (stage : Fin 3) (b a : Bit) :
    (machine p).transition (bridge p stage b) a=some (a,.left,next p stage b) := by
  simp [machine,bridge,localState,show ¬460+b.val<460 by omega]

end CatchUp.Machine.Succ
