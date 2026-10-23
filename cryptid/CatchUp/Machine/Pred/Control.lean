import CatchUp.Machine.Succ.Prototype

namespace CatchUp.Machine.Pred
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

/-- Branch labels are compiled into paid control. `pred` decrements positives;
`test` preserves its operand. Both distinguish zero from strictly positive. -/
inductive Instruction where
  | halt | call | ret | succ
  | pred (zeroTarget positiveTarget : Nat)
  | test (zeroTarget positiveTarget : Nat)
  deriving DecidableEq, Repr

def Instruction.lower : Instruction → Succ.Instruction
  | .halt => .halt | .call => .call | .ret => .ret | .succ => .succ
  | .pred _ _ | .test _ _ => .halt
abbrev Program := List Instruction
def base (p : Program) : Succ.Program := p.map Instruction.lower
abbrev oldLength (p : Program) := (Call.base (Succ.base (base p))).length
abbrev states (p : Program) := Succ.states (base p)+(p.length+1)*(9*462)

def number (p : Program) :
    (Fin (Succ.states (base p)) ⊕ (Fin (p.length+1) × (Fin 9 × Fin 462))) ≃
      Fin (states p) :=
  ((Equiv.refl _).sumCongr
    (((Equiv.refl _).prodCongr finProdFinEquiv).trans finProdFinEquiv)).trans
      finSumFinEquiv

def lift (p : Program) (old : Fin (Succ.states (base p))) : Fin (states p) :=
  number p (.inl old)
def localState (p : Program) (site : Fin (p.length+1)) (stage : Fin 9) (slot : Fin 462) :
    Fin (states p) := number p (.inr (site,stage,slot))
def normal (p : Program) (site : Fin (p.length+1)) (stage : Fin 9) (old : Fin 460) :
    Fin (states p) := localState p site stage ⟨old.val,by have := old.isLt;omega⟩
def bridge (p : Program) (site : Fin (p.length+1)) (stage : Fin 9) (b : Bit) :
    Fin (states p) := localState p site stage ⟨460+b.val,by have := b.isLt;omega⟩
def index (p : Program) (address : Nat) : Fin (p.length+1) :=
  ⟨min address p.length,by omega⟩
abbrev wordState (p : Program) (q : Fin 3851) := lift p (Succ.wordState (base p) q)
abbrev global (p : Program) (q : Fin 5) := lift p (Succ.global (base p) q)
abbrev readStart (p : Program) := fun phase ↦ lift p (Succ.readStart (base p) phase)
abbrev bitState (p : Program) := fun phase q ↦ lift p (Succ.bitState (base p) phase q)
abbrev succNormal (p : Program) := fun stage q ↦ lift p (Succ.normal (base p) stage q)

def entry (p : Program) (address : Nat) : Fin (states p) :=
  match p[address]? with
  | none => global p 3
  | some .halt => global p 4
  | some .call => wordState p (Words.start false false)
  | some .ret => wordState p (Words.start true false)
  | some .succ => succNormal p 0 (q 10 false 0 0)
  | some (.pred _ _) => normal p (index p address) 0 (q 10 false 0 0)
  | some (.test _ _) => normal p (index p address) 2 (q 10 false 0 0)

def targets (p : Program) (site : Fin (p.length+1)) : Nat × Nat :=
  match p[site.val]? with
  | some (.pred z s) | some (.test z s) => (z,s)
  | _ => (p.length,p.length)
def branch (p : Program) (site : Fin (p.length+1)) (positive : Bool) : Fin (states p) :=
  entry p (if positive then (targets p site).2 else (targets p site).1)

def after (p : Program) (phase : Fin (oldLength p+2)) (b : Bit) : Fin (states p) :=
  if phase.val=0 then
    if b=0 then readStart p (Dispatch.payload (oldLength p) 0) else global p 3
  else if b=1 then readStart p (Dispatch.payload (oldLength p) phase.val)
  else entry p (phase.val-1)

def next (p : Program) (site : Fin (p.length+1)) (stage : Fin 9) (b : Bit) : Fin (states p) :=
  if stage=0 then
    if b=0 then normal p site 1 (q 10 false 0 0) else global p 3
  else if stage=1 then
    if b=0 then normal p site 4 (q 2 false 0 0) else normal p site 6 (q 2 false 0 0)
  else if stage=2 then
    if b=0 then normal p site 3 (q 10 false 0 0) else global p 3
  else if stage=3 then
    if b=0 then normal p site 4 (q 2 false 0 0) else normal p site 7 (q 2 false 1 0)
  else if stage=4 then normal p site 5 (q 2 false 0 0)
  else if stage=5 then branch p site false
  else if stage=6 then branch p site true
  else if stage=7 then normal p site 8 (q 2 false 0 0)
  else branch p site true

def oldInstruction (p : Program) (site : Fin (p.length+1)) (stage : Fin 9)
    (old : Fin 460) (a : Bit) : Option (Bit × Dir × Fin (states p)) :=
  match Separate.machine.transition old a with
  | some (w,d,n) => some (w,d,normal p site stage n)
  | none =>
    let (part,_,b,_) := Separate.number.symm old
    if part=20 then some (a,.right,bridge p site stage b) else none

/-- Every conditional site has nine counted bit contexts and eighteen bridges.
Existing successor/call controls are copied; completed-PC lookup alone changes
its routing to select the six-opcode program and retain a conditional's site. -/
def machine (p : Program) : Machine (states p) 2 where
  transition state a :=
    match (number p).symm state with
    | .inl old =>
      match (Succ.number (base p)).symm old with
      | .inl callOld =>
        match (Dispatch.number (oldLength p)).symm callOld with
        | .inr (.inr (phase,slot)) =>
          if slot.val<460 then
            ((Succ.machine (base p)).transition old a).map fun (w,d,n) ↦ (w,d,lift p n)
          else
            let attr : Fin 20 := ⟨slot.val-460,by have := slot.isLt;omega⟩
            some (a,.left,after p phase (Words.attrs.symm attr).2.1)
        | _ => ((Succ.machine (base p)).transition old a).map fun (w,d,n) ↦ (w,d,lift p n)
      | _ => ((Succ.machine (base p)).transition old a).map fun (w,d,n) ↦ (w,d,lift p n)
    | .inr (site,stage,slot) =>
      if h : slot.val<460 then oldInstruction p site stage ⟨slot.val,h⟩ a
      else some (a,.left,next p site stage ⟨slot.val-460,by have := slot.isLt;omega⟩)

abbrev run (p : Program) := FlatInit.runFrom (machine p)
def wordEmbed (p : Program) (c : Cfg 3851 2) : Cfg (states p) 2 :=
  ⟨wordState p c.state,c.tape⟩
def bitEmbed (p : Program) (phase : Fin (oldLength p+2)) (c : Cfg 460 2) : Cfg (states p) 2 :=
  ⟨bitState p phase c.state,c.tape⟩

theorem base_length (p : Program) : oldLength p=p.length := by
  simp [oldLength,base,Succ.base,Call.base]

theorem word_transition (p : Program) (old : Fin 3851) (a : Bit) :
    (machine p).transition (wordState p old) a =
      ((Succ.machine (base p)).transition (Succ.wordState (base p) old) a).map
        (fun (w,d,n) ↦ (w,d,lift p n)) := by
  simp [machine,lift,Succ.wordState,Succ.lift,Call.wordState,Dispatch.wordState]

theorem global_transition (p : Program) (old : Fin 5) (a : Bit) :
    (machine p).transition (global p old) a =
      ((Succ.machine (base p)).transition (Succ.global (base p) old) a).map
        (fun (w,d,n) ↦ (w,d,lift p n)) := by
  simp [machine,lift,Succ.global,Succ.lift,Call.global,Dispatch.global]

theorem bit_transition (p : Program) (phase : Fin (oldLength p+2)) (old : Fin 460) (a : Bit) :
    (machine p).transition (bitState p phase old) a =
      ((Dispatch.oldInstruction (Call.base (Succ.base (base p))) phase old a).map
        (fun (w,d,n) ↦ (w,d,Succ.lift (base p) n))).map
          (fun (w,d,n) ↦ (w,d,lift p n)) := by
  simp only [machine,lift,Succ.bitState,Succ.lift,Dispatch.normal,Dispatch.localState,
    Equiv.symm_apply_apply,old.isLt,↓reduceIte]
  exact congrArg (Option.map (fun (w,d,n) ↦ (w,d,lift p n)))
    (Succ.bit_transition (base p) phase old a)

theorem bounce_transition (p : Program) (phase : Fin (oldLength p+2)) (attr : Fin 20) (a : Bit) :
    (machine p).transition (lift p (Succ.lift (base p)
      (Dispatch.bounce (oldLength p) phase attr))) a =
      some (a,.left,after p phase (Words.attrs.symm attr).2.1) := by
  simp [machine,lift,Succ.lift,Dispatch.bounce,Dispatch.localState,
    show ¬460+attr.val<460 by omega]

theorem normal_transition (p : Program) (site : Fin (p.length+1)) (stage : Fin 9)
    (old : Fin 460) (a : Bit) :
    (machine p).transition (normal p site stage old) a=oldInstruction p site stage old a := by
  simp [machine,normal,localState,old.isLt]

theorem bridge_transition (p : Program) (site : Fin (p.length+1)) (stage : Fin 9) (b a : Bit) :
    (machine p).transition (bridge p site stage b) a=some (a,.left,next p site stage b) := by
  simp [machine,bridge,localState,show ¬460+b.val<460 by omega]

theorem succ_transition (p : Program) (stage : Fin 3) (old : Fin 460) (a : Bit) :
    (machine p).transition (succNormal p stage old) a =
      ((Succ.machine (base p)).transition (Succ.normal (base p) stage old) a).map
        (fun (w,d,n) ↦ (w,d,lift p n)) := by
  simp [machine,lift,Succ.normal,Succ.localState]

theorem succ_bridge_transition (p : Program) (stage : Fin 3) (b a : Bit) :
    (machine p).transition (lift p (Succ.bridge (base p) stage b)) a=
      some (a,.left,lift p (Succ.next (base p) stage b)) := by
  simp only [machine,lift,Succ.bridge,Succ.localState,Equiv.symm_apply_apply]
  exact congrArg (Option.map (fun (w,d,n) ↦ (w,d,lift p n)))
    (Succ.bridge_transition (base p) stage b a)

end CatchUp.Machine.Pred
