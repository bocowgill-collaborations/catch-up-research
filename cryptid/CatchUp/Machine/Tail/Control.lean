import CatchUp.Machine.Tail.Program

namespace CatchUp.Machine.Tail
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

abbrev prefixStates (p : Program) := Succ.states (base p)+(p.length+1)*(9*462)
abbrev states (p : Program) := 2+(prefixStates p+(pool p).length*462)+2*463

def layout (p : Program) :
    (Fin (Succ.states (base p)) ⊕ (Fin (p.length+1) × (Fin 9 × Fin 462))) ≃
      Fin (prefixStates p) :=
  ((Equiv.refl _).sumCongr
    (((Equiv.refl _).prodCongr finProdFinEquiv).trans finProdFinEquiv)).trans
      finSumFinEquiv

def number (p : Program) :
    ( (Fin 2 ⊕ (Fin (prefixStates p) ⊕ (Fin (pool p).length × Fin 462))) ⊕
      (Fin 2 × Fin 463)) ≃ Fin (states p) :=
  ((((Equiv.refl _).sumCongr
    (((Equiv.refl _).sumCongr finProdFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv).sumCongr
      finProdFinEquiv).trans finSumFinEquiv

def bootState (p : Program) (q : Fin 2) : Fin (states p) := number p (.inl (.inl q))

def lift (p : Program) (old : Fin (Succ.states (base p))) : Fin (states p) :=
  number p (.inl (.inr (.inl (layout p (.inl old)))))
def localState (p : Program) (site : Fin (p.length+1)) (stage : Fin 9) (slot : Fin 462) :
    Fin (states p) := number p (.inl (.inr (.inl (layout p (.inr (site,stage,slot))))))
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

def literalNormal (p : Program) (i : Fin (pool p).length) (old : Fin 460) : Fin (states p) :=
  number p (.inl (.inr (.inr (i,⟨old.val,by have := old.isLt;omega⟩))))
def literalBridge (p : Program) (i : Fin (pool p).length) (b : Bit) : Fin (states p) :=
  number p (.inl (.inr (.inr (i,⟨460+b.val,by have := b.isLt;omega⟩))))
def literalCell (p : Program) (i : Nat) : Cell := (pool p)[i]?.getD (0,some p.length)
def literalStart (p : Program) (i : Nat) : Fin (states p) :=
  if h : i<(pool p).length then literalNormal p ⟨i,h⟩ (q 2 false (literalCell p i).1 0)
  else global p 3

def tailNormal (p : Program) (stage : Fin 2) (old : Fin 460) : Fin (states p) :=
  number p (.inr (stage,⟨old.val,by have := old.isLt;omega⟩))
def tailBridge (p : Program) (stage : Fin 2) (b : Bit) : Fin (states p) :=
  number p (.inr (stage,⟨460+b.val,by have := b.isLt;omega⟩))
def tailEmpty (p : Program) (stage : Fin 2) : Fin (states p) :=
  number p (.inr (stage,462))
def tailStart (p : Program) : Fin (states p) := tailNormal p 0 (q 10 false 0 0)

def entry (p : Program) (address : Nat) : Fin (states p) :=
  match p[address]? with
  | none => global p 3
  | some .halt => global p 4
  | some .call => wordState p (Words.start false false)
  | some .ret => wordState p (Words.start true false)
  | some .tail => tailStart p
  | some .succ => succNormal p 0 (q 10 false 0 0)
  | some (.pred _ _) => normal p (index p address) 0 (q 10 false 0 0)
  | some (.test _ _) => normal p (index p address) 2 (q 10 false 0 0)
  | some (.push _ _) => literalStart p (offset p address)

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

def advance (p : Program) (i : Nat) : Option Nat → Fin (states p)
  | none => literalStart p (i+1)
  | some address => entry p address

def literalInstruction (p : Program) (i : Fin (pool p).length) (old : Fin 460) (a : Bit) :
    Option (Bit × Dir × Fin (states p)) :=
  match Separate.machine.transition old a with
  | some (w,d,n) => some (w,d,literalNormal p i n)
  | none =>
    let (part,_,b,_) := Separate.number.symm old
    if part=20 then some (a,.right,literalBridge p i b) else none

def tailNext (p : Program) (stage : Fin 2) (b : Bit) : Fin (states p) :=
  if stage=0 then
    if b=0 then tailNormal p 1 (q 10 false 0 0) else global p 3
  else if b=0 then wordState p (Words.start true false)
  else tailNormal p 1 (q 10 false 0 0)

def tailInstruction (p : Program) (stage : Fin 2) (old : Fin 460) (a : Bit) :
    Option (Bit × Dir × Fin (states p)) :=
  match Separate.machine.transition old a with
  | some (w,d,n) => some (w,d,tailNormal p stage n)
  | none =>
    let (part,_,b,_) := Separate.number.symm old
    if part=20 then some (a,.right,tailBridge p stage b)
    else if part=19 then some (a,.right,tailEmpty p stage)
    else none

/-- All instruction sites share the two discard contexts. Empty input has an
explicit bridge; successful literals and branches enter the same real dispatcher. -/
def machine (p : Program) : Machine (states p) 2 where
  transition state a :=
    match (number p).symm state with
    | .inl (.inl boot) =>
      if boot=0 then some (a,.right,bootState p 1) else some (a,.left,entry p 0)
    | .inl (.inr (.inl prior)) =>
      match (layout p).symm prior with
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
    | .inl (.inr (.inr (i,slot))) =>
      if h : slot.val<460 then literalInstruction p i ⟨slot.val,h⟩ a
      else some (a,.left,advance p i.val (literalCell p i.val).2)
    | .inr (stage,slot) =>
      if h : slot.val<460 then tailInstruction p stage ⟨slot.val,h⟩ a
      else if mid : slot.val<462 then
        some (a,.left,tailNext p stage ⟨slot.val-460,by omega⟩)
      else some (a,.left,if stage=0 then wordState p (Words.start true false) else global p 3)

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

theorem boot_transition (p : Program) (q : Fin 2) (a : Bit) :
    (machine p).transition (bootState p q) a=
      if q=0 then some (a,.right,bootState p 1) else some (a,.left,entry p 0) := by
  simp [machine,bootState]

theorem literal_transition (p : Program) (i : Fin (pool p).length) (old : Fin 460) (a : Bit) :
    (machine p).transition (literalNormal p i old) a=literalInstruction p i old a := by
  simp [machine,literalNormal,old.isLt]

theorem literal_bridge_transition (p : Program) (i : Fin (pool p).length) (b a : Bit) :
    (machine p).transition (literalBridge p i b) a=
      some (a,.left,advance p i.val (literalCell p i.val).2) := by
  simp [machine,literalBridge,show ¬460+b.val<460 by omega]

end CatchUp.Machine.Tail
