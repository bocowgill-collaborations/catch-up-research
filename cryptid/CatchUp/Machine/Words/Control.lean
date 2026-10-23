import CatchUp.Machine.Words.Codec
import CatchUp.Machine.Separate.Prototype

namespace CatchUp.Machine.Words
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

def ctx (s pushing begun : Bool) : Fin 8 :=
  ⟨(if s then 4 else 0)+(if pushing then 2 else 0)+(if begun then 1 else 0),by
    cases s <;> cases pushing <;> cases begun <;> decide⟩
def side (c : Fin 8) : Bool := decide (4 ≤ c.val)
def pushing (c : Fin 8) : Bool := decide (2 ≤ c.val%4)
def begun (c : Fin 8) : Bool := decide (c.val%2=1)

@[simp] theorem ctx_side (s p b : Bool) : side (ctx s p b)=s := by
  cases s <;> cases p <;> cases b <;> rfl
@[simp] theorem ctx_pushing (s p b : Bool) : pushing (ctx s p b)=p := by
  cases s <;> cases p <;> cases b <;> rfl
@[simp] theorem ctx_begun (s p b : Bool) : begun (ctx s p b)=b := by
  cases s <;> cases p <;> cases b <;> rfl

def attrs : (Side × (Bit × Fin 5)) ≃ Fin 20 :=
  ((finTwoEquiv.symm).prodCongr finProdFinEquiv).trans finProdFinEquiv

def normal (c : Fin 8) (old : Fin 460) : Fin 3851 :=
  ⟨3+c.val*481+old.val,by have := c.isLt;have := old.isLt;omega⟩
def bounce (c : Fin 8) (a : Fin 20) : Fin 3851 :=
  ⟨3+c.val*481+460+a.val,by have := c.isLt;have := a.isLt;omega⟩
def doneState (c : Fin 8) : Fin 3851 :=
  ⟨3+c.val*481+480,by have := c.isLt;omega⟩

def start (s first : Bool) : Fin 3851 := normal (ctx s false first) (q 10 s 0 0)

def after (c : Fin 8) (b : Bit) : Fin 3851 :=
  if pushing c then
    if begun c && decide (b=0) then doneState c else start (side c) true
  else normal (ctx (side c) true (begun c)) (q 2 (!(side c)) b 0)

def instruction (c : Fin 8) (old : Fin 460) (a : Bit) :
    Option (Bit × Dir × Fin 3851) :=
  match Separate.machine.transition old a with
  | some (write,dir,next) => some (write,dir,normal c next)
  | none =>
    let (phase,s,b,k) := Separate.number.symm old
    if phase=20 then
      if !pushing c && !begun c && decide (b≠0) then none
      else some (a,.right,bounce c (attrs (s,b,k)))
    else none

/-- Every successful old bit-machine instruction is unchanged in its context.
Only its old stopping boundary is extended with word-level control. -/
def machine : Machine 3851 2 where
  transition state a :=
    if inBoot : state.val < 3 then
      if state.val=0 then some (a,.right,1)
      else some (a,.left,start true false)
    else
      let pos := state.val-3
      let c : Fin 8 := ⟨pos/481,by have := state.isLt;omega⟩
      let slot := pos%481
      if old : slot < 460 then
        let state' : Fin 460 := ⟨slot,old⟩
        instruction c state' a
      else if mid : slot < 480 then
        let attr : Fin 20 := ⟨slot-460,by omega⟩
        let (_,b,_) := attrs.symm attr
        some (a,.left,after c b)
      else if side c then none else some (a,.right,2)

def embed (c : Fin 8) (old : Cfg 460 2) : Cfg 3851 2 := ⟨normal c old.state,old.tape⟩
abbrev run := FlatInit.runFrom machine

theorem normal_transition (c : Fin 8) (old : Fin 460) (a : Bit) :
    machine.transition (normal c old) a = instruction c old a := by
  have off : 3+c.val*481+old.val-3=c.val*481+old.val := by omega
  have div : (c.val*481+old.val)/481=c.val := by have := old.isLt;omega
  have rem : (c.val*481+old.val)%481=old.val := by have := old.isLt;omega
  simp [machine,normal,show ¬3+c.val*481+old.val<3 by omega,off,div,rem,old.isLt]

theorem normal_present (c : Fin 8) (old next : Fin 460) (a write : Bit) (dir : Dir)
    (h : Separate.machine.transition old a = some (write,dir,next)) :
    machine.transition (normal c old) a = some (write,dir,normal c next) := by
  rw [normal_transition]
  simp [instruction,h]

end CatchUp.Machine.Words
