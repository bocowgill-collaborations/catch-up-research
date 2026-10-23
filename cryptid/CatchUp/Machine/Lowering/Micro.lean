import CatchUp.Machine.Lowering.Program

namespace CatchUp.Machine.Lowering
open Turing ConjectureMachines Compilation
set_option backward.isDefEq.respectTransparency false

abbrev Cell := Separate.Bit × Dir × Int
inductive Segment where
  | row (z o : Option Cell)
  | bit (z o : Nat) (empty : Option Nat)
  | word (done next : Nat)

def Segment.size : Segment → Nat
  | .row _ _ => 1 | .bit _ _ _ => 460 | .word _ _ => 3851

def Segment.cell (offset : Nat) (s : Segment) (q : Nat) (a : Separate.Bit) : Option Cell :=
  match s with
  | .row z o => if a=0 then z else o
  | .bit z o empty =>
    if h : q<460 then
      match Separate.machine.transition ⟨q,h⟩ a with
      | some (w,d,n) => some (w,d,Int.ofNat (offset+n.val))
      | none =>
        if q/20=20 then some (a,.right,Int.ofNat (if (q%10)/5=0 then z else o))
        else if q/20=19 then empty.map (fun n ↦ (a,.right,Int.ofNat n)) else none
    else none
  | .word done next =>
    if q=done then some (a,.right,Int.ofNat next)
    else if h : q<3851 then
      (Words.machine.transition ⟨q,h⟩ a).map (fun (w,d,n) ↦ (w,d,Int.ofNat (offset+n.val)))
    else none

structure Micro where
  entry : Nat
  segments : List Segment

def Micro.size (m : Micro) : Nat := (m.segments.map Segment.size).sum

def cells : List Segment → Nat → Nat → Separate.Bit → Option Cell
  | [],_,_,_ => none
  | s::ss,offset,q,a =>
    if q<s.size then s.cell offset q a else cells ss (offset+s.size) (q-s.size) a

def Micro.cell (m : Micro) (q : Nat) (a : Separate.Bit) : Option Cell :=
  cells m.segments 0 q a

end CatchUp.Machine.Lowering
