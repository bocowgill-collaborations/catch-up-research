import Cryptids.Compilation.FlatInit
import Mathlib.Tactic

/-! Two outward-growing regions. Words are bottom first, encoded as marker/bit pairs.
The three zero cells around the origin separate the regions. All controls are finite. -/
namespace CatchUp.Machine.Separate
open Turing ConjectureMachines Compilation
set_option backward.isDefEq.respectTransparency false

abbrev Bit := Fin 2
abbrev Side := Bool
abbrev Control := Fin 23 × (Side × (Bit × Fin 5))

def number : Control ≃ Fin 460 :=
  ((Equiv.refl _).prodCongr ((finTwoEquiv.symm).prodCongr (Equiv.refl _))).trans
    ((Equiv.refl _).prodCongr ((Equiv.refl _).prodCongr finProdFinEquiv |>.trans
      finProdFinEquiv) |>.trans finProdFinEquiv)

def q (p : Fin 23) (s : Side) (b : Bit) (k : Fin 5) : Fin 460 :=
  number (p,s,b,k)

def outward (s : Side) : Dir := if s then .right else .left
def inward (s : Side) : Dir := if s then .left else .right

def destination (s : Side) (b : Bit) (k : Fin 5) : Fin 460 :=
  if k = 1 then q 2 true 0 3
  else if k = 2 then q 21 s b k
  else if k = 3 then q 22 s b k
  else if k = 4 then if b = 0 then q 21 s b k else q 22 s b k
  else q 20 s b k

def machine : Machine 460 2 where
  transition state a :=
    let (p,s,b,k) := number.symm state
    let go (v : Bit) (d : Dir) (phase : Fin 23) (value := b) :=
      some (v,d,q phase s value k)
    match p.val with
    | 0 => some (a,.right,q 1 false 1 1)
    | 1 => some (a,.left,q 2 false 1 1)
    | 2 => go a (outward s) 3
    | 3 => go a (outward s) 4
    | 4 => if a = 1 then go a (outward s) 5 else go 1 (outward s) 6
    | 5 => go a (outward s) 4
    | 6 => go b (inward s) 7
    | 7 => if a = 1 then go a (inward s) 8 else go a .right 9
    | 8 => go a (inward s) 7
    | 9 => some (a,.left,destination s b k)
    | 10 => go a (outward s) 11
    | 11 => go a (outward s) 12
    | 12 => if a = 1 then go a (outward s) 13 else go a (inward s) 14
    | 13 => go a (outward s) 12
    | 14 => go a (inward s) 15
    | 15 => if a = 1 then go 0 (outward s) 16 else go a .right 18
    | 16 => go 0 (inward s) 17 a
    | 17 => go a (inward s) 8
    | 18 => go a .left 19
    | 21 => some (a,.left,q 11 false 0 0)
    | 22 => some (a,.right,q 11 true 0 4)
    | _ => none

@[simp] theorem transition_q (p : Fin 23) (s : Side) (b a : Bit) (k : Fin 5) :
    machine.transition (q p s b k) a = machine.transition (number (p,s,b,k)) a := rfl

def wire (w : List Bit) : List Bit := w.flatMap fun b ↦ [1,b]

@[simp] theorem wire_nil : wire [] = [] := rfl
@[simp] theorem wire_cons (b : Bit) (w : List Bit) : wire (b::w) = 1::b::wire w := rfl
@[simp] theorem wire_append (v w : List Bit) : wire (v++w) = wire v ++ wire w :=
  List.flatMap_append

def mirror (T : Tape Bit) : Tape Bit := ⟨T.head,T.right,T.left⟩
def view (s : Side) (L R : List Bit) : Tape Bit :=
  if s then Tape.mk₂ L R else mirror (Tape.mk₂ L R)

def home (s : Side) (w other : List Bit) : Tape Bit :=
  view s (0::wire other) (0::0::wire w)
def cursor (s : Side) (pre rest other : List Bit) : Tape Bit :=
  view s ((wire pre).reverse ++ 0::0::0::wire other) (wire rest)

abbrev run := FlatInit.runFrom machine

theorem run_add (m n : Nat) (c : Cfg 460 2) :
    run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run,FlatInit.runFrom]
  | succ m ih => simp only [Nat.succ_add,run,FlatInit.runFrom,ih,Option.bind_assoc]

theorem at_home (s : Side) (w other : List Bit) (b : Bit) (k : Fin 5) :
    run 2 ⟨q 2 s b k,home s w other⟩ = some ⟨q 4 s b k,cursor s [] w other⟩ := by
  cases s <;> simp [run,FlatInit.runFrom,step,machine,q,home,cursor,view,mirror,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write,outward]

theorem push_scan_pair (s : Side) (pre rest other : List Bit) (a b : Bit) (k : Fin 5) :
    run 2 ⟨q 4 s b k,cursor s pre (a::rest) other⟩ =
      some ⟨q 4 s b k,cursor s (pre++[a]) rest other⟩ := by
  cases s <;> simp [run,FlatInit.runFrom,step,machine,q,cursor,view,mirror,outward,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write,List.reverse_append]

theorem push_write (s : Side) (pre other : List Bit) (b : Bit) (k : Fin 5) :
    run 2 ⟨q 4 s b k,cursor s pre [] other⟩ =
      some ⟨q 7 s b k,cursor s pre [b] other⟩ := by
  cases s <;> simp [run,FlatInit.runFrom,step,machine,q,cursor,view,mirror,outward,inward,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write]

theorem push_scan (s : Side) (pre rest other : List Bit) (b : Bit) (k : Fin 5) :
    run (2*rest.length+2) ⟨q 4 s b k,cursor s pre rest other⟩ =
      some ⟨q 7 s b k,cursor s (pre++rest) [b] other⟩ := by
  induction rest generalizing pre with
  | nil => simpa using push_write s pre other b k
  | cons a rest ih =>
    rw [show 2*(a::rest).length+2 = 2+(2*rest.length+2) by simp; omega,
      run_add,push_scan_pair,Option.bind_some]
    simpa [List.append_assoc] using ih (pre++[a])

theorem back_pair (s : Side) (pre rest other : List Bit) (a c b : Bit) (k : Fin 5) :
    run 2 ⟨q 7 s b k,cursor s (pre++[a]) (c::rest) other⟩ =
      some ⟨q 7 s b k,cursor s pre (a::c::rest) other⟩ := by
  cases s <;> simp [run,FlatInit.runFrom,step,machine,q,cursor,view,mirror,inward,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write,List.reverse_append]

theorem back_home (s : Side) (rest other : List Bit) (a b : Bit) (k : Fin 5) :
    run 4 ⟨q 7 s b k,cursor s [] (a::rest) other⟩ =
      some ⟨destination s b k,home s (a::rest) other⟩ := by
  cases s <;> simp [run,FlatInit.runFrom,step,machine,q,cursor,home,view,mirror,inward,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write]

theorem back_run (s : Side) (pre rest other : List Bit) (a b : Bit) (k : Fin 5) :
    run (2*(pre.length+1)+2) ⟨q 7 s b k,cursor s pre (a::rest) other⟩ =
      some ⟨destination s b k,home s (pre++a::rest) other⟩ := by
  induction pre using List.reverseRecOn generalizing a rest with
  | nil => exact back_home s rest other a b k
  | append_singleton pre last ih =>
    rw [show 2*((pre++[last]).length+1)+2 = 2+(2*(pre.length+1)+2) by simp; omega,
      run_add,back_pair,Option.bind_some]
    simpa [List.append_assoc] using ih (a::rest) last

theorem push_correct (s : Side) (w other : List Bit) (b : Bit) (k : Fin 5) :
    run (4*w.length+8) ⟨q 2 s b k,home s w other⟩ =
      some ⟨destination s b k,home s (w++[b]) other⟩ := by
  rw [show 4*w.length+8 = 2+((2*w.length+2)+(2*(w.length+1)+2)) by omega,
    run_add,at_home,Option.bind_some,run_add,push_scan,Option.bind_some]
  simpa using back_run s w [] other b b k

end CatchUp.Machine.Separate
