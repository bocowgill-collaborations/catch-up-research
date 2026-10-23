import CatchUp.Machine.Separate.Stacks

namespace CatchUp.Machine.Separate
open Turing ConjectureMachines Compilation
set_option backward.isDefEq.respectTransparency false

@[simp] theorem blank_one : ListBlank.mk [(0:Bit)] = ListBlank.mk [] :=
  Quotient.sound' (Or.inr ⟨1,rfl⟩)
@[simp] theorem blank_two : ListBlank.mk [0,(0:Bit)] = ListBlank.mk [] :=
  Quotient.sound' (Or.inr ⟨2,rfl⟩)

theorem pop_home (s : Side) (w other : List Bit) (b : Bit) (k : Fin 5) :
    run 2 ⟨q 10 s b k,home s w other⟩ = some ⟨q 12 s b k,cursor s [] w other⟩ := by
  cases s <;> simp [run,FlatInit.runFrom,step,machine,q,home,cursor,view,mirror,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write,outward]

theorem pop_scan_pair (s : Side) (pre rest other : List Bit) (a b : Bit) (k : Fin 5) :
    run 2 ⟨q 12 s b k,cursor s pre (a::rest) other⟩ =
      some ⟨q 12 s b k,cursor s (pre++[a]) rest other⟩ := by
  cases s <;> simp [run,FlatInit.runFrom,step,machine,q,cursor,view,mirror,outward,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write,List.reverse_append]

theorem pop_scan (s : Side) (pre rest other : List Bit) (b : Bit) (k : Fin 5) :
    run (2*rest.length) ⟨q 12 s b k,cursor s pre rest other⟩ =
      some ⟨q 12 s b k,cursor s (pre++rest) [] other⟩ := by
  induction rest generalizing pre with
  | nil => simp [run,FlatInit.runFrom]
  | cons a rest ih =>
    rw [show 2*(a::rest).length = 2+2*rest.length by simp; omega,
      run_add,pop_scan_pair,Option.bind_some]
    simpa [List.append_assoc] using ih (pre++[a])

theorem pop_empty_tail (s : Side) (other : List Bit) (b : Bit) (k : Fin 5) :
    run 4 ⟨q 12 s b k,cursor s [] [] other⟩ =
      some ⟨q 19 s b k,home s [] other⟩ := by
  cases s <;> simp [run,FlatInit.runFrom,step,machine,q,cursor,home,view,mirror,inward,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write]

theorem pop_unwrite (s : Side) (w other : List Bit) (a b : Bit) (k : Fin 5) :
    run 4 ⟨q 12 s b k,cursor s (w++[a]) [] other⟩ =
      some ⟨q 17 s a k,cursor s w [] other⟩ := by
  cases s <;> simp [run,FlatInit.runFrom,step,machine,q,cursor,view,mirror,inward,outward,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write,List.reverse_append]

theorem retreat_pair (s : Side) (w other : List Bit) (c b : Bit) (k : Fin 5) :
    run 2 ⟨q 17 s b k,cursor s (w++[c]) [] other⟩ =
      some ⟨q 7 s b k,cursor s w [c] other⟩ := by
  cases s <;> simp [run,FlatInit.runFrom,step,machine,q,cursor,view,mirror,inward,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write,List.reverse_append]

theorem retreat_home (s : Side) (other : List Bit) (b : Bit) (k : Fin 5) :
    run 4 ⟨q 17 s b k,cursor s [] [] other⟩ =
      some ⟨destination s b k,home s [] other⟩ := by
  cases s <;> simp [run,FlatInit.runFrom,step,machine,q,cursor,home,view,mirror,inward,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write]

theorem retreat_run (s : Side) (w other : List Bit) (b : Bit) (k : Fin 5) :
    run (2*w.length+4) ⟨q 17 s b k,cursor s w [] other⟩ =
      some ⟨destination s b k,home s w other⟩ := by
  induction w using List.reverseRecOn with
  | nil => exact retreat_home s other b k
  | append_singleton w c _ =>
    rw [show 2*(w++[c]).length+4 = 2+(2*(w.length+1)+2) by simp; omega,
      run_add,retreat_pair,Option.bind_some]
    exact back_run s w [] other c b k

theorem pop_correct (s : Side) (w other : List Bit) (a b : Bit) (k : Fin 5) :
    run (4*w.length+12) ⟨q 10 s b k,home s (w++[a]) other⟩ =
      some ⟨destination s a k,home s w other⟩ := by
  rw [show 4*w.length+12 = 2+(2*(w++[a]).length+(4+(2*w.length+4))) by simp; omega,
    run_add,pop_home,Option.bind_some,run_add,pop_scan,Option.bind_some]
  simp only [List.nil_append]
  rw [run_add,pop_unwrite,Option.bind_some,retreat_run]

theorem pop_empty (s : Side) (other : List Bit) (b : Bit) (k : Fin 5) :
    run 6 ⟨q 10 s b k,home s [] other⟩ = some ⟨q 19 s b k,home s [] other⟩ := by
  rw [show 6=2+4 by rfl,run_add,pop_home,Option.bind_some,pop_empty_tail]

end CatchUp.Machine.Separate
