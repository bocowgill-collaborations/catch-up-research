import CatchUp.Machine.Lowering.Switch.ExtractTape

/-! The existing right-bank push, with an arbitrary untouched physical left
context. This frame generalization is needed while extraction marks a cursor. -/
namespace CatchUp.Machine.Lowering.Switch.Extract
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

def RH (left w : List Bit) : Tape Bit := Tape.mk₂ left (0::0::wire w)
def RC (left pre rest : List Bit) : Tape Bit :=
  Tape.mk₂ ((wire pre).reverse++0::0::left) (wire rest)

theorem push_home (left w : List Bit) (b : Bit) :
    Separate.run 2 ⟨q 2 true b 0,RH left w⟩=some ⟨q 4 true b 0,RC left [] w⟩ := by
  simp [Separate.run,FlatInit.runFrom,ConjectureMachines.step,Separate.machine,q,
    RH,RC,Tape.mk₂,Tape.mk',Tape.move,Tape.write,outward]

theorem push_pair (left pre rest : List Bit) (a b : Bit) :
    Separate.run 2 ⟨q 4 true b 0,RC left pre (a::rest)⟩=
      some ⟨q 4 true b 0,RC left (pre++[a]) rest⟩ := by
  simp [Separate.run,FlatInit.runFrom,ConjectureMachines.step,Separate.machine,q,
    RC,Tape.mk₂,Tape.mk',Tape.move,Tape.write,outward,List.reverse_append]

theorem push_write (left pre : List Bit) (b : Bit) :
    Separate.run 2 ⟨q 4 true b 0,RC left pre []⟩=
      some ⟨q 7 true b 0,RC left pre [b]⟩ := by
  simp [Separate.run,FlatInit.runFrom,ConjectureMachines.step,Separate.machine,q,
    RC,Tape.mk₂,Tape.mk',Tape.move,Tape.write,outward,inward]

theorem push_scan (left pre rest : List Bit) (b : Bit) :
    Separate.run (2*rest.length+2) ⟨q 4 true b 0,RC left pre rest⟩=
      some ⟨q 7 true b 0,RC left (pre++rest) [b]⟩ := by
  induction rest generalizing pre with
  | nil => simpa using push_write left pre b
  | cons a rest ih =>
    rw [show 2*(a::rest).length+2=2+(2*rest.length+2) by simp;omega,
      Separate.run_add,push_pair,Option.bind_some]
    simpa [List.append_assoc] using ih (pre++[a])

theorem push_back_pair (left pre rest : List Bit) (a c b : Bit) :
    Separate.run 2 ⟨q 7 true b 0,RC left (pre++[a]) (c::rest)⟩=
      some ⟨q 7 true b 0,RC left pre (a::c::rest)⟩ := by
  simp [Separate.run,FlatInit.runFrom,ConjectureMachines.step,Separate.machine,q,
    RC,Tape.mk₂,Tape.mk',Tape.move,Tape.write,inward,List.reverse_append]

theorem push_back_home (left rest : List Bit) (a b : Bit) :
    Separate.run 4 ⟨q 7 true b 0,RC left [] (a::rest)⟩=
      some ⟨q 20 true b 0,RH left (a::rest)⟩ := by
  simp [Separate.run,FlatInit.runFrom,ConjectureMachines.step,Separate.machine,q,
    RC,RH,Tape.mk₂,Tape.mk',Tape.move,Tape.write,inward,destination]

theorem push_back (left pre rest : List Bit) (a b : Bit) :
    Separate.run (2*(pre.length+1)+2) ⟨q 7 true b 0,RC left pre (a::rest)⟩=
      some ⟨q 20 true b 0,RH left (pre++a::rest)⟩ := by
  induction pre using List.reverseRecOn generalizing a rest with
  | nil => exact push_back_home left rest a b
  | append_singleton pre last ih =>
    rw [show 2*((pre++[last]).length+1)+2=2+(2*(pre.length+1)+2) by simp;omega,
      Separate.run_add,push_back_pair,Option.bind_some]
    simpa [List.append_assoc] using ih (a::rest) last

/-- No shape assumption is imposed on the physical left context. In particular
an extraction cursor marker can be zero without invalidating this push. -/
theorem right_push (left w : List Bit) (b : Bit) :
    Separate.run (4*w.length+8) ⟨q 2 true b 0,RH left w⟩=
      some ⟨q 20 true b 0,RH left (w++[b])⟩ := by
  rw [show 4*w.length+8=2+((2*w.length+2)+(2*(w.length+1)+2)) by omega,
    Separate.run_add,push_home,Option.bind_some,Separate.run_add,push_scan,Option.bind_some]
  simpa using push_back left w [] b b

theorem push_cells (k : Kind) (q : Fin 460) (a : Bit) :
    switchBody.cell (O k+q.val) a=
      (Segment.bit (461*k.val) (461*k.val) none).cell (O k) q.val a := by
  fin_cases k
  · exact cell_in switchBody (switchBody.segments.take 1) (switchBody.segments.drop 2)
      (.bit 0 0 none) (by rfl) q.val q.isLt a
  · exact cell_in switchBody (switchBody.segments.take 3) (switchBody.segments.drop 4)
      (.bit 461 461 none) (by rfl) q.val q.isLt a
  · exact cell_in switchBody (switchBody.segments.take 5) (switchBody.segments.drop 6)
      (.bit 922 922 none) (by rfl) q.val q.isLt a

theorem push_prefix (k : Kind) (left w : List Bit) :
    run switchBody (4*w.length+8) ((P k : Int),RH left w)=
      some (Int.ofNat (O k+410+5*(B k).val),RH left (w++[B k])) := by
  have h := run_present Separate.machine switchBody (O k)
    (bit_present switchBody (O k) (461*k.val) (461*k.val) none (push_cells k))
    _ _ _ (right_push left w (B k))
  fin_cases k <;> exact h

theorem push_ports (k : Kind) (a : Bit) :
    switchBody.cell (O k+410+5*(B k).val) a=some (a,.right,Int.ofNat (461*k.val)) ∧
    switchBody.cell (461*k.val) a=some (a,.left,Int.ofNat (R k)) := by
  fin_cases k <;> fin_cases a <;> exact ⟨rfl,rfl⟩

theorem push_exit (k : Kind) (T : Tape Bit) :
    run switchBody 2 ((O k+410+5*(B k).val : Nat),T)=some ((R k : Int),T) :=
  bounce switchBody (O k+410+5*(B k).val) (461*k.val) (R k)
    (fun a ↦ (push_ports k a).1) (fun a ↦ (push_ports k a).2) T

theorem push_bit (k : Kind) (left w : List Bit) :
    run switchBody (4*w.length+10) ((P k : Int),RH left w)=
      some ((R k : Int),RH left (w++[B k])) := by
  rw [show 4*w.length+10=(4*w.length+8)+2 by omega,run_add,push_prefix,Option.bind_some]
  exact push_exit k (RH left (w++[B k]))

end CatchUp.Machine.Lowering.Switch.Extract
