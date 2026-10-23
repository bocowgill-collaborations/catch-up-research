import CatchUp.Machine.Lowering.Switch.ExtractShift
import CatchUp.Machine.Lowering.Switch.ExtractCopy

namespace CatchUp.Machine.Lowering.Switch.Extract
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem mark_home_base (flag : Bit) (rest frames : List Bit) :
    run switchBody 2 ((M flag 3 : Int),H rest frames)=
      some ((S flag 0 : Int),H rest frames) := by
  simp [run,step_nat,mark_cell,markRow,H,view,mirror,Tape.mk₂,Tape.mk',
    Tape.move,Tape.write,Int.ofNat_eq_natCast]

theorem mark_home_pair (flag : Bit) (pre rest frames : List Bit) (b : Bit) :
    run switchBody 2 ((M flag 3 : Int),At (wire pre) (1::b::rest) frames)=
      some ((M flag 3 : Int),
        ((At (wire pre) (1::b::rest) frames).move .right).move .right) := by
  simp [run,step_nat,mark_cell,markRow,At,view,mirror,Tape.mk₂,Tape.mk',
    Tape.move,Tape.write,Int.ofNat_eq_natCast]

theorem mark_home (flag : Bit) (pre rest frames : List Bit) :
    run switchBody (2*pre.length+2)
      ((M flag 3 : Int),((At (wire pre) rest frames).move .right).move .right)=
      some ((S flag 0 : Int),H (wire pre++rest) frames) := by
  induction pre using List.reverseRecOn generalizing rest with
  | nil => simpa [at_home] using mark_home_base flag rest frames
  | append_singleton pre b ih =>
    have ht : ((At (wire (pre++[b])) rest frames).move .right).move .right=
        At (wire pre) (1::b::rest) frames := by
      rw [wire_append]
      exact at_in_pair (wire pre) rest frames 1 b
    rw [show 2*(pre++[b]).length+2=2+(2*pre.length+2) by simp;omega,
      run_add,ht,mark_home_pair,Option.bind_some]
    simpa only [wire_append,wire_cons,wire_nil,List.append_assoc,List.cons_append,
      List.nil_append] using ih (1::b::rest)

theorem mark_first (flag : Bit) (pre tail frames : List Bit) :
    run switchBody 1 (1416,At (wire pre) (flag::0::wire tail) frames)=
      some ((M flag 0 : Int),At (wire pre++[0]) (0::wire tail) frames) := by
  simp [run,Switch.step,mark_entry_cell,At,view,mirror,Tape.mk₂,Tape.mk',
    Tape.move,Tape.write,List.reverse_append,Int.ofNat_eq_natCast]

theorem mark_finish (flag : Bit) (pre tail frames : List Bit) :
    run switchBody 3 ((M flag 0 : Int),At (wire pre++[0]) (0::wire tail) frames)=
      some ((M flag 3 : Int),
        ((At (wire pre) (0::1::wire tail) frames).move .right).move .right) := by
  simp [run,step_nat,mark_cell,markRow,At,view,mirror,Tape.mk₂,Tape.mk',
    Tape.move,Tape.write,List.reverse_append,Int.ofNat_eq_natCast]

/-- Remember the old first marker, install the temporary 01 boundary, and
return home. Both flag values preserve the complete following bank and frames. -/
theorem mark_boundary (flag : Bit) (pre tail frames : List Bit) :
    ∃ steps, run switchBody steps (1416,At (wire pre) (flag::0::wire tail) frames)=
      some ((S flag 0 : Int),H (wire pre++0::1::wire tail) frames) := by
  exact ⟨_,run_chain switchBody
    (run_chain switchBody (mark_first flag pre tail frames) (mark_finish flag pre tail frames))
    (mark_home flag pre (0::1::wire tail) frames)⟩

end CatchUp.Machine.Lowering.Switch.Extract
