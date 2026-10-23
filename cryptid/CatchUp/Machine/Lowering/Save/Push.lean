import CatchUp.Machine.Lowering.Save.Rows

namespace CatchUp.Machine.Lowering.Save
open Turing ConjectureMachines Compilation Separate Words Switch Switch.Extract
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- All eight actual save pushes preserve an arbitrary physical left bank,
including a temporarily cleared cursor marker. The two bridge steps are paid. -/
theorem push_bit (k : Push) (left w : List Bit) :
    run saveBody (4*w.length+10) ((P k : Int),RH left w)=
      some ((R k : Int),RH left (w++[B k])) := by
  have copied := run_present Separate.machine saveBody (O k)
    (bit_present saveBody (O k) (Bridge k) (Bridge k) none (push_cells k))
    _ _ _ (right_push left w (B k))
  have equalP : embedControl (O k) ⟨q 2 true (B k) 0,RH left w⟩=
      ((P k : Int),RH left w) := by fin_cases k <;> rfl
  have equalR : embedControl (O k) ⟨q 20 true (B k) 0,RH left (w++[B k])⟩=
      (Int.ofNat (O k+410+5*(B k).val),RH left (w++[B k])) := by fin_cases k <;> rfl
  rw [equalP,equalR] at copied
  have back := bounce saveBody (O k+410+5*(B k).val) (Bridge k) (R k)
    (fun a ↦ (push_ports k a).1) (fun a ↦ (push_ports k a).2) (RH left (w++[B k]))
  rw [show 4*w.length+10=(4*w.length+8)+2 by omega]
  exact run_chain saveBody copied back

/-- A tagged word is followed by exactly 010, the encoding of natural one. -/
theorem push_tag (left frames : List Bit) :
    ∃ steps, run saveBody steps (973,RH left frames)=
      some (2766,RH left (frames++word 1)) := by
  have first := push_bit 2 left frames
  have middle := push_bit 1 left (frames++[0])
  have last := push_bit 0 left (frames++[0,1])
  simp only [B,P,O,R,List.append_assoc,List.cons_append,List.nil_append] at first middle last
  have path := run_chain saveBody (run_chain saveBody first middle) last
  exact ⟨_,path⟩

theorem copy_push (k : Kind) (left frames : List Bit) :
    ∃ steps, run saveBody steps ((P (K k) : Int),RH left frames)=
      some ((Restore k : Int),RH left (frames++[V k]++
        (if k.val=2 then word 1 else []))) := by
  fin_cases k
  · refine ⟨4*frames.length+10,?_⟩
    simpa [K,P,O,B,R,Restore,V] using push_bit 3 left frames
  · refine ⟨4*frames.length+10,?_⟩
    simpa [K,P,O,B,R,Restore,V] using push_bit 4 left frames
  · have first := push_bit 5 left frames
    obtain ⟨last,hlast⟩ := push_tag left (frames++[0])
    exact ⟨_,run_chain saveBody first hlast⟩

theorem sentinel (data frames : List Bit) :
    ∃ steps, run saveBody steps (3310,H data frames)=
      some (2794,H data (frames++word 0)) := by
  have first := push_bit 7 (0::data) frames
  have last := push_bit 6 (0::data) (frames++[0])
  have path := run_chain saveBody first last
  simp only [←H_RH] at path
  refine ⟨4*frames.length+10+(4*(frames++[0]).length+10),?_⟩
  change run saveBody _ (3310,H data frames)=
    some (2794,H data (frames++[0]++[0])) at path
  simpa only [word,List.replicate_zero,List.nil_append,List.cons_append,List.append_assoc]
    using path

end CatchUp.Machine.Lowering.Save
