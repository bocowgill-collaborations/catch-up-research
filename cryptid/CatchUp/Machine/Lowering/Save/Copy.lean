import CatchUp.Machine.Lowering.Save.Push

namespace CatchUp.Machine.Lowering.Save
open Turing ConjectureMachines Compilation Separate Words Switch Switch.Extract
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Cursor at the last marker of pre, or at home when pre is empty.
rest is physical tape and may be the already-copied suffix. -/
def Cursor (pre rest frames : List Bit) : Tape Bit :=
  ((At (wire pre) rest frames).move .right).move .right

theorem cursor_nil (rest frames : List Bit) : Cursor [] rest frames=H rest frames :=
  at_home rest frames

theorem cursor_snoc (pre rest frames : List Bit) (b : Bit) :
    Cursor (pre++[b]) rest frames=At (wire pre) (1::b::rest) frames := by
  rw [Cursor,wire_append]
  exact at_in_pair (wire pre) rest frames 1 b

theorem carry (k : Kind) (T : Tape Bit) :
    Switch.run saveBody 2 ((Q k 4 : Int),T)=
      some ((Q k 6 : Int),(T.move .right).move .right) := by
  simp [Switch.run,step_nat,copy_cell,copyRow,Int.ofNat_eq_natCast]

theorem to_home_base (k : Kind) (rest frames : List Bit) :
    Switch.run saveBody 2 ((Q k 6 : Int),H rest frames)=
      some ((P (K k) : Int),H rest frames) := by
  simp [Switch.run,step_nat,copy_cell,copyRow,H,view,mirror,Tape.mk₂,Tape.mk',
    Tape.move,Tape.write,Int.ofNat_eq_natCast]

theorem to_home_pair (k : Kind) (pre rest frames : List Bit) (b : Bit) :
    Switch.run saveBody 2 ((Q k 6 : Int),At (wire pre) (1::b::rest) frames)=
      some ((Q k 6 : Int),((At (wire pre) (1::b::rest) frames).move .right).move .right) := by
  simp [Switch.run,step_nat,copy_cell,copyRow,At,view,mirror,Tape.mk₂,Tape.mk',
    Tape.move,Tape.write,Int.ofNat_eq_natCast]

theorem to_home (k : Kind) (pre rest frames : List Bit) :
    Switch.run saveBody (2*pre.length+2) ((Q k 6 : Int),Cursor pre rest frames)=
      some ((P (K k) : Int),H (wire pre++rest) frames) := by
  induction pre using List.reverseRecOn generalizing rest with
  | nil => simpa [cursor_nil] using to_home_base k rest frames
  | append_singleton pre b ih =>
    rw [show 2*(pre++[b]).length+2=2+(2*pre.length+2) by simp;omega,
      Switch.run_add,cursor_snoc,to_home_pair,Option.bind_some]
    simpa only [Cursor,wire_append,wire_cons,wire_nil,List.append_assoc,List.cons_append,
      List.nil_append] using ih (1::b::rest)

theorem restore_start (k : Kind) (rest frames : List Bit) :
    Switch.run saveBody 2 ((Q k 0 : Int),H rest frames)=
      some ((Q k 2 : Int),At [] rest frames) := by
  simp [Switch.run,step_nat,copy_cell,copyRow,At,H,view,mirror,Tape.mk₂,Tape.mk',
    Tape.move,Tape.write,Int.ofNat_eq_natCast]

theorem restore_found (k : Kind) (pre rest frames : List Bit) :
    Switch.run saveBody 2 ((Q k 2 : Int),At (wire pre) (0::V k::rest) frames)=
      some ((Next k : Int),Cursor pre (1::V k::rest) frames) := by
  simp [Switch.run,step_nat,copy_cell,copyRow,Cursor,At,view,mirror,Tape.mk₂,Tape.mk',
    Tape.move,Tape.write,Int.ofNat_eq_natCast]

theorem restore_pair (k : Kind) (pre rest frames : List Bit) (b : Bit) :
    Switch.run saveBody 2 ((Q k 2 : Int),At (wire pre) (1::b::rest) frames)=
      some ((Q k 2 : Int),At (wire (pre++[b])) rest frames) := by
  simp [Switch.run,step_nat,copy_cell,copyRow,At,view,mirror,wire_append,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write,List.reverse_append,Int.ofNat_eq_natCast]

theorem restore_walk (k : Kind) (todo pre rest frames : List Bit) :
    Switch.run saveBody (2*todo.length+2)
      ((Q k 2 : Int),At (wire pre) (wire todo++0::V k::rest) frames)=
      some ((Next k : Int),Cursor (pre++todo) (1::V k::rest) frames) := by
  induction todo generalizing pre with
  | nil => simpa using restore_found k pre rest frames
  | cons b todo ih =>
    rw [show 2*(b::todo).length+2=2+(2*todo.length+2) by simp;omega,Switch.run_add]
    simp only [wire_cons,List.cons_append]
    rw [restore_pair,Option.bind_some]
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using ih (pre++[b])

theorem restore_cursor (k : Kind) (pre rest frames : List Bit) :
    Switch.run saveBody (2*pre.length+4)
      ((Restore k : Int),H (wire pre++0::V k::rest) frames)=
      some ((Next k : Int),Cursor pre (1::V k::rest) frames) := by
  have first := restore_start k (wire pre++0::V k::rest) frames
  have last := restore_walk k pre [] rest frames
  rw [show 2*pre.length+4=2+(2*pre.length+2) by omega]
  exact run_chain saveBody first last

/-- Copy the marked bit, pay the optional word tag, restore its marker,
and move the cursor inward. The earlier caller frame is arbitrary. -/
theorem copy_bit (k : Kind) (pre rest frames : List Bit) :
    ∃ steps, Switch.run saveBody steps
      ((C k : Int),At (wire pre) (0::V k::rest) frames)=
      some ((Next k : Int),Cursor pre (1::V k::rest)
        (frames++[V k]++(if k.val=2 then word 1 else []))) := by
  have home := run_chain saveBody
    (carry k (At (wire pre) (0::V k::rest) frames))
    (to_home k pre (0::V k::rest) frames)
  obtain ⟨n,push⟩ := copy_push k (0::(wire pre++0::V k::rest)) frames
  simp only [←H_RH] at push
  exact ⟨_,run_chain saveBody (run_chain saveBody home push)
    (restore_cursor k pre rest (frames++[V k]++
      (if k.val=2 then word 1 else [])))⟩

theorem open_drive (pre rest frames : List Bit) :
    Switch.run saveBody 2 (2774,At (wire pre) (1::0::rest) frames)=
      some (2779,At (wire pre) (0::0::rest) frames) := by
  simp [Switch.run,Switch.step,(drive_cell 1).1,(drive_cell 0).2.2.1,At,view,mirror,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write]

theorem payload_drive (pre rest frames : List Bit) (b : Bit) :
    Switch.run saveBody 2 (2775,At (wire pre) (1::b::rest) frames)=
      some (if b=0 then 2784 else 2789,At (wire pre) (0::b::rest) frames) := by
  fin_cases b <;>
    simp [Switch.run,Switch.step,drive_cell,At,view,mirror,Tape.mk₂,Tape.mk',Tape.move,Tape.write]

theorem copy_open (pre rest frames : List Bit) :
    ∃ steps, Switch.run saveBody steps (2774,Cursor (pre++[0]) rest frames)=
      some (2775,Cursor pre (1::0::rest) (frames++[0])) := by
  rw [cursor_snoc]
  obtain ⟨n,h⟩ := copy_bit 0 pre rest frames
  simp [C,Next,V] at h
  exact ⟨_,run_chain saveBody (open_drive pre rest frames) h⟩

theorem copy_one (pre rest frames : List Bit) :
    ∃ steps, Switch.run saveBody steps (2775,Cursor (pre++[1]) rest frames)=
      some (2775,Cursor pre (1::1::rest) (frames++[1])) := by
  rw [cursor_snoc]
  obtain ⟨n,h⟩ := copy_bit 1 pre rest frames
  simp [C,Next,V] at h
  exact ⟨_,run_chain saveBody (payload_drive pre rest frames 1) h⟩

theorem copy_close (pre rest frames : List Bit) :
    ∃ steps, Switch.run saveBody steps (2775,Cursor (pre++[0]) rest frames)=
      some (2774,Cursor pre (1::0::rest) (frames++[0]++word 1)) := by
  rw [cursor_snoc]
  obtain ⟨n,h⟩ := copy_bit 2 pre rest frames
  exact ⟨_,run_chain saveBody (payload_drive pre rest frames 0) h⟩

end CatchUp.Machine.Lowering.Save
