import CatchUp.Machine.Lowering.Switch.ExtractPush

namespace CatchUp.Machine.Lowering.Switch.Extract
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem H_RH (raw frames : List Bit) : H raw frames=RH (0::raw) frames := by
  simp [H,RH,view,mirror,Tape.mk₂,Tape.mk']

theorem carry (k : Kind) (T : Tape Bit) :
    run switchBody 2 ((Q k 4 : Int),T)=
      some ((Q k 6 : Int),(T.move .right).move .right) := by
  simp [run,step_nat,copy_cell,copyRow,Int.ofNat_eq_natCast]

theorem to_home_base (k : Kind) (rest frames : List Bit) :
    run switchBody 2 ((Q k 6 : Int),H rest frames)=some ((P k : Int),H rest frames) := by
  simp [run,step_nat,copy_cell,copyRow,H,view,mirror,Tape.mk₂,Tape.mk',
    Tape.move,Tape.write,Int.ofNat_eq_natCast]

theorem to_home_pair (k : Kind) (pre rest frames : List Bit) (b : Bit) :
    run switchBody 2 ((Q k 6 : Int),At (wire pre) (1::b::rest) frames)=
      some ((Q k 6 : Int),((At (wire pre) (1::b::rest) frames).move .right).move .right) := by
  simp [run,step_nat,copy_cell,copyRow,At,view,mirror,Tape.mk₂,Tape.mk',
    Tape.move,Tape.write,Int.ofNat_eq_natCast]

theorem to_home (k : Kind) (pre rest frames : List Bit) :
    run switchBody (2*pre.length+2)
      ((Q k 6 : Int),((At (wire pre) rest frames).move .right).move .right)=
      some ((P k : Int),H (wire pre++rest) frames) := by
  induction pre using List.reverseRecOn generalizing rest with
  | nil => simpa [at_home] using to_home_base k rest frames
  | append_singleton pre b ih =>
    have ht : ((At (wire (pre++[b])) rest frames).move .right).move .right=
        At (wire pre) (1::b::rest) frames := by
      rw [wire_append]
      exact at_in_pair (wire pre) rest frames 1 b
    rw [show 2*(pre++[b]).length+2=2+(2*pre.length+2) by simp;omega,
      run_add,ht,to_home_pair,Option.bind_some]
    simpa only [wire_append,wire_cons,wire_nil,List.append_assoc,List.cons_append,
      List.nil_append] using ih (1::b::rest)

theorem restore_start (k : Kind) (rest frames : List Bit) :
    run switchBody 2 ((Q k 0 : Int),H rest frames)=
      some ((Q k 2 : Int),At [] rest frames) := by
  simp [run,step_nat,copy_cell,copyRow,At,H,view,mirror,Tape.mk₂,Tape.mk',
    Tape.move,Tape.write,Int.ofNat_eq_natCast]

theorem restore_found (k : Kind) (pre rest frames : List Bit) :
    run switchBody 2 ((Q k 2 : Int),At (wire pre) (0::B k::rest) frames)=
      some ((N k : Int),At (wire (pre++[B k])) rest frames) := by
  simp [run,step_nat,copy_cell,copyRow,At,view,mirror,wire_append,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write,List.reverse_append,Int.ofNat_eq_natCast]

theorem restore_pair (k : Kind) (pre rest frames : List Bit) (b : Bit) :
    run switchBody 2 ((Q k 2 : Int),At (wire pre) (1::b::rest) frames)=
      some ((Q k 2 : Int),At (wire (pre++[b])) rest frames) := by
  simp [run,step_nat,copy_cell,copyRow,At,view,mirror,wire_append,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write,List.reverse_append,Int.ofNat_eq_natCast]

theorem restore_walk (k : Kind) (todo pre rest frames : List Bit) :
    run switchBody (2*todo.length+2)
      ((Q k 2 : Int),At (wire pre) (wire todo++0::B k::rest) frames)=
      some ((N k : Int),At (wire (pre++todo++[B k])) rest frames) := by
  induction todo generalizing pre with
  | nil => simpa using restore_found k pre rest frames
  | cons b todo ih =>
    rw [show 2*(b::todo).length+2=2+(2*todo.length+2) by simp;omega,run_add]
    simp only [wire_cons,List.cons_append]
    rw [restore_pair,Option.bind_some]
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using ih (pre++[b])

theorem restore_cursor (k : Kind) (pre rest frames : List Bit) :
    run switchBody (2*pre.length+4)
      ((R k : Int),H (wire pre++0::B k::rest) frames)=
      some ((N k : Int),At (wire (pre++[B k])) rest frames) := by
  have first := restore_start k (wire pre++0::B k::rest) frames
  have last := restore_walk k pre [] rest frames
  rw [show 2*pre.length+4=2+(2*pre.length+2) by omega]
  exact run_chain switchBody first last

/-- Copy one bit to the caller-frame bank while the original marker is zero;
then restore that marker and advance the extraction cursor. -/
theorem copy_bit (k : Kind) (pre rest frames : List Bit) :
    ∃ steps, run switchBody steps
      ((C k : Int),At (wire pre) (0::B k::rest) frames)=
      some ((N k : Int),At (wire (pre++[B k])) rest (frames++[B k])) := by
  have home := run_chain switchBody
    (carry k (At (wire pre) (0::B k::rest) frames))
    (to_home k pre (0::B k::rest) frames)
  have push := push_bit k (0::(wire pre++0::B k::rest)) frames
  simp only [←H_RH] at push
  exact ⟨_,run_chain switchBody (run_chain switchBody home push)
    (restore_cursor k pre rest (frames++[B k]))⟩

theorem input_start (raw frames : List Bit) :
    run switchBody 2 (1395,H raw frames)=some (1397,At [] raw frames) := by
  simp [run,Switch.step,start_cell 0 (by decide),start_cell 1 (by decide),startRow,
    At,H,view,mirror,Tape.mk₂,Tape.mk',Tape.move,Tape.write]

theorem open_drive (pre rest frames : List Bit) :
    run switchBody 2 (1397,At (wire pre) (1::0::rest) frames)=
      some (1401,At (wire pre) (0::0::rest) frames) := by
  simp [run,Switch.step,start_cell 2 (by decide),start_cell 4 (by decide),startRow,
    At,view,mirror,Tape.mk₂,Tape.mk',Tape.move,Tape.write]

theorem payload_drive (pre rest frames : List Bit) (b : Bit) :
    run switchBody 2 (1398,At (wire pre) (1::b::rest) frames)=
      some (if b=0 then 1411 else 1406,At (wire pre) (0::b::rest) frames) := by
  fin_cases b <;> simp [run,Switch.step,start_cell 3 (by decide),start_cell 5 (by decide),
    startRow,At,view,mirror,Tape.mk₂,Tape.mk',Tape.move,Tape.write]

theorem copy_open (pre rest frames : List Bit) :
    ∃ steps, run switchBody steps (1397,At (wire pre) (1::0::rest) frames)=
      some (1398,At (wire (pre++[0])) rest (frames++[0])) := by
  obtain ⟨steps,h⟩ := copy_bit 0 pre rest frames
  exact ⟨_,run_chain switchBody (open_drive pre rest frames) h⟩

theorem copy_one (pre rest frames : List Bit) :
    ∃ steps, run switchBody steps (1398,At (wire pre) (1::1::rest) frames)=
      some (1398,At (wire (pre++[1])) rest (frames++[1])) := by
  obtain ⟨steps,h⟩ := copy_bit 1 pre rest frames
  exact ⟨_,run_chain switchBody (payload_drive pre rest frames 1) h⟩

theorem copy_close (pre rest frames : List Bit) :
    ∃ steps, run switchBody steps (1398,At (wire pre) (1::0::rest) frames)=
      some (1416,At (wire (pre++[0])) rest (frames++[0])) := by
  obtain ⟨steps,h⟩ := copy_bit 2 pre rest frames
  exact ⟨_,run_chain switchBody (payload_drive pre rest frames 0) h⟩

theorem copy_ones (n : Nat) (pre rest frames : List Bit) :
    ∃ steps, run switchBody steps
      (1398,At (wire pre) (wire (List.replicate n 1++[0])++rest) frames)=
      some (1416,At (wire (pre++List.replicate n 1++[0])) rest
        (frames++List.replicate n 1++[0])) := by
  induction n generalizing pre frames with
  | zero => simpa using copy_close pre rest frames
  | succ n ih =>
    obtain ⟨first,hfirst⟩ := copy_one pre (wire (List.replicate n 1++[0])++rest) frames
    obtain ⟨last,hlast⟩ := ih (pre++[1]) (frames++[1])
    refine ⟨first+last,?_⟩
    simpa only [List.replicate_succ,wire_cons,List.cons_append,List.append_assoc,
      List.nil_append] using run_chain switchBody hfirst hlast

/-- The actual cursor-copy loop copies a retained head of arbitrary width to
the frame bank, restores every cursor marker, and stops at the following bank. -/
theorem copy_head (n : Nat) (rest frames : List Bit) :
    ∃ steps, run switchBody steps (1395,H (wire (word n)++rest) frames)=
      some (1416,At (wire (word n)) rest (frames++word n)) := by
  obtain ⟨opening,hopening⟩ := copy_open [] (wire (List.replicate n 1++[0])++rest) frames
  obtain ⟨payload,hpayload⟩ := copy_ones n [0] rest (frames++[0])
  refine ⟨2+opening+payload,?_⟩
  have path := run_chain switchBody
    (run_chain switchBody (input_start (wire (word n)++rest) frames) hopening) hpayload
  simpa only [word,List.cons_append,List.nil_append,List.append_assoc] using path

end CatchUp.Machine.Lowering.Switch.Extract
