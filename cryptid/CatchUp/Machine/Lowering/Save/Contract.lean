import CatchUp.Machine.Lowering.Save.Copy
import CatchUp.Machine.Lowering.Switch.Extract

namespace CatchUp.Machine.Lowering.Save
open Turing ConjectureMachines Compilation Separate Words Switch Switch.Extract
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem copy_ones (n : Nat) (pre rest frames : List Bit) :
    ∃ steps, Switch.run saveBody steps (2775,Cursor (pre++List.replicate n 1) rest frames)=
      some (2775,Cursor pre (wire (List.replicate n 1)++rest)
        (frames++List.replicate n 1)) := by
  induction n generalizing rest frames with
  | zero => exact ⟨0,by simp [Switch.run]⟩
  | succ n ih =>
    obtain ⟨first,hfirst⟩ := copy_one (pre++List.replicate n 1) rest frames
    obtain ⟨last,hlast⟩ := ih (1::1::rest) (frames++[1])
    have path := run_chain saveBody hfirst hlast
    have frame_eq : frames++[1]++List.replicate n 1=frames++List.replicate (n+1) 1 := by
      simp only [List.replicate_succ,List.append_assoc,List.cons_append,List.nil_append]
    rw [frame_eq] at path
    refine ⟨first+last,?_⟩
    simpa only [List.replicate_succ',wire_append,wire_cons,wire_nil,List.append_assoc,
      List.cons_append,List.nil_append,List.append_nil] using path

/-- A whole word is copied backward. Its unary, self-delimiting representation
is symmetric; neither its value nor any original input cell is changed. -/
theorem copy_word (n : Nat) (pre rest frames : List Bit) :
    ∃ steps, Switch.run saveBody steps (2774,Cursor (pre++word n) rest frames)=
      some (2774,Cursor pre (wire (word n)++rest) (frames++word n++word 1)) := by
  let middle := List.replicate n (1 : Bit)
  obtain ⟨opening,hopening⟩ := copy_open (pre++[0]++middle) rest frames
  obtain ⟨ones,hones⟩ := copy_ones n (pre++[0]) (1::0::rest) (frames++[0])
  obtain ⟨closing,hclosing⟩ := copy_close pre (wire middle++1::0::rest)
    (frames++[0]++middle)
  have path := run_chain saveBody (run_chain saveBody hopening hones) hclosing
  refine ⟨opening+ones+closing,?_⟩
  simpa only [word,middle,List.append_assoc,List.cons_append,List.nil_append,
    wire_cons,wire_append,wire_nil,List.append_nil] using path

theorem scan_start (data frames : List Bit) :
    Switch.run saveBody 2 (2794,H (wire data) frames)=
      some (2796,At [] (wire data) frames) := by
  simp [Switch.run,Switch.step,scan_cell 0 (by decide),scan_cell 1 (by decide),scanRow,
    At,H,view,mirror,Tape.mk₂,Tape.mk',Tape.move,Tape.write]

theorem scan_pair (pre rest frames : List Bit) (b : Bit) :
    Switch.run saveBody 2 (2796,At (wire pre) (1::b::rest) frames)=
      some (2796,At (wire (pre++[b])) rest frames) := by
  simp [Switch.run,Switch.step,scan_cell 2 (by decide),scan_cell 1 (by decide),scanRow,
    At,view,mirror,wire_append,Tape.mk₂,Tape.mk',Tape.move,Tape.write,List.reverse_append]

theorem scan_end (pre frames : List Bit) :
    Switch.run saveBody 2 (2796,At (wire pre) [] frames)=
      some (2774,Cursor pre [] frames) := by
  simp [Switch.run,Switch.step,scan_cell 2 (by decide),scan_cell 3 (by decide),scanRow,
    At,Cursor,view,mirror,Tape.mk₂,Tape.mk',Tape.move,Tape.write]

theorem scan_walk (todo pre frames : List Bit) :
    Switch.run saveBody (2*todo.length+2) (2796,At (wire pre) (wire todo) frames)=
      some (2774,Cursor (pre++todo) [] frames) := by
  induction todo generalizing pre with
  | nil => simpa using scan_end pre frames
  | cons b todo ih =>
    rw [show 2*(b::todo).length+2=2+(2*todo.length+2) by simp;omega,Switch.run_add,wire_cons,
      scan_pair,Option.bind_some]
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using ih (pre++[b])

theorem scan (data frames : List Bit) :
    Switch.run saveBody (2*data.length+4) (2794,H (wire data) frames)=
      some (2774,Cursor data [] frames) := by
  rw [show 2*data.length+4=2+(2*data.length+2) by omega]
  exact run_chain saveBody (scan_start data frames) (scan_walk data [] frames)

/-- No more word is read at home, including for empty input. The exit returns
at exactly the original head position with the complete tape unchanged. -/
theorem finish (rest frames : List Bit) :
    Switch.run saveBody 4 (2774,Cursor [] rest frames)=some (-1,H rest frames) := by
  rw [cursor_nil]
  simp [Switch.run,Switch.step,drive_cell,exit_cell,H,view,mirror,Tape.mk₂,Tape.mk',
    Tape.move,Tape.write]

/-- All input words, and an arbitrary physical suffix, are preserved. The
sentinel already exists; the new words are saved in reverse order with tags. -/
theorem copy_input (data : List Nat) (rest frames : List Bit) :
    ∃ steps, Switch.run saveBody steps (2774,Cursor (encode data) rest frames)=
      some (-1,H (wire (encode data)++rest)
        (frames++encode (data.reverse.flatMap (fun n ↦ [n,1])))) := by
  induction data using List.reverseRecOn generalizing rest frames with
  | nil => simpa [encode] using Exists.intro 4 (finish rest frames)
  | append_singleton data n ih =>
    obtain ⟨first,hfirst⟩ := copy_word n (encode data) rest frames
    obtain ⟨last,hlast⟩ := ih (wire (word n)++rest) (frames++word n++word 1)
    have path := run_chain saveBody hfirst hlast
    refine ⟨first+last,?_⟩
    simpa only [encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.nil_append,List.cons_append,List.append_assoc,wire_append] using path

/-- Contract of the frozen actual 3723-state saveBody, for every input and
arbitrary earlier bit frames. Both sentinel pushes and the full scan are paid. -/
theorem save_bits (data : List Nat) (frames : List Bit) :
    ∃ steps, Switch.run saveBody steps (Int.ofNat saveBody.entry,banks (encode data) frames)=
      some (-1,banks (encode data) (frames++savedPayload data)) := by
  obtain ⟨opening,hopening⟩ := sentinel (wire (encode data)) frames
  have search := scan (encode data) (frames++word 0)
  obtain ⟨copy,hcopy⟩ := copy_input data [] (frames++word 0)
  have path := run_chain saveBody (run_chain saveBody hopening search) hcopy
  refine ⟨opening+(2*(encode data).length+4)+copy,?_⟩
  rw [show Int.ofNat saveBody.entry=(3310 : Int) by decide +kernel]
  simp only [List.append_nil,H_wire] at path
  simpa only [savedPayload,savedFrames,encode,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,List.append_assoc] using path

theorem save_correct (data frames : List Nat) :
    ∃ steps, Switch.run saveBody steps (Int.ofNat saveBody.entry,natBanks data frames)=
      some (-1,natBanks data (frames++savedFrames data)) := by
  simpa only [natBanks,savedPayload,encode,List.flatMap_append] using
    save_bits data (encode frames)

end CatchUp.Machine.Lowering.Save
