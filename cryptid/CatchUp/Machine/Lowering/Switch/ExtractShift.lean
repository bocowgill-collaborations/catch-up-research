import CatchUp.Machine.Lowering.Switch.ExtractTape

namespace CatchUp.Machine.Lowering.Switch.Extract
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem copy_pair (flag : Bit) (pre rest frames : List Bit) (u v : Bit) (p : Piece) :
    run switchBody 8 ((S flag 7 : Int),At (pre++[u,v]) (pair p++rest) frames)=
      some ((S flag 7 : Int),At (pre++pair p++pair p) rest frames) := by
  cases p with
  | bit b =>
    fin_cases b <;> simp [run,step_nat,shift_cell,shiftRow,pair,At,view,mirror,
      Tape.mk₂,Tape.mk',Tape.move,Tape.write,List.reverse_append,Int.ofNat_eq_natCast]
  | boundary =>
    simp [run,step_nat,shift_cell,shiftRow,pair,At,view,mirror,
      Tape.mk₂,Tape.mk',Tape.move,Tape.write,List.reverse_append,Int.ofNat_eq_natCast]

theorem copy_stop (flag : Bit) (pre frames : List Bit) (u v : Bit) :
    run switchBody 6 ((S flag 7 : Int),At (pre++[u,v]) [0,0] frames)=
      some ((S flag 32 : Int),((At pre [] frames).move .right).move .right) := by
  simp [run,step_nat,shift_cell,shiftRow,At,view,mirror,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write,List.reverse_append,Int.ofNat_eq_natCast]

/-- Shift every nonblank pair, including temporary boundary markers, and copy
the final blank pair. Earlier physical cells and all caller frames survive. -/
theorem copy_all (flag : Bit) (ps : List Piece) (pre frames : List Bit) (u v : Bit) :
    run switchBody (8*ps.length+6)
      ((S flag 7 : Int),At (pre++[u,v]) (flat ps++[0,0]) frames)=
      some ((S flag 32 : Int),
        ((At (pre++flat ps) [] frames).move .right).move .right) := by
  induction ps generalizing pre u v with
  | nil => simpa [flat] using copy_stop flag pre frames u v
  | cons p ps ih =>
    have first := copy_pair flag pre (flat ps++[0,0]) frames u v p
    have rest := ih (pre++pair p) (mark p) (value p)
    rw [←pair_eq p] at rest
    rw [show 8*(p::ps).length+6=8+(8*ps.length+6) by simp;omega]
    simpa only [flat,List.flatMap_cons,List.append_assoc] using run_chain switchBody first rest

def findCost : Piece → Nat | .bit _ => 2 | .boundary => 4

theorem find_pair (flag : Bit) (pre rest frames : List Bit) (p : Piece) :
    run switchBody (findCost p) ((S flag 32 : Int),At pre (pair p++rest) frames)=
      some ((S flag 32 : Int),
        ((At pre (pair p++rest) frames).move .right).move .right) := by
  cases p with
  | bit b => simp [findCost,pair,run,step_nat,shift_cell,shiftRow,At,view,mirror,
      Tape.mk₂,Tape.mk',Tape.move,Tape.write,Int.ofNat_eq_natCast]
  | boundary => simp [findCost,pair,run,step_nat,shift_cell,shiftRow,At,view,mirror,
      Tape.mk₂,Tape.mk',Tape.move,Tape.write,Int.ofNat_eq_natCast]

theorem find_home_base (flag : Bit) (rest frames : List Bit) :
    run switchBody 2 ((S flag 32 : Int),H rest frames)=
      some ((S flag 0 : Int),H rest frames) := by
  simp [run,step_nat,shift_cell,shiftRow,H,view,mirror,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write,Int.ofNat_eq_natCast]

/-- The home scan crosses every ordinary or 01 boundary pair without changing
it. Only the true three-cell separator returns control to the deletion loop. -/
theorem find_home (flag : Bit) (ps : List Piece) (rest frames : List Bit) :
    ∃ steps, run switchBody steps
      ((S flag 32 : Int),((At (flat ps) rest frames).move .right).move .right)=
      some ((S flag 0 : Int),H (flat ps++rest) frames) := by
  induction ps using List.reverseRecOn generalizing rest with
  | nil =>
    exact ⟨2,by simpa only [flat,List.flatMap_nil,List.nil_append,at_home] using
      find_home_base flag rest frames⟩
  | append_singleton ps p ih =>
    obtain ⟨steps,h⟩ := ih (pair p++rest)
    refine ⟨findCost p+steps,?_⟩
    rw [flat_snoc,at_in_piece]
    simpa only [List.append_assoc] using
      run_chain switchBody (find_pair flag (flat ps) rest frames p) h

theorem copy_then_home (flag : Bit) (ps : List Piece) (frames : List Bit) (u v : Bit) :
    ∃ steps, run switchBody steps ((S flag 7 : Int),At [u,v] (flat ps) frames)=
      some ((S flag 0 : Int),H (flat ps) frames) := by
  have first := copy_all flag ps [] frames u v
  rw [at_pad] at first
  obtain ⟨steps,last⟩ := find_home flag ps [] frames
  simp only [List.append_nil] at last
  exact ⟨_,run_chain switchBody first last⟩

theorem delete_first (flag : Bit) (rest frames : List Bit) (b : Bit) :
    run switchBody 4 ((S flag 0 : Int),H (1::b::rest) frames)=
      some ((S flag 7 : Int),At [1,b] rest frames) := by
  simp [run,step_nat,shift_cell,shiftRow,At,H,view,mirror,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write,Int.ofNat_eq_natCast]

theorem finish_boundary (flag : Bit) (tail frames : List Bit) :
    run switchBody 6 ((S flag 0 : Int),H (0::1::wire tail) frames)=
      some (15384,H (flag::0::wire tail) frames) := by
  simp [run,step_nat,shift_cell,shiftRow,H,view,mirror,
    Tape.mk₂,Tape.mk',Tape.move,Tape.write,Int.ofNat_eq_natCast]

/-- The actual deletion loop removes any length of ordinary bit pairs up to
the temporary boundary. Both boundary flags and all caller frames are covered. -/
theorem shift_prefix (flag : Bit) (pre tail frames : List Bit) :
    ∃ steps, run switchBody steps
      ((S flag 0 : Int),H (wire pre++0::1::wire tail) frames)=
      some (15384,H (flag::0::wire tail) frames) := by
  induction pre with
  | nil => exact ⟨6,finish_boundary flag tail frames⟩
  | cons b pre ih =>
    obtain ⟨round,hr⟩ := copy_then_home flag
      (pre.map Piece.bit++Piece.boundary::tail.map Piece.bit) frames 1 b
    rw [flat_marked] at hr
    obtain ⟨steps,hs⟩ := ih
    exact ⟨_,run_chain switchBody
      (run_chain switchBody (delete_first flag (wire pre++0::1::wire tail) frames b) hr) hs⟩

end CatchUp.Machine.Lowering.Switch.Extract
