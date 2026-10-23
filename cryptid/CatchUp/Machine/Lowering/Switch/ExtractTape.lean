import CatchUp.Machine.Lowering.Switch.ExtractRows

namespace CatchUp.Machine.Lowering.Switch.Extract
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Cursor at a physical cell of the left bank. pre/rest are physical cells,
not decoded bits; they can include the temporary 01 boundary marker. -/
def At (pre rest frames : List Bit) : Tape Bit :=
  view false (pre.reverse++0::0::0::wire frames) rest

def H (raw frames : List Bit) : Tape Bit := view false (0::wire frames) (0::0::raw)

theorem step_nat (m : Micro) (q : Nat) (T : Tape Bit) :
    Switch.step m ((q : Int),T)=
      (m.cell q T.head).map (fun (w,d,target) ↦ (target,(T.write w).move d)) := by
  simp only [Switch.step,show ¬(q : Int)<0 by omega,↓reduceIte,Int.toNat_natCast]

inductive Piece where
  | bit (value : Bit)
  | boundary

def pair : Piece → List Bit
  | .bit b => [1,b]
  | .boundary => [0,1]

def flat (ps : List Piece) : List Bit := ps.flatMap pair

theorem at_out (pre rest frames : List Bit) (a : Bit) :
    (At pre (a::rest) frames).move .left=At (pre++[a]) rest frames := by
  simp [At,view,mirror,Tape.mk₂,Tape.mk',Tape.move,List.reverse_append]

theorem blank_tail (rest : List Bit) :
    ListBlank.mk (rest.headI::rest.tail)=ListBlank.mk rest := by
  cases rest with
  | nil => exact Separate.blank_one
  | cons b rest => rfl

theorem at_in (pre rest frames : List Bit) (a : Bit) :
    (At (pre++[a]) rest frames).move .right=At pre (a::rest) frames := by
  simp [At,view,mirror,Tape.mk₂,Tape.mk',Tape.move,List.reverse_append]
  exact blank_tail rest

theorem at_in_pair (pre rest frames : List Bit) (a b : Bit) :
    ((At (pre++[a,b]) rest frames).move .right).move .right=
      At pre (a::b::rest) frames := by
  simp [At,view,mirror,Tape.mk₂,Tape.mk',Tape.move,List.reverse_append]
  exact congrArg (ListBlank.cons b) (blank_tail rest)

theorem at_home (rest frames : List Bit) :
    ((At [] rest frames).move .right).move .right=H rest frames := by
  simp [At,H,view,mirror,Tape.mk₂,Tape.mk',Tape.move]
  exact congrArg (ListBlank.cons 0) (blank_tail rest)

def mark : Piece → Bit | .bit _ => 1 | .boundary => 0
def value : Piece → Bit | .bit b => b | .boundary => 1

theorem pair_eq (p : Piece) : pair p=[mark p,value p] := by cases p <;> rfl

theorem at_in_piece (pre rest frames : List Bit) (p : Piece) :
    ((At (pre++pair p) rest frames).move .right).move .right=
      At pre (pair p++rest) frames := by
  cases p <;> exact at_in_pair pre rest frames _ _

theorem flat_snoc (ps : List Piece) (p : Piece) : flat (ps++[p])=flat ps++pair p := by
  simp [flat,List.flatMap_append]

theorem blank_pad (rest : List Bit) :
    ListBlank.mk (rest++[0,0])=ListBlank.mk rest := Quotient.sound' (Or.inr ⟨2,rfl⟩)

theorem at_pad (pre rest frames : List Bit) :
    At pre (rest++[0,0]) frames=At pre rest frames := by
  simp only [At,view,Tape.mk₂,blank_pad]

theorem flat_marked (pre tail : List Bit) :
    flat (pre.map Piece.bit++Piece.boundary::tail.map Piece.bit)=
      wire pre++0::1::wire tail := by
  simp [flat,wire,pair,List.flatMap_append,List.flatMap_map]

end CatchUp.Machine.Lowering.Switch.Extract
