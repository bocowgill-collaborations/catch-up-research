import Cryptids.Compilation.BinaryTemplates

/-! The earlier DecoderShare read-restoration argument, generalized to arbitrary
labels/stores for the actual interpreter graph. No reserved tape cell is assumed. -/
namespace CatchUp.Machine.ReadShare
open Turing ConjectureMachines.Compilation
variable {L S : Type}

def window : (n : Nat) → Tape Bool → List.Vector Bool n
  | 0, _ => List.Vector.nil
  | n+1, T => T.head ::ᵥ window n (T.move .right)

theorem readAux_congr (n : Nat) (f g : List.Vector Bool n → TM1.Stmt Bool L S)
    (v : S) (T : Tape Bool)
    (equal : ∀ bits U, TM1.stepAux (f bits) v U = TM1.stepAux (g bits) v U) :
    TM1.stepAux (BinaryTemplates.readAux n f) v T =
      TM1.stepAux (BinaryTemplates.readAux n g) v T := by
  induction n generalizing T with
  | zero => exact equal _ _
  | succ n ih =>
    cases h : T.head <;>
      simp only [BinaryTemplates.readAux, TM1.stepAux, h, Bool.cond_false, Bool.cond_true]
    · exact ih _ _ _ (fun bits U => equal (false ::ᵥ bits) U)
    · exact ih _ _ _ (fun bits U => equal (true ::ᵥ bits) U)

theorem readAux_select (n : Nat) (p : S → Bool)
    (f g : List.Vector Bool n → TM1.Stmt Bool L S) (v : S) (T : Tape Bool) :
    TM1.stepAux (BinaryTemplates.readAux n (fun bits =>
      .branch (fun _ s => p s) (f bits) (g bits))) v T =
    TM1.stepAux (BinaryTemplates.readAux n (if p v then f else g)) v T := by
  apply readAux_congr
  intro bits U
  cases hp : p v <;> simp [TM1.stepAux, hp]

theorem readAux_returns (n : Nat) (f : List.Vector Bool n → TM1.Stmt Bool L S)
    (v : S) (T : Tape Bool) :
    TM1.stepAux (BinaryTemplates.readAux n
      (fun w => BinaryTemplates.move n .left (f w))) v T =
      TM1.stepAux (f (window n T)) v T := by
  induction n generalizing T with
  | zero => rfl
  | succ n ih =>
    cases h : T.head <;>
      simp only [BinaryTemplates.readAux, TM1.stepAux, h, Bool.cond_false, Bool.cond_true]
    · change TM1.stepAux (BinaryTemplates.readAux n
        (fun w => BinaryTemplates.move n .left (.move .left (f (false ::ᵥ w))))) v
          (T.move .right) = _
      rw [ih]
      simp [TM1.stepAux, window, h]
    · change TM1.stepAux (BinaryTemplates.readAux n
        (fun w => BinaryTemplates.move n .left (.move .left (f (true ::ᵥ w))))) v
          (T.move .right) = _
      rw [ih]
      simp [TM1.stepAux, window, h]

theorem read_returns {n : Nat} {G : Type} (dec : List.Vector Bool n → G)
    (f : G → TM1.Stmt Bool L S) (v : S) (T : Tape Bool) :
    TM1.stepAux (BinaryTemplates.read dec f) v T =
      TM1.stepAux (f (dec (window n T))) v T := readAux_returns n _ v T

end CatchUp.Machine.ReadShare
