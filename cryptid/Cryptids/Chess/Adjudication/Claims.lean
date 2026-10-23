/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Adjudication.History

/-!
# Current-position and intended-move draw claims

Claim eligibility does not execute the intended move. It witnesses one legal raw ply whose
resulting position satisfies the threshold. Claiming remains a separate optional action.
-/

@[expose] public section
namespace Chess.Adjudication

def canClaimThreefold (game : Game) : Bool :=
  game.repeated 3 || (Exec.legalPlies game.current).any (fun ply ↦ (game.play ply).repeated 3)

@[simp] theorem canClaimThreefold_iff (game : Game) :
    canClaimThreefold game = true ↔ CanClaimThreefold (decodeGame game) := by
  simp only [canClaimThreefold, Bool.or_eq_true, List.any_eq_true, repeated_iff,
    Exec.mem_legalPlies, decode_play, CanClaimThreefold]
  rfl

def canClaimFiftyMove (game : Game) : Bool :=
  decide (100 ≤ (Exec.decode game.current).halfmoveClock) ||
    (Exec.legalPlies game.current).any (fun ply ↦
      decide (100 ≤ (Exec.decode (Exec.applyPly game.current ply)).halfmoveClock))

@[simp] theorem canClaimFiftyMove_iff (game : Game) :
    canClaimFiftyMove game = true ↔ CanClaimFiftyMove (decodeGame game) := by
  simp only [canClaimFiftyMove, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq,
    Exec.mem_legalPlies, CanClaimFiftyMove, Exec.decode_applyPly]
  rfl

def canClaimDraw (game : Game) : Bool := canClaimThreefold game || canClaimFiftyMove game

@[simp] theorem canClaimDraw_iff (game : Game) :
    canClaimDraw game = true ↔ CanClaimDraw (decodeGame game) := by
  simp [canClaimDraw, CanClaimDraw]

instance (game : Chess.Game) : Decidable (CanClaimDraw game) :=
  decidable_of_iff (canClaimDraw (encodeGame game) = true)
    (by simpa only [decode_encodeGame] using canClaimDraw_iff (encodeGame game))

end Chess.Adjudication
