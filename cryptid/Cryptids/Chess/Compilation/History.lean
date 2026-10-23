/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Compilation.Encoding

/-! # Exact repetition interface

Distinct raw en-passant targets can be ignored for repetition only when neither position
admits a legal en-passant capture. This statement applies even to arbitrary raw positions.
-/

@[expose] public section

namespace Chess.Compilation.History

open Adjudication

def HasLegalEnPassant (position : Chess.Position) : Prop :=
  ∃ ply, IsLegalPly position ply ∧ ∃ piece,
    position.board ply.src = some piece ∧ IsEnPassant position piece ply

instance (position : Chess.Position) : Decidable (HasLegalEnPassant position) := by
  unfold HasLegalEnPassant
  infer_instance

/-- An exact short-circuit form of the frozen repetition relation. -/
theorem samePosition_iff (first second : Chess.Position) :
    SamePosition first second ↔
      (∀ square, first.board square = second.board square) ∧
      first.turn = second.turn ∧ first.castlingRights = second.castlingRights ∧
      (first.enPassantTarget = second.enPassantTarget ∨
        (¬HasLegalEnPassant first ∧ ¬HasLegalEnPassant second)) := by
  constructor
  · rintro ⟨board, turn, rights, captures⟩
    refine ⟨board, turn, rights, ?_⟩
    by_cases equal : first.enPassantTarget = second.enPassantTarget
    · exact Or.inl equal
    · apply Or.inr
      constructor
      · rintro ⟨ply, legal, piece, present, capture⟩
        obtain ⟨_, other, _, otherCapture⟩ := (captures ply).mp ⟨legal, piece, present, capture⟩
        exact equal (capture.2.2.1.trans otherCapture.2.2.1.symm)
      · rintro ⟨ply, legal, piece, present, capture⟩
        obtain ⟨_, other, _, otherCapture⟩ := (captures ply).mpr ⟨legal, piece, present, capture⟩
        exact equal (otherCapture.2.2.1.trans capture.2.2.1.symm)
  · rintro ⟨board, turn, rights, equal | absent⟩
    · apply samePosition_of_project_eq
      simp only [project, Key.mk.injEq]
      exact ⟨funext board, turn, rights, equal⟩
    · refine ⟨board, turn, rights, ?_⟩
      intro ply
      constructor
      · intro capture
        exact (absent.1 ⟨ply, capture⟩).elim
      · intro capture
        exact (absent.2 ⟨ply, capture⟩).elim

end Chess.Compilation.History
