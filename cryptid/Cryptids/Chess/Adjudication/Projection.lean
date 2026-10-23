/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Adjudication.Search

/-!
# Clock-free legal-move graph

The graph retains the entire board, turn, castling rights, and raw en-passant target. Only the
halfmove clock is removed. Legal-ply reachability is unrestricted: game-level terminal results
do not cut off graph edges. Projection, path lifting, and checkmate preservation justify using
this finite graph for the reference's exact dead-position predicate.
-/

@[expose] public section
namespace Chess.Adjudication
open Relation

/-- The raw position data on which legal plies and checkmate depend. -/
structure Key where
  board : Chess.Board
  turn : Color
  castlingRights : CastlingRights
  enPassantTarget : Option Square
  deriving DecidableEq

instance : Finite Key := Finite.of_injective
  (fun k : Key ↦ (k.board, k.turn, k.castlingRights.whiteKingside,
    k.castlingRights.whiteQueenside, k.castlingRights.blackKingside,
    k.castlingRights.blackQueenside, k.enPassantTarget))
  (by
    intro a b h
    cases a with | mk ab aturn ar ae =>
      cases b with | mk bb bt br be =>
        cases ar
        cases br
        simpa only [Prod.mk.injEq, Key.mk.injEq, CastlingRights.mk.injEq, and_assoc] using h)

/-- Remove only the halfmove clock. -/
def project (position : Chess.Position) : Key :=
  ⟨position.board, position.turn, position.castlingRights, position.enPassantTarget⟩

/-- Restore an arbitrary clock. Zero is sufficient for graph exploration. -/
def Key.position (key : Key) (clock : ℕ := 0) : Chess.Position :=
  ⟨key.board, key.turn, key.castlingRights, key.enPassantTarget, clock⟩

@[simp] theorem project_position (key : Key) (clock : ℕ) : project (key.position clock) = key := by
  rfl

@[simp] theorem legal_position (position : Chess.Position) (clock : ℕ) (ply : Ply) :
    IsLegalPly ((project position).position clock) ply ↔ IsLegalPly position ply := by
  rfl

@[simp] theorem checkmate_position (position : Chess.Position) (clock : ℕ) :
    IsCheckmate ((project position).position clock) ↔ IsCheckmate position := by
  rfl

theorem project_applyPly (position : Chess.Position) (clock : ℕ) (ply : Ply) :
    project (Chess.applyPly ((project position).position clock) ply) =
      project (Chess.applyPly position ply) := by
  rfl

/-- One unrestricted legal edge in the projected graph. -/
def Key.Next (source target : Key) : Prop :=
  ∃ ply, IsLegalPly (source.position 0) ply ∧
    target = project (Chess.applyPly (source.position 0) ply)

theorem project_edge {source target : Chess.Position} (edge : Chess.Position.Next source target) :
    Key.Next (project source) (project target) := by
  rcases edge with ⟨ply, legal, rfl⟩
  exact ⟨ply, (legal_position source 0 ply).mpr legal, (project_applyPly source 0 ply).symm⟩

theorem lift_edge {source : Chess.Position} {target : Key}
    (edge : Key.Next (project source) target) :
    ∃ next, Chess.Position.Next source next ∧ project next = target := by
  rcases edge with ⟨ply, legal, rfl⟩
  exact ⟨Chess.applyPly source ply, ⟨ply, (legal_position source 0 ply).mp legal, rfl⟩,
    (project_applyPly source 0 ply).symm⟩

theorem project_path {source target : Chess.Position}
    (path : ReflTransGen Chess.Position.Next source target) :
    ReflTransGen Key.Next (project source) (project target) :=
  path.lift project (fun _ _ ↦ project_edge)

theorem lift_path {source : Chess.Position} {target : Key}
    (path : ReflTransGen Key.Next (project source) target) :
    ∃ next, ReflTransGen Chess.Position.Next source next ∧ project next = target := by
  induction path with
  | refl => exact ⟨source, .refl, rfl⟩
  | tail path edge ih =>
      rcases ih with ⟨middle, earlier, decoded⟩
      obtain ⟨next, step, projected⟩ := lift_edge (decoded.symm ▸ edge)
      exact ⟨next, earlier.tail step, projected⟩

end Chess.Adjudication
