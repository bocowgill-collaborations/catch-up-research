/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Adjudication.Projection

/-!
# Exact dead-position decision

The finite directed search follows every raw legal-ply edge, including continuations beyond
game-level draw rules. Its finiteness argument projects away only the irrelevant halfmove clock.
The baseline is mathematically total but can require an astronomical search; it is not claimed
to be practical on ordinary chess positions.
-/

@[expose] public section
namespace Chess.Adjudication
open Relation

instance (position : Chess.Position) : Decidable (HasLegalPly position) :=
  inferInstanceAs (Decidable (∃ ply, IsLegalPly position ply))

instance (position : Chess.Position) : Decidable (IsCheckmate position) :=
  inferInstanceAs (Decidable (InCheck position.board position.turn ∧ ¬HasLegalPly position))

instance (position : Chess.Position) : Decidable (IsStalemate position) :=
  inferInstanceAs (Decidable (¬InCheck position.board position.turn ∧ ¬HasLegalPly position))

/-- Every raw legal successor of a projected position. -/
def successors (key : Key) : List Key :=
  (Exec.legalPlies (Exec.encode (key.position 0))).map
    (fun ply ↦ project (Exec.positionAfter (key.position 0) ply))

theorem mem_successors (source target : Key) :
    target ∈ successors source ↔ Key.Next source target := by
  simp only [successors, List.mem_map, Exec.mem_legalPlies, Exec.decode_encode,
    Exec.positionAfter_eq, Key.Next]
  exact exists_congr fun ply ↦ and_congr_right fun _ ↦ eq_comm

/-- Executable checkmate test on projected data. -/
def isMate (key : Key) : Bool := decide (IsCheckmate (key.position 0))

/-- A checkmate is reachable in the exact finite move graph. -/
def canReachMate (key : Key) : Bool := FiniteSearch.reachableTarget successors isMate key

theorem canReachMate_iff (key : Key) : canReachMate key = true ↔
    ∃ finish, ReflTransGen Key.Next key finish ∧ IsCheckmate (finish.position 0) := by
  have edge_eq : FiniteSearch.Edge successors = Key.Next :=
    funext fun a ↦ funext fun b ↦ propext (mem_successors a b)
  simp only [canReachMate, FiniteSearch.reachableTarget_iff, edge_eq, isMate, decide_eq_true_eq]

theorem dead_iff_no_projected_mate (position : Chess.Position) :
    IsDeadPosition position ↔
      ¬∃ finish, ReflTransGen Key.Next (project position) finish ∧
        IsCheckmate (finish.position 0) := by
  constructor
  · rintro dead ⟨finish, path, mate⟩
    obtain ⟨next, lifted, projected⟩ := lift_path path
    exact dead next lifted ((checkmate_position next 0).mp (projected.symm ▸ mate))
  · intro absent next path mate
    exact absent ⟨project next, project_path path, (checkmate_position next 0).mpr mate⟩

/-- Exact dead-position Boolean. Its search has no heuristic or external oracle. -/
def isDead (position : Exec.Position) : Bool := !(canReachMate (project (Exec.decode position)))

@[simp] theorem isDead_iff (position : Exec.Position) :
    isDead position = true ↔ IsDeadPosition (Exec.decode position) := by
  simp only [isDead, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, canReachMate_iff,
    dead_iff_no_projected_mate]

instance (position : Chess.Position) : Decidable (IsDeadPosition position) :=
  decidable_of_iff (isDead (Exec.encode position) = true)
    (by simpa only [Exec.decode_encode] using isDead_iff (Exec.encode position))

end Chess.Adjudication
