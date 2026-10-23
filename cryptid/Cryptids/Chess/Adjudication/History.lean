/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Adjudication.DeadPosition

/-!
# Exact history and repetition

Retain the complete history. Repetition equality compares the reference's board, side, rights,
and legal en-passant possibilities; neither the halfmove clock nor an inert raw en-passant
target changes repetition equality. Occurrences count distinct historical indices, so repeated
equal positions are counted separately. The cardinality theorem matches the frozen definition
which uses an injective map from `Fin n` into the matching indices.
-/

@[expose] public section
namespace Chess.Adjudication

/-- Executable games retain every prior position, newest first. -/
structure Game where
  current : Exec.Position
  previous : List Exec.Position
  deriving DecidableEq

def decodeGame (game : Game) : Chess.Game :=
  ⟨Exec.decode game.current, game.previous.map Exec.decode⟩

def encodeGame (game : Chess.Game) : Game :=
  ⟨Exec.encode game.current, game.previous.map Exec.encode⟩

@[simp] theorem decode_encodeGame (game : Chess.Game) : decodeGame (encodeGame game) = game := by
  simp [decodeGame, encodeGame, List.map_map, Function.comp_def]

@[simp] theorem encode_decodeGame (game : Game) : encodeGame (decodeGame game) = game := by
  simp [decodeGame, encodeGame, List.map_map, Function.comp_def]

def Game.initial : Game := ⟨Exec.initial, []⟩

@[simp] theorem decode_initialGame : decodeGame Game.initial = Chess.Game.initial := by
  simp [Game.initial, decodeGame, Chess.Game.initial]

/-- Extend full history by an unchecked raw move. -/
def Game.play (game : Game) (ply : Ply) : Game :=
  ⟨Exec.applyPly game.current ply, game.current :: game.previous⟩

theorem decode_play (game : Game) (ply : Ply) :
    decodeGame (game.play ply) = (decodeGame game).play ply := by
  simp [decodeGame, Game.play, Chess.Game.play, Exec.decode_applyPly]

theorem samePosition_self (position : Chess.Position) : SamePosition position position :=
  ⟨fun _ ↦ rfl, rfl, rfl, fun _ ↦ Iff.rfl⟩

theorem samePosition_project (first second : Chess.Position) :
    SamePosition ((project first).position 0) ((project second).position 0) ↔
      SamePosition first second := by
  rfl

theorem samePosition_of_project_eq {first second : Chess.Position}
    (equal : project first = project second) : SamePosition first second := by
  apply (samePosition_project first second).mp
  rw [← equal]
  exact samePosition_self _

def decideSamePosition (first second : Chess.Position) : Decidable (SamePosition first second) := by
  unfold SamePosition
  infer_instance

instance (first second : Chess.Position) : Decidable (SamePosition first second) :=
  if equal : project first = project second then isTrue (samePosition_of_project_eq equal)
  else decideSamePosition first second

def samePosition (first second : Exec.Position) : Bool :=
  decide (SamePosition (Exec.decode first) (Exec.decode second))

@[simp] theorem samePosition_iff (first second : Exec.Position) :
    samePosition first second = true ↔ SamePosition (Exec.decode first) (Exec.decode second) := by
  simp [samePosition]

/-- The number of distinct history indices equal to the current position for repetition. -/
def occurrences (game : Chess.Game) : ℕ :=
  Fintype.card {i : Fin game.positions.length // SamePosition (game.positions.get i) game.current}

theorem repeated_iff_occurrences (game : Chess.Game) (n : ℕ) :
    game.RepeatedAtLeast n ↔ n ≤ occurrences game := by
  unfold Chess.Game.RepeatedAtLeast occurrences
  have embedding_iff := Function.Embedding.nonempty_iff_card_le (α := Fin n)
    (β := {i : Fin game.positions.length // SamePosition (game.positions.get i) game.current})
  simp only [Fintype.card_fin] at embedding_iff
  rw [← embedding_iff]
  constructor
  · rintro ⟨indices, injective, matching⟩
    exact ⟨⟨fun i ↦ ⟨indices i, matching i⟩,
      fun i j equal ↦ injective (congrArg Subtype.val equal)⟩⟩
  · rintro ⟨embedding⟩
    exact ⟨fun i ↦ (embedding i).val,
      fun i j equal ↦ embedding.injective (Subtype.ext equal), fun i ↦ (embedding i).property⟩

instance (game : Chess.Game) (n : ℕ) : Decidable (game.RepeatedAtLeast n) :=
  decidable_of_iff (n ≤ occurrences game) (repeated_iff_occurrences game n).symm

/-- An executable occurrence count over the complete decoded history. -/
def Game.occurrences (game : Game) : ℕ := Chess.Adjudication.occurrences (decodeGame game)

def Game.repeated (game : Game) (n : ℕ) : Bool := decide (n ≤ game.occurrences)

@[simp] theorem repeated_iff (game : Game) (n : ℕ) :
    game.repeated n = true ↔ (decodeGame game).RepeatedAtLeast n := by
  exact ⟨fun h ↦ (repeated_iff_occurrences _ _).mpr (of_decide_eq_true h),
    fun h ↦ decide_eq_true ((repeated_iff_occurrences _ _).mp h)⟩

end Chess.Adjudication
