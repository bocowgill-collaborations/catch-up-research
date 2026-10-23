/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Spec
public import Mathlib.Tactic

/-!
# Concrete chess positions

Boards use two fixed-size arrays, indexed by rank and then file. Coordinates, pieces, moves,
and metadata reuse the reference's executable finite data types. The halfmove clock remains
an arbitrary natural number. Every raw reference position is representable; no legality or
reachability invariant is required by the round trips or the subsequent refinement theorems.
-/

@[expose] public section
namespace Chess.Exec

/-- A concrete board with eight ranks of eight squares. -/
abbrev Board := Vector (Vector (Option Piece) 8) 8

/-- Read a concrete board as the reference's square-indexed function. -/
def decodeBoard (board : Board) : Chess.Board := fun square ↦
  board[square.rank.val][square.file.val]

/-- Tabulate every square of a reference board into fixed-size arrays. -/
def encodeBoard (board : Chess.Board) : Board :=
  Vector.ofFn fun rank ↦ Vector.ofFn fun file ↦ board ⟨file, rank⟩

@[simp] theorem decode_encodeBoard (board : Chess.Board) :
    decodeBoard (encodeBoard board) = board := by
  funext square
  simp [decodeBoard, encodeBoard]

@[simp] theorem encode_decodeBoard (board : Board) :
    encodeBoard (decodeBoard board) = board := by
  exact Vector.ext fun rank hr ↦ Vector.ext fun file hf ↦ by simp [encodeBoard, decodeBoard]

/-- An executable position. The fields impose exactly the reference's raw data constraints. -/
structure Position where
  board : Board
  turn : Color
  castlingRights : CastlingRights
  enPassantTarget : Option Square
  halfmoveClock : ℕ
  deriving DecidableEq

/-- Decode all position fields without validation or normalization. -/
def decode (position : Position) : Chess.Position :=
  { board := decodeBoard position.board
    turn := position.turn
    castlingRights := position.castlingRights
    enPassantTarget := position.enPassantTarget
    halfmoveClock := position.halfmoveClock }

/-- Encode all position fields without validation or normalization. -/
def encode (position : Chess.Position) : Position :=
  { board := encodeBoard position.board
    turn := position.turn
    castlingRights := position.castlingRights
    enPassantTarget := position.enPassantTarget
    halfmoveClock := position.halfmoveClock }

/-- The concrete initial position. -/
def initial : Position := encode initialPosition

@[simp] theorem decode_encode (position : Chess.Position) :
    decode (encode position) = position := by
  simp [decode, encode]

@[simp] theorem encode_decode (position : Position) : encode (decode position) = position := by
  simp [decode, encode]

@[simp] theorem decode_initial : decode initial = initialPosition := decode_encode _

/-- M2 requires only representability, which is preserved even by unchecked raw updates. -/
theorem represents_all (position : Chess.Position) : ∃ concrete, decode concrete = position :=
  ⟨encode position, decode_encode position⟩

end Chess.Exec
