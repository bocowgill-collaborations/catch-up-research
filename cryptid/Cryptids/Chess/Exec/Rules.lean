/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Exec.Encoding

/-!
# Executable decisions and unchecked updates

The instances below decide finite reference predicates by inspection and finite enumeration.
The reference's classical choices occur only in propositions and proofs. The executable update
functions use these constructive decisions instead of calling noncomputable reference updates.
-/

@[expose] public section
namespace Chess.Exec

instance : Fintype Color := ⟨{.white, .black}, by intro color; cases color <;> simp⟩
instance : Fintype PieceKind :=
  ⟨{.king, .queen, .rook, .bishop, .knight, .pawn}, by intro kind; cases kind <;> simp⟩
deriving instance Fintype for Piece
instance : Fintype CastleSide := ⟨{.kingside, .queenside}, by intro side; cases side <;> simp⟩
deriving instance Fintype for Ply

instance (a b x : ℕ) : Decidable (StrictlyBetween a b x) :=
  inferInstanceAs (Decidable (min a b < x ∧ x < max a b))

instance (src dst square : Square) : Decidable (OnOpenSegment src dst square) := by
  unfold OnOpenSegment
  infer_instance

instance (board : Chess.Board) (src dst : Square) : Decidable (PathClear board src dst) :=
  inferInstanceAs (Decidable (∀ square, OnOpenSegment src dst square → board square = none))

instance (color : Color) (src dst : Square) : Decidable (PawnAttacks color src dst) := by
  unfold PawnAttacks
  cases color <;> infer_instance

instance (board : Chess.Board) (piece : Piece) (src dst : Square) :
    Decidable (PieceAttacks board piece src dst) := by
  unfold PieceAttacks
  cases piece.kind <;> infer_instance

instance (board : Chess.Board) (color : Color) (square : Square) :
    Decidable (IsAttackedBy board color square) :=
  inferInstanceAs (Decidable (∃ src piece, board src = some piece ∧ piece.color = color ∧
    PieceAttacks board piece src square))

instance (board : Chess.Board) (color : Color) : Decidable (InCheck board color) :=
  inferInstanceAs (Decidable (∃ square, board square = some ⟨color, .king⟩ ∧
    IsAttackedBy board color.other square))

instance (position : Chess.Position) (piece : Piece) (ply : Ply) :
    Decidable (IsEnPassant position piece ply) := by
  unfold IsEnPassant
  infer_instance

instance (board : Chess.Board) (color : Color) (src dst : Square) :
    Decidable (IsPawnAdvance board color src dst) := by
  unfold IsPawnAdvance
  cases color <;> infer_instance

instance (board : Chess.Board) (color : Color) (src dst : Square) :
    Decidable (IsPawnDoubleAdvance board color src dst) := by
  unfold IsPawnDoubleAdvance
  cases color <;> infer_instance

instance (board : Chess.Board) (piece : Piece) (src dst : Square) :
    Decidable (IsPawnCapture board piece src dst) := by
  unfold IsPawnCapture
  infer_instance

/-- Whether this requested move reaches a pawn's last rank. -/
def promotionNeeded (piece : Piece) (ply : Ply) : Prop :=
  piece.kind = .pawn ∧ match piece.color with
    | .white => ply.dst.rank = 7
    | .black => ply.dst.rank = 0

instance (piece : Piece) (ply : Ply) : Decidable (promotionNeeded piece ply) := by
  unfold promotionNeeded
  cases piece.color <;> infer_instance

instance (piece : Piece) (ply : Ply) : Decidable (ValidPromotion piece ply) :=
  decidable_of_iff
    (if promotionNeeded piece ply then
      ∃ kind, ply.promotion = some kind ∧ kind ≠ .king ∧ kind ≠ .pawn
    else ply.promotion = none)
    (by unfold ValidPromotion promotionNeeded; congr!)

instance (position : Chess.Position) (ply : Ply) : Decidable (DestinationAllowed position ply) := by
  unfold DestinationAllowed
  cases position.board ply.dst <;> infer_instance

instance (position : Chess.Position) (piece : Piece) (ply : Ply) :
    Decidable (IsCastling position piece ply) := by
  unfold IsCastling
  infer_instance

instance (position : Chess.Position) (piece : Piece) (ply : Ply) :
    Decidable (PieceMovement position piece ply) := by
  unfold PieceMovement
  cases piece.kind <;> infer_instance

instance (position : Chess.Position) (ply : Ply) : Decidable (IsPseudoLegal position ply) := by
  unfold IsPseudoLegal
  infer_instance

/-- Executable board effect, including the reference's behavior on illegal requests. -/
def boardAfter (position : Chess.Position) (ply : Ply) : Chess.Board :=
  match position.board ply.src with
  | none => position.board
  | some piece => fun square ↦
      if square = ply.dst then
        some (movedPiece piece ply)
      else if square = ply.src then
        none
      else
        match castleSide? piece ply with
        | some side =>
            if square = castleRookDestination piece.color side then
              some ⟨piece.color, .rook⟩
            else if square = rookHome piece.color side then
              none
            else
              position.board square
        | none =>
            if IsEnPassant position piece ply ∧ square = enPassantCapturedSquare ply then
              none
            else
              position.board square

/-- Board refinement holds for all raw positions and all plies. -/
theorem boardAfter_eq (position : Chess.Position) (ply : Ply) :
    boardAfter position ply = Chess.applyBoard position ply := by
  unfold boardAfter Chess.applyBoard
  congr!

instance (position : Chess.Position) (ply : Ply) : Decidable (IsLegalPly position ply) :=
  decidable_of_iff (IsPseudoLegal position ply ∧ ¬InCheck (boardAfter position ply) position.turn)
    (by rw [boardAfter_eq]; rfl)

/-- Executable en-passant metadata, cleared unless this is a double pawn advance. -/
def enPassantAfter (position : Chess.Position) (ply : Ply) : Option Square :=
  match position.board ply.src with
  | some piece =>
      if piece.kind = .pawn ∧
          IsPawnDoubleAdvance position.board piece.color ply.src ply.dst then
        match piece.color with
        | .white => some ⟨ply.src.file, 2⟩
        | .black => some ⟨ply.src.file, 5⟩
      else none
  | none => none

theorem enPassantAfter_eq (position : Chess.Position) (ply : Ply) :
    enPassantAfter position ply = nextEnPassantTarget position ply := by
  unfold enPassantAfter nextEnPassantTarget
  congr!

instance (position : Chess.Position) (ply : Ply) : Decidable (IsCapture position ply) := by
  unfold IsCapture
  infer_instance

/-- Executable raw position update, without legality or terminal checks. -/
def positionAfter (position : Chess.Position) (ply : Ply) : Chess.Position :=
  let isPawn := ∃ piece, position.board ply.src = some piece ∧ piece.kind = .pawn
  { board := boardAfter position ply
    turn := position.turn.other
    castlingRights := nextCastlingRights position ply
    enPassantTarget := enPassantAfter position ply
    halfmoveClock := if isPawn ∨ IsCapture position ply then 0 else position.halfmoveClock + 1 }

theorem positionAfter_eq (position : Chess.Position) (ply : Ply) :
    positionAfter position ply = Chess.applyPly position ply := by
  simp only [positionAfter, Chess.applyPly, boardAfter_eq, enPassantAfter_eq]
  congr!

/-- Concrete board update. -/
def applyBoard (position : Position) (ply : Ply) : Board :=
  encodeBoard (boardAfter (decode position) ply)

/-- Concrete position update. It preserves the reference's unchecked-update behavior. -/
def applyPly (position : Position) (ply : Ply) : Position :=
  encode (positionAfter (decode position) ply)

theorem decode_applyBoard (position : Position) (ply : Ply) :
    decodeBoard (applyBoard position ply) = Chess.applyBoard (decode position) ply := by
  simp [applyBoard, boardAfter_eq]

/-- All five fields agree, for every raw position and every requested move. -/
theorem decode_applyPly (position : Position) (ply : Ply) :
    decode (applyPly position ply) = Chess.applyPly (decode position) ply := by
  simp [applyPly, positionAfter_eq]

/-- Encoding commutes with every reference update, so no narrower invariant is needed. -/
theorem applyPly_encode (position : Chess.Position) (ply : Ply) :
    applyPly (encode position) ply = encode (Chess.applyPly position ply) := by
  simp [applyPly, positionAfter_eq]

/-- Every legal concrete transition is a reference position transition. -/
theorem next_applyPly (position : Position) (ply : Ply)
    (legal : IsLegalPly (decode position) ply) :
    Chess.Position.Next (decode position) (decode (applyPly position ply)) :=
  ⟨ply, legal, decode_applyPly position ply⟩

/-- Any reference invariant preserved by legal moves is preserved by the executable update. -/
theorem invariant_applyPly {invariant : Chess.Position → Prop}
    (preserved : ∀ p m, invariant p → IsLegalPly p m → invariant (Chess.applyPly p m))
    (position : Position) (ply : Ply) (holds : invariant (decode position))
    (legal : IsLegalPly (decode position) ply) : invariant (decode (applyPly position ply)) := by
  simpa only [decode_applyPly] using preserved (decode position) ply holds legal

/-- Legal game steps preserve the reference's exact reachable-history contract. -/
theorem reachable_applyPly (game : Game) (position : Position) (ply : Ply)
    (reachable : Reachable game) (decoded : decode position = game.current)
    (legal : IsLegalAction game (.play ply)) :
    Reachable { current := decode (applyPly position ply)
                previous := game.current :: game.previous } := by
  simpa only [Game.play, decode_applyPly, decoded] using Reachable.play reachable legal

/-- Check one move against the raw move rules, without game-history adjudication. -/
def isLegal (position : Position) (ply : Ply) : Bool := decide (IsLegalPly (decode position) ply)

@[simp] theorem isLegal_iff (position : Position) (ply : Ply) :
    isLegal position ply = true ↔ IsLegalPly (decode position) ply := by
  simp [isLegal]

/-- A checked move update; automatic outcomes and claims belong to M3. -/
def play? (position : Position) (ply : Ply) : Option Position :=
  if isLegal position ply then some (applyPly position ply) else none

theorem play?_eq_some (position next : Position) (ply : Ply) :
    play? position ply = some next ↔
      IsLegalPly (decode position) ply ∧ applyPly position ply = next := by
  simp [play?]

end Chess.Exec
