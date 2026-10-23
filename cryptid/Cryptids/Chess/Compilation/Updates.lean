/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Compilation.Geometry
public import Cryptids.Chess.Compilation.Rules

/-! # Compiled unchecked position updates

The environment is a fixed position followed by three move words. Formulas preserve the
frozen update order even for illegal requests, including destination/source overlap.
-/

@[expose] public section
namespace Chess.Compilation.Updates

open ConjectureMachines.Compilation
open Scalar Geometry
open Turing.ToPartrec

set_option backward.isDefEq.respectTransparency false

/-- All seven raw promotion requests remain expressible. -/
def encodePromotion : Option PieceKind → Nat
  | none => 0
  | some kind => 1 + Data.encodeKind kind

/-- Source, destination, then the unchecked promotion request. -/
def encodePly (ply : Ply) : List Nat :=
  [index ply.src, index ply.dst, encodePromotion ply.promotion]

/-- Position words occupy indices 0–70; move words occupy indices 71–73. -/
def context (position : Exec.Position) (ply : Ply) : List Nat :=
  Data.encodePosition position ++ encodePly ply

@[simp] theorem context_length (position : Exec.Position) (ply : Ply) :
    (context position ply).length = 74 := by simp [context, encodePly]

theorem context_position_read (position : Exec.Position) (ply : Ply) (i : Nat) (hi : i < 71) :
    (context position ply)[i]?.getD 0 = (Data.encodePosition position)[i]?.getD 0 := by
  unfold context
  rw [List.getElem?_append_left (by simpa using hi)]

theorem context_ply_read (position : Exec.Position) (ply : Ply) (i : Nat) :
    (context position ply)[71 + i]?.getD 0 = (encodePly ply)[i]?.getD 0 := by
  unfold context
  rw [List.getElem?_append_right (by simp)]
  simp only [Data.encodePosition_length, Nat.add_sub_cancel_left]

/-- The position board begins at word seven. -/
def boardBase : Expr := .literal 7
def src : Expr := .input 71
def dst : Expr := .input 72
def promotion : Expr := .input 73

theorem context_board_view (position : Exec.Position) (ply : Ply) :
    BoardView boardBase (context position ply) (Exec.decode position).board := by
  intro square
  simp only [boardBase, eval]
  rw [context_position_read _ _ _ (by have := index_lt square; omega)]
  simpa only [Rules.squareIndex, index, Nat.add_comm, Exec.decode] using
    Rules.position_board_lookup position square

@[simp] theorem eval_src (position : Exec.Position) (ply : Ply) :
    eval src (context position ply) = index ply.src := by
  exact context_ply_read position ply 0

@[simp] theorem eval_dst (position : Exec.Position) (ply : Ply) :
    eval dst (context position ply) = index ply.dst := by
  exact context_ply_read position ply 1

@[simp] theorem eval_promotion (position : Exec.Position) (ply : Ply) :
    eval promotion (context position ply) = encodePromotion ply.promotion := by
  exact context_ply_read position ply 2

@[simp] theorem eval_turn_input (position : Exec.Position) (ply : Ply) :
    eval (.input 0) (context position ply) = Data.encodeColor position.turn := by
  exact context_position_read position ply 0 (by decide)

@[simp] theorem eval_clock_input (position : Exec.Position) (ply : Ply) :
    eval (.input 6) (context position ply) = position.halfmoveClock := by
  exact context_position_read position ply 6 (by decide)

@[simp] theorem eval_target_input (position : Exec.Position) (ply : Ply) :
    eval (.input 5) (context position ply) = Data.encodeTarget position.enPassantTarget := by
  exact context_position_read position ply 5 (by decide)

/-- Piece-color and kind formulas are used only after the relevant nonempty test. -/
def pieceColor (cell : Expr) : Expr := .div (.sub cell (.literal 1)) (.literal 6)
def pieceKind (cell : Expr) : Expr := .mod (.sub cell (.literal 1)) (.literal 6)
def sourceCell : Expr := boardAt boardBase src
def destinationCell : Expr := boardAt boardBase dst

theorem eval_sourceCell (position : Exec.Position) (ply : Ply) :
    eval sourceCell (context position ply) =
      Data.encodeCell ((Exec.decode position).board ply.src) :=
  eval_boardAt _ _ _ _ (context_board_view position ply) ply.src (eval_src position ply)

theorem eval_destinationCell (position : Exec.Position) (ply : Ply) :
    eval destinationCell (context position ply) =
      Data.encodeCell ((Exec.decode position).board ply.dst) :=
  eval_boardAt _ _ _ _ (context_board_view position ply) ply.dst (eval_dst position ply)

/-- Decode color from any nonempty raw cell. -/
theorem eval_pieceColor (cell : Expr) (v : List Nat) (piece : Piece)
    (h : eval cell v = Data.encodeCell (some piece)) :
    eval (pieceColor cell) v = Data.encodeColor piece.color := by
  rcases piece with ⟨color, kind⟩
  cases color <;> cases kind <;> simp [pieceColor, eval, h, Data.encodeCell,
    Data.encodeColor, Data.encodeKind]

/-- Decode kind from any nonempty raw cell. -/
theorem eval_pieceKind (cell : Expr) (v : List Nat) (piece : Piece)
    (h : eval cell v = Data.encodeCell (some piece)) :
    eval (pieceKind cell) v = Data.encodeKind piece.kind := by
  rcases piece with ⟨color, kind⟩
  cases color <;> cases kind <;> simp [pieceKind, eval, h, Data.encodeCell,
    Data.encodeColor, Data.encodeKind]

/-- The color-dependent home-rank offset is zero or 56. -/
def homeBase : Expr := .mul (.literal 56) (pieceColor sourceCell)

/-- One means kingside, two means queenside, zero means no castling shape. -/
def castleShape : Expr :=
  .ifZero (.eq (pieceKind sourceCell) (.literal 0)) (.literal 0)
    (.ifZero (and (.eq src (.add homeBase (.literal 4)))
        (.eq dst (.add homeBase (.literal 6))))
      (.ifZero (and (.eq src (.add homeBase (.literal 4)))
          (.eq dst (.add homeBase (.literal 2)))) (.literal 0) (.literal 2))
      (.literal 1))

def rookDestination : Expr :=
  .add homeBase (.ifZero (.eq castleShape (.literal 1)) (.literal 3) (.literal 5))

def rookSource : Expr :=
  .add homeBase (.ifZero (.eq castleShape (.literal 1)) (.literal 0) (.literal 7))

/-- Every requested promotion, including king and pawn, changes the moving piece. -/
def movedCell : Expr :=
  .ifZero promotion sourceCell
    (.add (.mul (.literal 6) (pieceColor sourceCell)) promotion)

def capturedSquare : Expr := .add (file dst) (.mul (.literal 8) (rank src))

/-- The frozen en-passant predicate, without a legality premise. -/
def enPassant : Expr :=
  and (.eq (pieceKind sourceCell) (.literal 5))
    (and (pawnAttacks (pieceColor sourceCell) src dst)
      (and (.eq (.input 5) (.add (.literal 1) dst))
        (and (.eq destinationCell (.literal 0))
          (.eq (boardAt boardBase capturedSquare)
            (.ifZero (pieceColor sourceCell) (.literal 12) (.literal 6))))))

/-- Exact raw double advance; path clearance is a bounded 64-cell expression. -/
def doubleAdvance : Expr :=
  and (.eq (file src) (file dst))
    (and (.eq destinationCell (.literal 0))
      (and (pathClear boardBase src dst)
        (.ifZero (pieceColor sourceCell)
          (and (.eq (rank src) (.literal 1)) (.eq (rank dst) (.literal 3)))
          (and (.eq (rank src) (.literal 6)) (.eq (rank dst) (.literal 4))))))

/-- Double pawn moves create the target; every other request clears it. -/
def target : Expr :=
  .ifZero sourceCell (.literal 0)
    (.ifZero (and (.eq (pieceKind sourceCell) (.literal 5)) doubleAdvance) (.literal 0)
      (.add (.literal 1) (.add (file src)
        (.ifZero (pieceColor sourceCell) (.literal 16) (.literal 40)))))

/-- Metadata slot for one castling right. -/
def rightSlot : Color → CastleSide → Nat
  | .white, .kingside => 1
  | .white, .queenside => 2
  | .black, .kingside => 3
  | .black, .queenside => 4

/-- King, home-rook, and captured home-rook removal conditions. -/
def rightRemoval (color : Color) (side : CastleSide) : Expr :=
  let c := Expr.literal (Data.encodeColor color)
  let home := Expr.literal (index (rookHome color side))
  or
    (and (.eq (pieceColor sourceCell) c)
      (or (.eq (pieceKind sourceCell) (.literal 0))
        (and (.eq (pieceKind sourceCell) (.literal 2)) (.eq src home))))
    (and (not (.eq destinationCell (.literal 0)))
      (and (.eq (pieceColor destinationCell) c)
        (and (.eq (pieceKind destinationCell) (.literal 2)) (.eq dst home))))

/-- Empty-source requests preserve every right, including when a rook occupies the destination. -/
def right (color : Color) (side : CastleSide) : Expr :=
  .ifZero sourceCell (.input (rightSlot color side))
    (.ifZero (rightRemoval color side) (.input (rightSlot color side)) (.literal 0))

/-- The old source and destination determine whether the halfmove clock resets. -/
def resetClock : Expr :=
  or (and (not (.eq sourceCell (.literal 0)))
      (.eq (pieceKind sourceCell) (.literal 5)))
    (or (not (.eq destinationCell (.literal 0)))
      (and (not (.eq sourceCell (.literal 0))) enPassant))

/-- Even an empty-source request resets the clock if its destination is occupied. -/
def clock : Expr := .ifZero resetClock (.add (.input 6) (.literal 1)) (.literal 0)

/-- The destination test precedes the source test, as in the unchecked frozen board update. -/
def cell (square : Expr) : Expr :=
  let old := boardAt boardBase square
  .ifZero sourceCell old
    (.ifZero (.eq square dst)
      (.ifZero (.eq square src)
        (.ifZero castleShape
          (.ifZero (and enPassant (.eq square capturedSquare)) old (.literal 0))
          (.ifZero (.eq square rookDestination)
            (.ifZero (.eq square rookSource) old (.literal 0))
            (.add (.literal 3) (.mul (.literal 6) (pieceColor sourceCell)))))
        (.literal 0))
      movedCell)

/-- Exactly seven metadata formulas followed by 64 literal-indexed cell formulas. -/
def expressions : List Expr :=
  [.sub (.literal 1) (.input 0), right .white .kingside, right .white .queenside,
    right .black .kingside, right .black .queenside, target, clock] ++
    (List.finRange 64).map (fun i ↦ cell (.literal i.val))

/-- Concrete ToPartrec syntax for the complete unchecked position update. -/
def code : Code := NatCode.tuple (expressions.map Scalar.compile)


theorem removeKingside_has (rights : CastlingRights) (color query : Color) (side : CastleSide) :
    (rights.removeKingside color).has query side =
      if color = query ∧ side = .kingside then false else rights.has query side := by
  cases color <;> cases query <;> cases side <;> rfl

theorem removeQueenside_has (rights : CastlingRights) (color query : Color) (side : CastleSide) :
    (rights.removeQueenside color).has query side =
      if color = query ∧ side = .queenside then false else rights.has query side := by
  cases color <;> cases query <;> cases side <;> rfl

theorem removeBoth_has (rights : CastlingRights) (color query : Color) (side : CastleSide) :
    (rights.removeBoth color).has query side =
      if color = query then false else rights.has query side := by
  cases color <;> cases query <;> cases side <;> rfl

theorem removeRookRightAt_has (rights : CastlingRights) (color query : Color)
    (square : Square) (side : CastleSide) :
    (removeRookRightAt rights color square).has query side =
      if color = query ∧ square = rookHome query side then false else rights.has query side := by
  unfold removeRookRightAt
  split
  · subst square
    cases color <;> cases query <;> cases side <;> rfl
  · split
    · subst square
      cases color <;> cases query <;> cases side <;> rfl
    · cases color <;> cases query <;> cases side <;> simp_all [rookHome]

/-- The source-piece contribution to each castling right. -/
theorem afterMove_has (rights : CastlingRights) (piece : Piece) (src : Square)
    (color : Color) (side : CastleSide) :
    (if piece.kind = .king then rights.removeBoth piece.color
      else if piece.kind = .rook then removeRookRightAt rights piece.color src
      else rights).has color side =
      if piece.color = color ∧ (piece.kind = .king ∨
          piece.kind = .rook ∧ src = rookHome color side) then false
      else rights.has color side := by
  cases piece.kind <;> simp [removeBoth_has, removeRookRightAt_has]

/-- Source and captured home-rook effects are combined, except for an empty source. -/
def rightRemoved (position : Chess.Position) (ply : Ply)
    (color : Color) (side : CastleSide) : Prop :=
  match position.board ply.src with
  | none => False
  | some piece =>
    (piece.color = color ∧ (piece.kind = .king ∨
      piece.kind = .rook ∧ ply.src = rookHome color side)) ∨
    ∃ captured, position.board ply.dst = some captured ∧ captured.color = color ∧
      captured.kind = .rook ∧ ply.dst = rookHome color side

instance (position : Chess.Position) (ply : Ply) (color : Color) (side : CastleSide) :
    Decidable (rightRemoved position ply color side) := by
  unfold rightRemoved
  cases position.board ply.src <;> infer_instance

theorem nextCastlingRights_has (position : Chess.Position) (ply : Ply)
    (color : Color) (side : CastleSide) :
    (nextCastlingRights position ply).has color side =
      if rightRemoved position ply color side then false
      else position.castlingRights.has color side := by
  cases hs : position.board ply.src with
  | none => simp [nextCastlingRights, rightRemoved, hs]
  | some piece =>
    cases hd : position.board ply.dst with
    | none => simp [nextCastlingRights, rightRemoved, hs, hd, afterMove_has]
    | some captured =>
      by_cases hk : captured.kind = .rook
      · simp [nextCastlingRights, rightRemoved, hs, hd, hk, removeRookRightAt_has,
          afterMove_has, Bool.and_left_comm, Bool.and_assoc]
      · simp [nextCastlingRights, rightRemoved, hs, hd, hk, afterMove_has]


/-- Nonempty piece codes cannot be confused with the empty-cell sentinel. -/
theorem encodeCell_some_ne_zero (piece : Piece) : Data.encodeCell (some piece) ≠ 0 := by
  simp only [Data.encodeCell]
  omega

/-- Natural promotion arithmetic retains every unchecked requested kind. -/
theorem encode_movedPiece (piece : Piece) (ply : Ply) :
    Data.encodeCell (some (movedPiece piece ply)) =
      if encodePromotion ply.promotion = 0 then Data.encodeCell (some piece)
      else 6 * Data.encodeColor piece.color + encodePromotion ply.promotion := by
  cases hp : ply.promotion with
  | none => simp [movedPiece, hp, encodePromotion]
  | some kind =>
    simp [movedPiece, hp, encodePromotion, Data.encodeCell, Nat.add_assoc, Nat.add_left_comm]

/-- Compiling and collecting scalar expressions returns their complete ordered value list. -/
theorem compile_tuple_eval (es : List Expr) (v : List Nat) :
    (NatCode.tuple (es.map Scalar.compile)).eval v = pure (es.map (fun e ↦ eval e v)) := by
  induction es with
  | nil => simp [NatCode.tuple]
  | cons e es ih =>
    simp [NatCode.tuple, Scalar.compile_eval, ih, Bind.bind, Part.bind_some]

theorem encodeKind_injective : Function.Injective Data.encodeKind := by
  intro a b h
  cases a <;> cases b <;> simp_all [Data.encodeKind]

theorem encodeColor_injective : Function.Injective Data.encodeColor := by
  intro a b h
  cases a <;> cases b <;> simp_all [Data.encodeColor]

theorem encodeCell_injective : Function.Injective Data.encodeCell := by
  intro a b h
  have decoded := congrArg Data.cellOfNat h
  simpa only [Data.cellOfNat_encodeCell] using decoded

theorem source_kind {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) :
    eval (pieceKind sourceCell) (context position ply) = Data.encodeKind piece.kind := by
  apply eval_pieceKind
  rw [eval_sourceCell, h]

theorem source_color {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) :
    eval (pieceColor sourceCell) (context position ply) = Data.encodeColor piece.color := by
  apply eval_pieceColor
  rw [eval_sourceCell, h]

theorem source_kind_eq {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) (kind : PieceKind) :
    eval (.eq (pieceKind sourceCell) (.literal (Data.encodeKind kind))) (context position ply) =
      truth (piece.kind = kind) := by
  simp only [source_kind h, eval]
  exact truth_congr encodeKind_injective.eq_iff

theorem source_color_eq {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) (color : Color) :
    eval (.eq (pieceColor sourceCell) (.literal (Data.encodeColor color)))
        (context position ply) = truth (piece.color = color) := by
  simp only [source_color h, eval]
  exact truth_congr encodeColor_injective.eq_iff

theorem encodeTarget_eq (target : Option Square) (square : Square) :
    Data.encodeTarget target = 1 + index square ↔ target = some square := by
  cases target with
  | none => simp [Data.encodeTarget, show (0 : Nat) ≠ 1 + index square by omega]
  | some s =>
    simp only [Data.encodeTarget, index, Nat.add_assoc, Nat.add_left_cancel_iff,
      Option.some.injEq]
    exact index_injective.eq_iff

theorem eval_capturedSquare (position : Exec.Position) (ply : Ply) :
    eval capturedSquare (context position ply) = index (enPassantCapturedSquare ply) := by
  simp only [capturedSquare, eval, eval_file _ _ _ (eval_dst position ply),
    eval_rank _ _ _ (eval_src position ply), index, enPassantCapturedSquare]

theorem eval_other_pawn {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) :
    eval (.ifZero (pieceColor sourceCell) (.literal 12) (.literal 6)) (context position ply) =
      Data.encodeCell (some ⟨piece.color.other, .pawn⟩) := by
  simp only [eval, source_color h]
  cases piece.color <;> rfl

/-- En-passant source semantics agree for every raw source piece. -/
theorem eval_enPassant {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) :
    eval enPassant (context position ply) =
      truth (IsEnPassant (Exec.decode position) piece ply) := by
  unfold enPassant IsEnPassant
  apply eval_and
  · exact source_kind_eq h .pawn
  · apply eval_and
    · exact eval_pawnAttacks _ _ _ _ _ _ _ (source_color h)
        (eval_src position ply) (eval_dst position ply)
    · apply eval_and
      · simp only [eval, eval_dst]
        exact truth_congr (encodeTarget_eq _ _)
      · apply eval_and
        · simp only [eval, eval_destinationCell, encodeCell_eq_zero, truth]
        · rw [eval_eq, eval_other_pawn h,
            eval_boardAt _ _ _ _ (context_board_view position ply) _
              (eval_capturedSquare position ply)]
          exact truth_congr encodeCell_injective.eq_iff

/-- A truth-valued guard chooses the corresponding branch of a scalar expression. -/
theorem eval_choose (condition zero nonzero : Expr) (v : List Nat) (P : Prop) [Decidable P]
    (h : eval condition v = truth P) :
    eval (.ifZero condition zero nonzero) v = if P then eval nonzero v else eval zero v := by
  by_cases hp : P <;> simp [eval, h, truth, hp]

/-- Exact double-advance semantics use the shared bounded path-clearance procedure. -/
theorem eval_doubleAdvance {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) :
    eval doubleAdvance (context position ply) =
      truth (IsPawnDoubleAdvance (Exec.decode position).board piece.color ply.src ply.dst) := by
  suffices hh : eval doubleAdvance (context position ply) =
      truth (ply.src.file = ply.dst.file ∧ (Exec.decode position).board ply.dst = none ∧
        PathClear (Exec.decode position).board ply.src ply.dst ∧
        ((piece.color = .white ∧ ply.src.rank = 1 ∧ ply.dst.rank = 3) ∨
          (piece.color = .black ∧ ply.src.rank = 6 ∧ ply.dst.rank = 4))) by
    apply hh.trans
    apply truth_congr
    cases piece.color <;> simp [IsPawnDoubleAdvance]
  unfold doubleAdvance
  apply eval_and
  · simp only [eval_eq, eval_file _ _ _ (eval_src position ply),
      eval_file _ _ _ (eval_dst position ply), Fin.val_inj]
  · apply eval_and
    · simp only [eval, eval_destinationCell, encodeCell_eq_zero, truth]
    · apply eval_and
      · exact eval_pathClear _ _ _ _ _ _ _ (context_board_view position ply)
          (eval_src position ply) (eval_dst position ply)
      · cases hc : piece.color <;>
          simp [eval, source_color h, hc, Data.encodeColor, Geometry.and, rank,
            eval_src, eval_dst, truth, Fin.ext_iff, ite_and]

/-- Raw en-passant metadata is exactly the frozen post-move target. -/
theorem eval_target (position : Exec.Position) (ply : Ply) :
    eval target (context position ply) =
      Data.encodeTarget (Exec.enPassantAfter (Exec.decode position) ply) := by
  cases hs : (Exec.decode position).board ply.src with
  | none => simp [target, eval, eval_sourceCell, hs, Exec.enPassantAfter, Data.encodeTarget]
  | some piece =>
    have hcond := eval_and _ _ _ _ _ (source_kind_eq hs .pawn) (eval_doubleAdvance hs)
    simp only [Data.encodeKind] at hcond
    rw [show target = .ifZero sourceCell (.literal 0)
      (.ifZero (and (.eq (pieceKind sourceCell) (.literal 5)) doubleAdvance) (.literal 0)
        (.add (.literal 1) (.add (file src)
          (.ifZero (pieceColor sourceCell) (.literal 16) (.literal 40))))) from rfl]
    simp only [eval, eval_sourceCell, hs, encodeCell_some_ne_zero, ↓reduceIte]
    rw [hcond, source_color hs, eval_file _ _ _ (eval_src position ply)]
    by_cases hp : piece.kind = .pawn ∧
        IsPawnDoubleAdvance (Exec.decode position).board piece.color ply.src ply.dst <;>
      cases hc : piece.color
    all_goals simp only [hc] at hp
    all_goals simp [Exec.enPassantAfter, hs, truth, hc, Data.encodeColor,
      Data.encodeTarget, Nat.add_assoc, hp]

def encodeCastleSide : Option CastleSide → Nat
  | none => 0
  | some .kingside => 1
  | some .queenside => 2

/-- Castling shape detection follows piece color, independently of turn or legality. -/
theorem eval_castleShape {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) :
    eval castleShape (context position ply) = encodeCastleSide (castleSide? piece ply) := by
  have square_eq : ∀ a b : Square, a = b ↔ index a = index b :=
    fun _ _ ↦ index_injective.eq_iff.symm
  by_cases hks : ply.src = kingHome piece.color ∧
      ply.dst = castleKingDestination piece.color .kingside <;>
    by_cases hqs : ply.src = kingHome piece.color ∧
      ply.dst = castleKingDestination piece.color .queenside <;>
    cases hk : piece.kind <;> cases hc : piece.color <;>
    simp_all [castleShape, homeBase, eval, source_kind h, source_color h,
      Data.encodeKind, Data.encodeColor, eval_src, eval_dst, castleSide?,
      encodeCastleSide, kingHome, castleKingDestination, Geometry.and, index, ite_and]

theorem eval_movedCell {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) :
    eval movedCell (context position ply) = Data.encodeCell (some (movedPiece piece ply)) := by
  rw [encode_movedPiece]
  simp only [movedCell, eval, eval_promotion, eval_sourceCell, h, source_color h]

theorem eval_rookDestination {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) (side : CastleSide)
    (castle : castleSide? piece ply = some side) :
    eval rookDestination (context position ply) =
      index (castleRookDestination piece.color side) := by
  simp only [rookDestination, homeBase, eval, source_color h, eval_castleShape h, castle]
  cases piece.color <;> cases side <;> rfl

theorem eval_rookSource {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) (side : CastleSide)
    (castle : castleSide? piece ply = some side) :
    eval rookSource (context position ply) = index (rookHome piece.color side) := by
  simp only [rookSource, homeBase, eval, source_color h, eval_castleShape h, castle]
  cases piece.color <;> cases side <;> rfl

/-- Every output cell agrees with the frozen unchecked board effect. -/
theorem eval_cell (position : Exec.Position) (ply : Ply) (squareExpr : Expr) (square : Square)
    (hsquare : eval squareExpr (context position ply) = index square) :
    eval (cell squareExpr) (context position ply) =
      Data.encodeCell (Exec.boardAfter (Exec.decode position) ply square) := by
  have hold := eval_boardAt boardBase squareExpr _ _
    (context_board_view position ply) square hsquare
  cases hsrc : (Exec.decode position).board ply.src with
  | none => simp [cell, eval, eval_sourceCell, hsrc, hold, Exec.boardAfter, Data.encodeCell]
  | some piece =>
    by_cases hdst : square = ply.dst
    · simp [cell, eval, eval_sourceCell, hsrc, hsquare, eval_dst,
        hdst, eval_movedCell hsrc, Exec.boardAfter]
    · by_cases hsource : square = ply.src
      · subst square
        simp [cell, eval, eval_sourceCell, hsrc, hsquare, eval_dst, eval_src,
          index_injective.eq_iff, hdst, Exec.boardAfter, Data.encodeCell]
      · cases castle : castleSide? piece ply with
        | none =>
          by_cases hep : IsEnPassant (Exec.decode position) piece ply <;>
            by_cases hcap : square = enPassantCapturedSquare ply <;>
            simp_all [cell, eval, eval_sourceCell, eval_dst, eval_src,
              index_injective.eq_iff, Exec.boardAfter, eval_castleShape hsrc,
              encodeCastleSide, eval_enPassant hsrc, eval_capturedSquare,
              Geometry.and, truth, Data.encodeCell]
        | some side =>
          by_cases hrookdst : square = castleRookDestination piece.color side <;>
            by_cases hrooksrc : square = rookHome piece.color side <;>
            cases side <;>
            simp_all [cell, eval, eval_sourceCell, eval_dst, eval_src,
              index_injective.eq_iff, Exec.boardAfter, eval_castleShape hsrc,
              eval_rookDestination hsrc _ castle, eval_rookSource hsrc _ castle,
              source_color hsrc, Data.encodeCell, Data.encodeKind, encodeCastleSide,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

theorem eval_rightSlot (position : Exec.Position) (ply : Ply) (color : Color) (side : CastleSide) :
    eval (.input (rightSlot color side)) (context position ply) =
      Data.encodeBool (position.castlingRights.has color side) := by
  cases color <;> cases side <;> exact context_position_read position ply _ (by decide)

theorem context_right_read (position : Exec.Position) (ply : Ply) (color : Color)
    (side : CastleSide) :
    (context position ply)[rightSlot color side]?.getD 0 =
      Data.encodeBool (position.castlingRights.has color side) :=
  eval_rightSlot position ply color side

theorem eval_index_eq (a b : Expr) (v : List Nat) (s d : Square)
    (ha : eval a v = index s) (hb : eval b v = index d) :
    eval (.eq a b) v = truth (s = d) := by
  rw [eval_eq, ha, hb]
  exact truth_congr index_injective.eq_iff

theorem eval_kind_eq (cell : Expr) (v : List Nat) (piece : Piece)
    (h : eval cell v = Data.encodeCell (some piece)) (kind : PieceKind) :
    eval (.eq (pieceKind cell) (.literal (Data.encodeKind kind))) v =
      truth (piece.kind = kind) := by
  simp only [eval, eval_pieceKind cell v piece h]
  exact truth_congr encodeKind_injective.eq_iff

theorem eval_color_eq (cell : Expr) (v : List Nat) (piece : Piece)
    (h : eval cell v = Data.encodeCell (some piece)) (color : Color) :
    eval (.eq (pieceColor cell) (.literal (Data.encodeColor color))) v =
      truth (piece.color = color) := by
  simp only [eval, eval_pieceColor cell v piece h]
  exact truth_congr encodeColor_injective.eq_iff

/-- The complete right-removal predicate is computed from the old board. -/
theorem eval_rightRemoval {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) (color : Color) (side : CastleSide) :
    eval (rightRemoval color side) (context position ply) = truth
      ((piece.color = color ∧ (piece.kind = .king ∨
        piece.kind = .rook ∧ ply.src = rookHome color side)) ∨
        ∃ captured, (Exec.decode position).board ply.dst = some captured ∧
          captured.color = color ∧ captured.kind = .rook ∧ ply.dst = rookHome color side) := by
  unfold rightRemoval
  apply eval_or
  · apply eval_and
    · exact source_color_eq h color
    · apply eval_or
      · exact source_kind_eq h .king
      · apply eval_and
        · exact source_kind_eq h .rook
        · exact eval_index_eq _ _ _ _ _ (eval_src position ply) rfl
  · cases hd : (Exec.decode position).board ply.dst with
    | none =>
      simp [eval, Geometry.and, Geometry.not, eval_destinationCell, hd, Data.encodeCell, truth]
    | some captured =>
      have hcell : eval destinationCell (context position ply) =
          Data.encodeCell (some captured) := by
        rw [eval_destinationCell, hd]
      have hi := eval_and _ _ _ _ _ (eval_color_eq _ _ _ hcell color)
        (eval_and _ _ _ _ _ (eval_kind_eq _ _ _ hcell .rook)
          (eval_index_eq dst (.literal (index (rookHome color side))) (context position ply)
            ply.dst (rookHome color side) (eval_dst position ply) rfl))
      have hguard : eval (not (.eq destinationCell (.literal 0))) (context position ply) =
          truth True := by
        simp [Geometry.not, eval, hcell, truth]
      have ho := eval_and _ _ _ _ _ hguard hi
      simpa only [true_and, hd, Option.some.injEq, exists_eq_left', Data.encodeKind] using ho

/-- Every castling-right output agrees with the complete unchecked reference update. -/
theorem eval_right (position : Exec.Position) (ply : Ply) (color : Color) (side : CastleSide) :
    eval (right color side) (context position ply) =
      Data.encodeBool ((nextCastlingRights (Exec.decode position) ply).has color side) := by
  rw [nextCastlingRights_has]
  change eval (right color side) (context position ply) =
    Data.encodeBool (if rightRemoved (Exec.decode position) ply color side then false
      else position.castlingRights.has color side)
  cases hsrc : (Exec.decode position).board ply.src with
  | none =>
    simp only [right, eval, eval_sourceCell, hsrc, Data.encodeCell, ↓reduceIte,
      context_right_read, rightRemoved]
  | some piece =>
    have hr := (eval_rightRemoval hsrc color side).trans
      (truth_congr (show _ ↔ rightRemoved (Exec.decode position) ply color side by
        simp only [rightRemoved, hsrc]))
    simp only [right, eval, eval_sourceCell, hsrc, encodeCell_some_ne_zero, ↓reduceIte,
      hr, context_right_read]
    by_cases removed : rightRemoved (Exec.decode position) ply color side <;>
      simp [removed, truth, Data.encodeBool]

theorem eval_nonempty (cell : Expr) (v : List Nat) (value : Option Piece)
    (h : eval cell v = Data.encodeCell value) :
    eval (not (.eq cell (.literal 0))) v = truth (value ≠ none) := by
  apply eval_not
  simp only [eval, h, truth, encodeCell_eq_zero]

/-- The pawn test includes the necessary nonempty-source guard. -/
theorem eval_sourcePawn (position : Exec.Position) (ply : Ply) :
    eval (and (not (.eq sourceCell (.literal 0)))
        (.eq (pieceKind sourceCell) (.literal 5))) (context position ply) =
      truth (∃ piece, (Exec.decode position).board ply.src = some piece ∧
        piece.kind = .pawn) := by
  cases hs : (Exec.decode position).board ply.src with
  | none => simp [Geometry.and, Geometry.not, eval, eval_sourceCell, hs, Data.encodeCell, truth]
  | some piece =>
    have hnonempty := eval_nonempty sourceCell _ _ (eval_sourceCell position ply)
    have hk := source_kind_eq hs .pawn
    have hi := eval_and _ _ _ _ _ hnonempty hk
    apply hi.trans
    apply truth_congr
    simp [hs]

/-- The existential en-passant capture test also includes the nonempty-source guard. -/
theorem eval_enPassantCapture (position : Exec.Position) (ply : Ply) :
    eval (and (not (.eq sourceCell (.literal 0))) enPassant) (context position ply) =
      truth (∃ piece, (Exec.decode position).board ply.src = some piece ∧
        IsEnPassant (Exec.decode position) piece ply) := by
  cases hs : (Exec.decode position).board ply.src with
  | none => simp [Geometry.and, Geometry.not, eval, eval_sourceCell, hs, Data.encodeCell, truth]
  | some piece =>
    have hnonempty := eval_nonempty sourceCell _ _ (eval_sourceCell position ply)
    have hi := eval_and _ _ _ _ _ hnonempty (eval_enPassant hs)
    apply hi.trans
    apply truth_congr
    simp [hs]

/-- The reset test has exact frozen capture semantics, including occupied empty-source requests. -/
theorem eval_resetClock (position : Exec.Position) (ply : Ply) :
    eval resetClock (context position ply) = truth
      ((∃ piece, (Exec.decode position).board ply.src = some piece ∧ piece.kind = .pawn) ∨
        IsCapture (Exec.decode position) ply) := by
  have hi := eval_or _ _ _ _ _ (eval_sourcePawn position ply)
    (eval_or _ _ _ _ _
      (eval_nonempty destinationCell _ _ (eval_destinationCell position ply))
      (eval_enPassantCapture position ply))
  exact hi.trans (truth_congr Iff.rfl)

/-- The natural halfmove clock is updated without truncation or reachability assumptions. -/
theorem eval_clock (position : Exec.Position) (ply : Ply) :
    eval clock (context position ply) =
      (Exec.positionAfter (Exec.decode position) ply).halfmoveClock := by
  rw [clock, eval_choose _ _ _ _ _ (eval_resetClock position ply)]
  rfl

/-- The side-to-move field flips independently of the moving piece color. -/
theorem eval_turn (position : Exec.Position) (ply : Ply) :
    eval (.sub (.literal 1) (.input 0)) (context position ply) =
      Data.encodeColor position.turn.other := by
  change 1 - eval (.input 0) (context position ply) = _
  rw [eval_turn_input]
  cases position.turn <;> rfl

/-- All 64 output formulas reproduce the updated concrete board in rank-major order. -/
theorem eval_board_cells (position : Exec.Position) (ply : Ply) :
    (List.finRange 64).map (fun i ↦ eval (cell (.literal i.val)) (context position ply)) =
      Data.encodeBoard (Exec.applyPly position ply).board := by
  rw [Data.encodeBoard, List.ofFn_eq_map]
  apply List.map_congr_left
  intro i _
  rw [eval_cell position ply (.literal i.val) (squareAt i.val)
    (index_squareAt i.val i.isLt).symm]
  simp [Exec.applyPly, Exec.encode, Exec.positionAfter, Exec.encodeBoard, squareAt,
    Nat.mod_eq_of_lt (show i.val / 8 < 8 by omega)]

/-- The complete scalar source returns the exact frozen five-field raw update. -/
theorem expressions_refine (position : Exec.Position) (ply : Ply) :
    expressions.map (fun e ↦ eval e (context position ply)) =
      Data.encodePosition (Exec.applyPly position ply) := by
  simp only [expressions, List.map_append, List.map_cons, List.map_nil, List.map_map,
    Function.comp_def, eval_turn, eval_right, eval_target, eval_clock]
  rw [eval_board_cells]
  rfl

@[simp] theorem expressions_length : expressions.length = 71 := by simp [expressions]

/-- Actual ToPartrec evaluation refines the frozen unchecked update for every raw input. -/
theorem code_refines (position : Exec.Position) (ply : Ply) :
    code.eval (context position ply) = pure (Data.encodePosition (Exec.applyPly position ply)) := by
  rw [code, compile_tuple_eval, expressions_refine]

end Chess.Compilation.Updates
