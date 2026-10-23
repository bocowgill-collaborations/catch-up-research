/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Compilation.Updates

/-! # Scalar procedures for full ply validation

Inputs use `Updates.context`: 71 position words followed by source, destination, promotion.
The formulas retain the frozen separation of pseudo-legality and final king safety.
-/

@[expose] public section

namespace Chess.Compilation.Legality

open Turing.ToPartrec ConjectureMachines.Compilation Scalar Geometry Updates

set_option backward.isDefEq.respectTransparency false

attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some

/-- The encoded side to move, read independently of the source piece. -/
def turn : Expr := .input 0

def otherTurn : Expr := .sub (.literal 1) turn

def lastRank : Expr := .ifZero (pieceColor sourceCell) (.literal 7) (.literal 0)

def validPromotion : Expr :=
  .ifZero (and (.eq (pieceKind sourceCell) (.literal 5)) (.eq (rank dst) lastRank))
    (.eq promotion (.literal 0))
    (and (.le (.literal 2) promotion) (.le promotion (.literal 5)))

def destinationAllowed : Expr :=
  .ifZero destinationCell (.literal 1)
    (and (.eq (pieceColor destinationCell) otherTurn)
      (not (.eq (pieceKind destinationCell) (.literal 0))))

def pawnAdvance : Expr :=
  and (.eq (file src) (file dst))
    (and (.eq destinationCell (.literal 0))
      (.ifZero (pieceColor sourceCell)
        (.eq (.add (rank src) (.literal 1)) (rank dst))
        (.eq (.add (rank dst) (.literal 1)) (rank src))))

def pawnCapture : Expr :=
  and (pawnAttacks (pieceColor sourceCell) src dst)
    (and (not (.eq destinationCell (.literal 0)))
      (and (.eq (pieceColor destinationCell)
          (.sub (.literal 1) (pieceColor sourceCell)))
        (not (.eq (pieceKind destinationCell) (.literal 0)))))

def home : Expr := .mul (.literal 56) turn

def castle (side : CastleSide) : Expr :=
  let kingFile := if side = .kingside then 6 else 2
  let rookFile := if side = .kingside then 7 else 0
  let transitFile := if side = .kingside then 5 else 3
  let rightOffset := if side = .kingside then 1 else 2
  let rook := .add home (.literal rookFile)
  and (.eq sourceCell (.add (.literal 1) (.mul (.literal 6) turn)))
    (and (.eq src (.add home (.literal 4)))
      (and (.eq dst (.add home (.literal kingFile)))
        (and (.eq (.lookup (.add (.literal rightOffset) (.mul (.literal 2) turn))) (.literal 1))
          (and (.eq (boardAt boardBase rook) (.add (.literal 3) (.mul (.literal 6) turn)))
            (and (pathClear boardBase src rook)
              (and (not (isAttackedBy boardBase otherTurn src))
                (not (isAttackedBy boardBase otherTurn
                  (.add home (.literal transitFile))))))))))

def castling : Expr := or (castle .kingside) (castle .queenside)

def pieceMovement : Expr :=
  ifEq (pieceKind sourceCell) 0
    (or (and (.le (Geometry.fileDistance src dst) (.literal 1))
      (.le (Geometry.rankDistance src dst) (.literal 1))) castling)
    (ifEq (pieceKind sourceCell) 1
      (and (or (.eq (file src) (file dst))
          (or (.eq (rank src) (rank dst))
            (.eq (Geometry.fileDistance src dst) (Geometry.rankDistance src dst))))
        (pathClear boardBase src dst))
      (ifEq (pieceKind sourceCell) 2
        (and (or (.eq (file src) (file dst)) (.eq (rank src) (rank dst)))
          (pathClear boardBase src dst))
        (ifEq (pieceKind sourceCell) 3
          (and (.eq (Geometry.fileDistance src dst) (Geometry.rankDistance src dst))
            (pathClear boardBase src dst))
          (ifEq (pieceKind sourceCell) 4 (knightAttacks src dst)
            (ifEq (pieceKind sourceCell) 5
              (or pawnAdvance (or doubleAdvance (or pawnCapture enPassant)))
              (.literal 0))))))

def pseudoLegal : Expr :=
  and (not (.eq sourceCell (.literal 0)))
    (and (.eq (pieceColor sourceCell) turn)
      (and (not (.eq src dst))
        (and destinationAllowed (and validPromotion pieceMovement))))

/-- King safety is tested on the updated board, for the player who just moved. -/
def checkedAfter : Code :=
  .comp (Scalar.compile (inCheck (.literal 7) (.sub (.literal 1) (.input 0)))) Updates.code

/-- Complete concrete validation syntax, with a false result for pseudo-illegal requests. -/
def code : Code :=
  NatCode.ifZero (Scalar.compile pseudoLegal) .zero (.comp NatCode.isZero checkedAfter)

@[simp] theorem eval_turn (position : Exec.Position) (ply : Ply) :
    eval turn (context position ply) = Data.encodeColor position.turn :=
  eval_turn_input position ply

theorem eval_otherTurn (position : Exec.Position) (ply : Ply) :
    eval otherTurn (context position ply) = Data.encodeColor position.turn.other := by
  cases hc : position.turn <;> simp [otherTurn, eval, eval_turn, hc, Data.encodeColor, Color.other]

theorem eval_lastRank {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) :
    eval lastRank (context position ply) = if piece.color = .white then 7 else 0 := by
  cases hc : piece.color <;> simp [lastRank, eval, source_color h, hc, Data.encodeColor]

/-- Promotion is mandatory exactly for pawns arriving on their color's last rank. -/
theorem eval_validPromotion {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) :
    eval validPromotion (context position ply) = truth (ValidPromotion piece ply) := by
  have hk := source_kind h
  have hc := source_color h
  cases piece with
  | mk color kind =>
    cases color <;> cases kind <;> cases hp : ply.promotion with
    | none =>
      simp [validPromotion, Geometry.and, lastRank, eval, hk, hc, eval_dst, eval_promotion,
        hp, Data.encodeColor, Data.encodeKind, encodePromotion, ValidPromotion, truth, rank]
      all_goals simp only [Fin.ext_iff]
      all_goals rfl
    | some promoted =>
      cases promoted <;>
        simp [validPromotion, Geometry.and, lastRank, eval, hk, hc, eval_dst, eval_promotion,
          hp, Data.encodeColor, Data.encodeKind, encodePromotion, ValidPromotion, truth, rank]
      all_goals simp only [Fin.ext_iff]
      all_goals rfl

/-- Destination acceptance includes opponent color and the prohibition on king capture. -/
theorem eval_destinationAllowed (position : Exec.Position) (ply : Ply) :
    eval destinationAllowed (context position ply) =
      truth (DestinationAllowed (Exec.decode position) ply) := by
  cases hdst : (Exec.decode position).board ply.dst with
  | none => simp [destinationAllowed, eval, eval_destinationCell, hdst,
      Data.encodeCell, DestinationAllowed, truth]
  | some piece =>
    have hc : eval (pieceColor destinationCell) (context position ply) =
        Data.encodeColor piece.color := eval_pieceColor _ _ _ (by rw [eval_destinationCell, hdst])
    have hk : eval (pieceKind destinationCell) (context position ply) =
        Data.encodeKind piece.kind := eval_pieceKind _ _ _ (by rw [eval_destinationCell, hdst])
    have hnonzero := encodeCell_some_ne_zero piece
    rw [destinationAllowed]
    simp only [eval, eval_destinationCell, hdst, hnonzero, ↓reduceIte]
    have he : eval (and (.eq (pieceColor destinationCell) otherTurn)
        (Geometry.not (.eq (pieceKind destinationCell) (.literal 0)))) (context position ply) =
        truth (piece.color = position.turn.other ∧ piece.kind ≠ .king) := by
      apply eval_and
      · simp only [eval_eq, hc, eval_otherTurn, Updates.encodeColor_injective.eq_iff]
      · exact eval_not _ _ _ (by
        simpa only [Data.encodeKind] using
          eval_kind_eq destinationCell (context position ply) piece
            (by rw [eval_destinationCell, hdst]) .king)
    apply he.trans
    apply truth_congr
    simp only [DestinationAllowed, hdst]
    rfl

theorem eval_pawnAdvance {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) :
    eval pawnAdvance (context position ply) =
      truth (IsPawnAdvance (Exec.decode position).board piece.color ply.src ply.dst) := by
  suffices hh : eval pawnAdvance (context position ply) =
      truth (ply.src.file = ply.dst.file ∧ (Exec.decode position).board ply.dst = none ∧
        ((piece.color = .white ∧ ply.src.rank.val + 1 = ply.dst.rank.val) ∨
          (piece.color = .black ∧ ply.dst.rank.val + 1 = ply.src.rank.val))) by
    apply hh.trans
    apply truth_congr
    cases piece.color <;> simp [IsPawnAdvance]
  unfold pawnAdvance
  apply eval_and
  · simp only [eval_eq, eval_file _ _ _ (eval_src position ply),
      eval_file _ _ _ (eval_dst position ply), Fin.val_inj]
  · apply eval_and
    · simp only [eval, eval_destinationCell, encodeCell_eq_zero, truth]
    · cases hc : piece.color <;>
        simp [eval, source_color h, hc, Data.encodeColor, rank, eval_src, eval_dst, truth]

theorem eval_pawnCapture {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) :
    eval pawnCapture (context position ply) =
      truth (IsPawnCapture (Exec.decode position).board piece ply.src ply.dst) := by
  unfold pawnCapture IsPawnCapture
  apply eval_and
  · exact eval_pawnAttacks _ _ _ _ _ _ _ (source_color h)
      (eval_src position ply) (eval_dst position ply)
  · cases hdst : (Exec.decode position).board ply.dst with
    | none => simp [Geometry.and, Geometry.not, eval, eval_destinationCell, hdst,
        Data.encodeCell, truth]
    | some captured =>
      have hc : eval (pieceColor destinationCell) (context position ply) =
          Data.encodeColor captured.color :=
        eval_pieceColor _ _ _ (by rw [eval_destinationCell, hdst])
      have hother : eval (.sub (.literal 1) (pieceColor sourceCell)) (context position ply) =
          Data.encodeColor piece.color.other := by
        cases color : piece.color <;>
          simp [eval, source_color h, color, Data.encodeColor, Color.other]
      have hcpt : eval (and
          (.eq (pieceColor destinationCell) (.sub (.literal 1) (pieceColor sourceCell)))
          (Geometry.not (.eq (pieceKind destinationCell) (.literal 0)))) (context position ply) =
          truth (captured.color = piece.color.other ∧ captured.kind ≠ .king) := by
        apply eval_and
        · simp only [eval_eq, hc, hother, Updates.encodeColor_injective.eq_iff]
        · exact eval_not _ _ _ (by
          simpa only [Data.encodeKind] using
            eval_kind_eq destinationCell (context position ply) captured
              (by rw [eval_destinationCell, hdst]) .king)
      have hnonempty : eval (Geometry.not (.eq destinationCell (.literal 0)))
          (context position ply) = truth True := by
        simp [Geometry.not, eval, eval_destinationCell, hdst, truth]
      have htotal := eval_and _ _ (context position ply) True _ hnonempty hcpt
      simpa only [true_and, hdst, Option.some.injEq, exists_eq_left'] using htotal

/-- The side-specific conjunction in the frozen castling predicate. -/
def CastleCondition (position : Chess.Position) (piece : Piece) (ply : Ply)
    (side : CastleSide) : Prop :=
  piece = ⟨position.turn, .king⟩ ∧ ply.src = kingHome position.turn ∧
    ply.dst = castleKingDestination position.turn side ∧
    position.castlingRights.has position.turn side = true ∧
    position.board (rookHome position.turn side) = some ⟨position.turn, .rook⟩ ∧
    PathClear position.board ply.src (rookHome position.turn side) ∧
    ¬IsAttackedBy position.board position.turn.other ply.src ∧
    ¬IsAttackedBy position.board position.turn.other (castleKingTransit position.turn side)

instance (position : Chess.Position) (piece : Piece) (ply : Ply) (side : CastleSide) :
    Decidable (CastleCondition position piece ply side) := by
  unfold CastleCondition
  infer_instance

theorem eval_homeKing (position : Exec.Position) (ply : Ply) :
    eval (.add home (.literal 4)) (context position ply) = index (kingHome position.turn) := by
  cases hc : position.turn <;>
    simp [home, eval, eval_turn, hc, Data.encodeColor, kingHome, index]

theorem eval_homeRook (position : Exec.Position) (ply : Ply) (side : CastleSide) :
    eval (.add home (.literal (if side = .kingside then 7 else 0))) (context position ply) =
      index (rookHome position.turn side) := by
  cases hc : position.turn <;> cases side <;>
    simp [home, eval, eval_turn, hc, Data.encodeColor, rookHome, index]

theorem eval_castleDestination (position : Exec.Position) (ply : Ply) (side : CastleSide) :
    eval (.add home (.literal (if side = .kingside then 6 else 2))) (context position ply) =
      index (castleKingDestination position.turn side) := by
  cases hc : position.turn <;> cases side <;>
    simp [home, eval, eval_turn, hc, Data.encodeColor, castleKingDestination, index]

theorem eval_castleTransit (position : Exec.Position) (ply : Ply) (side : CastleSide) :
    eval (.add home (.literal (if side = .kingside then 5 else 3))) (context position ply) =
      index (castleKingTransit position.turn side) := by
  cases hc : position.turn <;> cases side <;>
    simp [home, eval, eval_turn, hc, Data.encodeColor, castleKingTransit, index]

theorem eval_castleRight (position : Exec.Position) (ply : Ply) (side : CastleSide) :
    eval (.lookup (.add (.literal (if side = .kingside then 1 else 2))
      (.mul (.literal 2) turn))) (context position ply) =
      Data.encodeBool (position.castlingRights.has position.turn side) := by
  have hr := context_right_read position ply position.turn side
  cases hc : position.turn <;> cases side <;>
    simpa [eval, eval_turn, hc, rightSlot, Data.encodeColor] using hr

theorem eval_castle {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) (side : CastleSide) :
    eval (castle side) (context position ply) =
      truth (CastleCondition (Exec.decode position) piece ply side) := by
  have hk : eval (.add (.literal 1) (.mul (.literal 6) turn)) (context position ply) =
      Data.encodeCell (some ⟨position.turn, .king⟩) := by
    simp [eval, eval_turn, Data.encodeCell, Data.encodeKind]
  have hr : eval (.add (.literal 3) (.mul (.literal 6) turn)) (context position ply) =
      Data.encodeCell (some ⟨position.turn, .rook⟩) := by
    simp only [eval, eval_turn, Data.encodeCell, Data.encodeKind]
    omega
  unfold castle CastleCondition
  apply eval_and
  · simp only [eval_eq, eval_sourceCell, h, hk, Updates.encodeCell_injective.eq_iff,
      Option.some.injEq]
    rfl
  · apply eval_and
    · exact eval_index_eq _ _ _ _ _ (eval_src position ply) (eval_homeKing position ply)
    · apply eval_and
      · exact eval_index_eq _ _ _ _ _ (eval_dst position ply)
          (eval_castleDestination position ply side)
      · apply eval_and
        · rw [eval_eq, eval_castleRight]
          apply truth_congr
          cases hrgt : position.castlingRights.has position.turn side <;>
            simp [eval, Exec.decode, Data.encodeBool, hrgt]
        · apply eval_and
          · rw [eval_eq, hr, eval_boardAt _ _ _ _ (context_board_view position ply)
              _ (eval_homeRook position ply side)]
            exact truth_congr Updates.encodeCell_injective.eq_iff
          · apply eval_and
            · exact eval_pathClear _ _ _ _ _ _ _ (context_board_view position ply)
                (eval_src position ply) (eval_homeRook position ply side)
            · apply eval_and
              · exact eval_not _ _ _ (eval_isAttackedBy _ _ _ _ _ _ _
                  (context_board_view position ply) (eval_otherTurn position ply)
                  (eval_src position ply))
              · exact eval_not _ _ _ (eval_isAttackedBy _ _ _ _ _ _ _
                  (context_board_view position ply) (eval_otherTurn position ply)
                  (eval_castleTransit position ply side))

theorem eval_castling {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) :
    eval castling (context position ply) = truth (IsCastling (Exec.decode position) piece ply) := by
  have he := eval_or _ _ (context position ply) _ _ (eval_castle h .kingside)
    (eval_castle h .queenside)
  apply he.trans
  apply truth_congr
  change (CastleCondition _ _ _ .kingside ∨ CastleCondition _ _ _ .queenside) ↔
    ∃ side, CastleCondition _ _ _ side
  constructor
  · rintro (hk | hq)
    · exact ⟨.kingside, hk⟩
    · exact ⟨.queenside, hq⟩
  · rintro ⟨side, hs⟩
    cases side
    · exact Or.inl hs
    · exact Or.inr hs

theorem eval_ifEq (value yes no : Expr) (n : Nat) (v : List Nat) :
    eval (ifEq value n yes no) v = if eval value v = n then eval yes v else eval no v := by
  simp [ifEq, eval]

/-- All six movement cases agree, retaining the frozen distinction from attack geometry. -/
theorem eval_pieceMovement {position : Exec.Position} {ply : Ply} {piece : Piece}
    (h : (Exec.decode position).board ply.src = some piece) :
    eval pieceMovement (context position ply) =
      truth (PieceMovement (Exec.decode position) piece ply) := by
  cases hk : piece.kind <;>
    simp only [pieceMovement, eval_ifEq, source_kind h, hk, Data.encodeKind,
      Nat.reduceEqDiff, ↓reduceIte, PieceMovement]
  · apply eval_or
    · apply eval_and
      · simp only [eval_fileDistance _ _ _ _ _ (eval_src position ply)
          (eval_dst position ply), eval, truth]
      · simp only [eval_rankDistance _ _ _ _ _ (eval_src position ply)
          (eval_dst position ply), eval, truth]
    · exact eval_castling h
  · apply eval_and
    · apply eval_or
      · simp only [eval_eq, eval_file _ _ _ (eval_src position ply),
          eval_file _ _ _ (eval_dst position ply), Fin.val_inj]
      · apply eval_or
        · simp only [eval_eq, eval_rank _ _ _ (eval_src position ply),
            eval_rank _ _ _ (eval_dst position ply), Fin.val_inj]
        · simp only [eval_eq, eval_fileDistance _ _ _ _ _ (eval_src position ply)
            (eval_dst position ply), eval_rankDistance _ _ _ _ _ (eval_src position ply)
            (eval_dst position ply)]
    · exact eval_pathClear _ _ _ _ _ _ _ (context_board_view position ply)
        (eval_src position ply) (eval_dst position ply)
  · apply eval_and
    · apply eval_or
      · simp only [eval_eq, eval_file _ _ _ (eval_src position ply),
          eval_file _ _ _ (eval_dst position ply), Fin.val_inj]
      · simp only [eval_eq, eval_rank _ _ _ (eval_src position ply),
          eval_rank _ _ _ (eval_dst position ply), Fin.val_inj]
    · exact eval_pathClear _ _ _ _ _ _ _ (context_board_view position ply)
        (eval_src position ply) (eval_dst position ply)
  · apply eval_and
    · simp only [eval_eq, eval_fileDistance _ _ _ _ _ (eval_src position ply)
        (eval_dst position ply), eval_rankDistance _ _ _ _ _ (eval_src position ply)
        (eval_dst position ply)]
    · exact eval_pathClear _ _ _ _ _ _ _ (context_board_view position ply)
        (eval_src position ply) (eval_dst position ply)
  · exact eval_knightAttacks _ _ _ _ _ (eval_src position ply) (eval_dst position ply)
  · apply eval_or
    · exact eval_pawnAdvance h
    · apply eval_or
      · exact eval_doubleAdvance h
      · exact eval_or _ _ _ _ _ (eval_pawnCapture h) (eval_enPassant h)

/-- Pseudo-legality agrees on every raw position, including absent or wrong-color sources. -/
theorem eval_pseudoLegal (position : Exec.Position) (ply : Ply) :
    eval pseudoLegal (context position ply) = truth (IsPseudoLegal (Exec.decode position) ply) := by
  cases h : (Exec.decode position).board ply.src with
  | none =>
    simp [pseudoLegal, Geometry.and, Geometry.not, eval, eval_sourceCell, h,
      Data.encodeCell, IsPseudoLegal, truth]
  | some piece =>
    have hr : eval (and (.eq (pieceColor sourceCell) turn)
        (and (Geometry.not (.eq src dst))
          (and destinationAllowed (and validPromotion pieceMovement)))) (context position ply) =
        truth (piece.color = position.turn ∧ ply.src ≠ ply.dst ∧
          DestinationAllowed (Exec.decode position) ply ∧ ValidPromotion piece ply ∧
            PieceMovement (Exec.decode position) piece ply) := by
      apply eval_and
      · simp only [eval_eq, source_color h, eval_turn, Updates.encodeColor_injective.eq_iff]
      · apply eval_and
        · exact eval_not _ _ _ (eval_sameSquare _ _ _ _ _
            (eval_src position ply) (eval_dst position ply))
        · apply eval_and
          · exact eval_destinationAllowed position ply
          · exact eval_and _ _ _ _ _ (eval_validPromotion h) (eval_pieceMovement h)
    have hn : eval (Geometry.not (.eq sourceCell (.literal 0))) (context position ply) =
        truth True := by
      simp [Geometry.not, eval, eval_sourceCell, h, truth]
    have ht := eval_and _ _ (context position ply) True _ hn hr
    apply ht.trans
    apply truth_congr
    simp only [true_and, IsPseudoLegal, h, Option.some.injEq, exists_eq_left']
    rfl

/-- The final check scan uses the updated raw board and the color that just moved. -/
theorem checkedAfter_refines (position : Exec.Position) (ply : Ply) :
    checkedAfter.eval (context position ply) =
      pure [truth (InCheck (applyBoard (Exec.decode position) ply)
        (Exec.decode position).turn)] := by
  simp only [checkedAfter, Code.comp_eval, Updates.code_refines, Bind.bind, Part.bind_some,
    Scalar.compile_eval, Part.pure_eq_some]
  have ht : eval (.sub (.literal 1) (.input 0))
      (Data.encodePosition (Exec.applyPly position ply)) = Data.encodeColor position.turn := by
    change 1 - Data.encodeColor (Exec.applyPly position ply).turn = Data.encodeColor position.turn
    have hturn : (Exec.applyPly position ply).turn = position.turn.other := rfl
    rw [hturn]
    cases position.turn <;> rfl
  rw [eval_inCheck _ _ _ _ position.turn
    (BoardView_encodePosition (Exec.applyPly position ply)) ht]
  have hb : Exec.decodeBoard (Exec.applyPly position ply).board =
      applyBoard (Exec.decode position) ply :=
    congrArg Chess.Position.board (Exec.decode_applyPly position ply)
  rw [hb]
  rfl

/-- Complete concrete legality evaluation, without validation or reachability premises. -/
theorem code_refines (position : Exec.Position) (ply : Ply) :
    code.eval (context position ply) = pure [truth (IsLegalPly (Exec.decode position) ply)] := by
  rw [code, NatCode.ifZero_eval _ _ _ _ _ (Scalar.compile_eval pseudoLegal _), eval_pseudoLegal]
  by_cases hp : IsPseudoLegal (Exec.decode position) ply
  · simp only [truth, hp, ↓reduceIte, List.headI_cons, Nat.one_ne_zero]
    simp only [Code.comp_eval, checkedAfter_refines, Bind.bind, Part.bind_some,
      NatCode.isZero_eval, List.headI_cons, Part.pure_eq_some]
    by_cases hc : InCheck (applyBoard (Exec.decode position) ply) (Exec.decode position).turn <;>
      simp [truth, hc, IsLegalPly, hp]
  · simp [truth, hp, IsLegalPly]

end Chess.Compilation.Legality
