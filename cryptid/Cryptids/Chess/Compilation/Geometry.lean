/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.Scalar
public import Cryptids.Chess.Compilation.Encoding

/-! # Concrete scalar expressions for chess geometry

Squares use the rank-major index `file + 8 * rank`. Board parameters are expressions whose
values are offsets into the current natural-number environment. Bounded board scans retain a
single expression body and compile through primitive recursion.
-/

@[expose] public section
namespace Chess.Compilation.Geometry

open ConjectureMachines.Compilation.Scalar

/-- The natural-number truth value of a decidable proposition. -/
def truth (p : Prop) [Decidable p] : Nat := if p then 1 else 0

theorem truth_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    truth p = truth q := by
  by_cases hp : p <;> simp [truth, hp, ← h]

/-- Rank-major, file-fast square index. -/
def index (square : Square) : Nat := square.file.val + 8 * square.rank.val

theorem index_lt (square : Square) : index square < 64 := by
  have := square.file.isLt
  have := square.rank.isLt
  unfold index
  omega

@[simp] theorem index_mod (square : Square) : index square % 8 = square.file.val := by
  have := square.file.isLt
  unfold index
  omega

@[simp] theorem index_div (square : Square) : index square / 8 = square.rank.val := by
  have := square.file.isLt
  unfold index
  omega

theorem index_injective : Function.Injective index := by
  intro a b h
  have hf := congrArg (· % 8) h
  have hr := congrArg (· / 8) h
  simp only [index_mod, index_div] at hf hr
  cases a
  cases b
  exact congrArg₂ Square.mk (Fin.ext hf) (Fin.ext hr)

/-- Conjunction, disjunction and negation on zero-or-one expression results. -/
def and (a b : Expr) : Expr := .ifZero a (.literal 0) b
def or (a b : Expr) : Expr := .ifZero a b (.literal 1)
def not (a : Expr) : Expr := .ifZero a (.literal 1) (.literal 0)

@[simp] theorem eval_and (a b : Expr) (v : List Nat) (p q : Prop)
    [Decidable p] [Decidable q] (ha : eval a v = truth p) (hb : eval b v = truth q) :
    eval (and a b) v = truth (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [and, eval, ha, hb, truth, hp, hq]

@[simp] theorem eval_or (a b : Expr) (v : List Nat) (p q : Prop)
    [Decidable p] [Decidable q] (ha : eval a v = truth p) (hb : eval b v = truth q) :
    eval (or a b) v = truth (p ∨ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [or, eval, ha, hb, truth, hp, hq]

@[simp] theorem eval_not (a : Expr) (v : List Nat) (p : Prop)
    [Decidable p] (ha : eval a v = truth p) : eval (not a) v = truth (¬p) := by
  by_cases hp : p <;> simp [not, eval, ha, truth, hp]

/-- Absolute difference, using the two natural-number truncated differences. -/
def distance (a b : Expr) : Expr := .add (.sub a b) (.sub b a)
def file (square : Expr) : Expr := .mod square (.literal 8)
def rank (square : Expr) : Expr := .div square (.literal 8)
def fileDistance (src dst : Expr) : Expr := distance (file src) (file dst)
def rankDistance (src dst : Expr) : Expr := distance (rank src) (rank dst)

@[simp] theorem eval_eq (a b : Expr) (v : List Nat) :
    eval (.eq a b) v = truth (eval a v = eval b v) := rfl

@[simp] theorem eval_le (a b : Expr) (v : List Nat) :
    eval (.le a b) v = truth (eval a v ≤ eval b v) := rfl

@[simp] theorem eval_lt (a b : Expr) (v : List Nat) :
    eval (.lt a b) v = truth (eval a v < eval b v) := rfl

@[simp] theorem eval_distance (a b : Expr) (v : List Nat) :
    eval (distance a b) v = Nat.dist (eval a v) (eval b v) := rfl

@[simp] theorem eval_file (square : Expr) (v : List Nat) (s : Square)
    (h : eval square v = index s) : eval (file square) v = s.file.val := by
  simp [file, eval, h]

@[simp] theorem eval_rank (square : Expr) (v : List Nat) (s : Square)
    (h : eval square v = index s) : eval (rank square) v = s.rank.val := by
  simp [rank, eval, h]

theorem eval_fileDistance (src dst : Expr) (v : List Nat) (s d : Square)
    (hs : eval src v = index s) (hd : eval dst v = index d) :
    eval (fileDistance src dst) v = Chess.fileDistance s d := by
  simp only [fileDistance, eval_distance, eval_file _ _ _ hs, eval_file _ _ _ hd,
    Chess.fileDistance]

theorem eval_rankDistance (src dst : Expr) (v : List Nat) (s d : Square)
    (hs : eval src v = index s) (hd : eval dst v = index d) :
    eval (rankDistance src dst) v = Chess.rankDistance s d := by
  simp only [rankDistance, eval_distance, eval_rank _ _ _ hs, eval_rank _ _ _ hd,
    Chess.rankDistance]

/-- Strict betweenness does not require a minimum or maximum primitive. -/
def strictlyBetween (a b x : Expr) : Expr :=
  or (and (.lt a x) (.lt x b)) (and (.lt b x) (.lt x a))

theorem strictlyBetween_iff (a b x : Nat) :
    (a < x ∧ x < b) ∨ (b < x ∧ x < a) ↔ Chess.StrictlyBetween a b x := by
  unfold Chess.StrictlyBetween
  omega

theorem eval_strictlyBetween (a b x : Expr) (v : List Nat) :
    eval (strictlyBetween a b x) v =
      truth (Chess.StrictlyBetween (eval a v) (eval b v) (eval x v)) := by
  calc
    _ = truth (((eval a v < eval x v) ∧ (eval x v < eval b v)) ∨
        ((eval b v < eval x v) ∧ (eval x v < eval a v))) :=
      eval_or _ _ _ _ _ (eval_and _ _ _ _ _ rfl rfl) (eval_and _ _ _ _ _ rfl rfl)
    _ = _ := truth_congr (strictlyBetween_iff _ _ _)

/-- Frozen open-segment geometry, including its diagonal strictness tests. -/
def onOpenSegment (src dst square : Expr) : Expr :=
  or
    (and (.eq (file src) (file dst))
      (and (.eq (file square) (file src))
        (strictlyBetween (rank src) (rank dst) (rank square))))
    (or
      (and (.eq (rank src) (rank dst))
        (and (.eq (rank square) (rank src))
          (strictlyBetween (file src) (file dst) (file square))))
      (and (.eq (fileDistance src dst) (rankDistance src dst))
        (and (.eq (fileDistance src square) (rankDistance src square))
          (and (strictlyBetween (file src) (file dst) (file square))
            (strictlyBetween (rank src) (rank dst) (rank square))))))

theorem eval_onOpenSegment (src dst square : Expr) (v : List Nat) (s d q : Square)
    (hs : eval src v = index s) (hd : eval dst v = index d)
    (hq : eval square v = index q) :
    eval (onOpenSegment src dst square) v = truth (Chess.OnOpenSegment s d q) := by
  unfold onOpenSegment Chess.OnOpenSegment
  apply eval_or
  all_goals repeat' first | apply eval_and | apply eval_or
  all_goals try simp only [eval_eq, eval_strictlyBetween,
    eval_file _ _ _ hs, eval_file _ _ _ hd, eval_file _ _ _ hq,
    eval_rank _ _ _ hs, eval_rank _ _ _ hd, eval_rank _ _ _ hq,
    eval_fileDistance _ _ _ _ _ hs hd, eval_fileDistance _ _ _ _ _ hs hq,
    eval_rankDistance _ _ _ _ _ hs hd, eval_rankDistance _ _ _ _ _ hs hq, Fin.val_inj]

/-- Decode any scan counter modulo 64; scans below 64 retain the exact counter. -/
def squareAt (i : Nat) : Square :=
  ⟨⟨i % 8, Nat.mod_lt _ (by decide)⟩,
    ⟨i / 8 % 8, Nat.mod_lt _ (by decide)⟩⟩

theorem index_squareAt (i : Nat) (hi : i < 64) : index (squareAt i) = i := by
  simp only [index, squareAt]
  omega

@[simp] theorem squareAt_index (square : Square) : squareAt (index square) = square := by
  apply index_injective
  exact index_squareAt _ (index_lt square)

/-- A bounded universal scan. The body receives the index and previous truth value. -/
def all (count : Nat) (body : Expr) : Expr :=
  .fold (.literal count) (.literal 1) (.ifZero (.input 1) (.literal 0) body)

theorem bounded_forall_succ (P : Nat → Prop) (n : Nat) :
    (∀ i, i < n + 1 → P i) ↔ (∀ i, i < n → P i) ∧ P n := by
  constructor
  · intro h
    exact ⟨fun i hi ↦ h i (by omega), h n (by omega)⟩
  · rintro ⟨h, hn⟩ i hi
    by_cases heq : i = n
    · simpa [heq] using hn
    · exact h i (by omega)

theorem truth_and (p q : Prop) [Decidable p] [Decidable q] :
    (if truth p = 0 then 0 else truth q) = truth (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [truth, hp, hq]

theorem eval_all (count : Nat) (body : Expr) (v : List Nat) (P : Nat → Prop)
    [DecidablePred P]
    (hb : ∀ i, i < count → ∀ a, eval body (i :: a :: v) = truth (P i)) :
    eval (all count body) v = truth (∀ i, i < count → P i) := by
  induction count with
  | zero => simp [all, eval, truth]
  | succ n ih =>
    change (if eval (all n body) v = 0 then 0
      else eval body (n :: eval (all n body) v :: v)) = _
    rw [ih (fun i hi ↦ hb i (by omega)), hb n (by omega), truth_and]
    exact truth_congr (bounded_forall_succ P n).symm

/-- A board view relates each of the 64 words to an arbitrary raw reference board. -/
def BoardView (base : Expr) (v : List Nat) (board : Board) : Prop :=
  ∀ square, v[eval base v + index square]?.getD 0 = Data.encodeCell (board square)

def boardAt (base square : Expr) : Expr := .lookup (.add base square)

/-- A board offset gains the number of freshly prefixed loop variables. -/
def liftBoard (count : Nat) (base : Expr) : Expr := .add (.literal count) (.drop count base)

theorem eval_boardAt (base square : Expr) (v : List Nat) (board : Board)
    (view : BoardView base v board) (s : Square) (hs : eval square v = index s) :
    eval (boardAt base square) v = Data.encodeCell (board s) := by
  simpa only [boardAt, eval, hs] using view s

theorem BoardView_lift (base : Expr) (v front : List Nat) (board : Board)
    (view : BoardView base v board) :
    BoardView (liftBoard front.length base) (front ++ v) board := by
  intro square
  simp only [liftBoard, eval, List.drop_left]
  rw [List.getElem?_append_right (by omega)]
  simpa only [Nat.add_assoc, Nat.add_sub_cancel_left] using view square

theorem BoardView_lift_two (base : Expr) (v : List Nat) (i a : Nat) (board : Board)
    (view : BoardView base v board) : BoardView (liftBoard 2 base) (i :: a :: v) board := by
  simpa only [List.length_cons, List.length_nil, List.cons_append, List.nil_append] using
    BoardView_lift base v [i, a] board view

/-- Every concrete raw board has the required view; no legal-position invariant is needed. -/
theorem BoardView_encodeBoard (board : Exec.Board) :
    BoardView (.literal 0) (Data.encodeBoard board) (Exec.decodeBoard board) := by
  intro square
  simp only [eval, Nat.zero_add, Data.encodeBoard, List.getElem?_ofFn, index_lt,
    ↓reduceDIte, Option.getD_some, index_div, index_mod, Exec.decodeBoard]

/-- The seven metadata words put a position's board at literal offset seven. -/
theorem BoardView_encodePosition (position : Exec.Position) :
    BoardView (.literal 7) (Data.encodePosition position) (Exec.decodeBoard position.board) := by
  have h := BoardView_lift (.literal 0) (Data.encodeBoard position.board)
    [Data.encodeColor position.turn,
      Data.encodeBool position.castlingRights.whiteKingside,
      Data.encodeBool position.castlingRights.whiteQueenside,
      Data.encodeBool position.castlingRights.blackKingside,
      Data.encodeBool position.castlingRights.blackQueenside,
      Data.encodeTarget position.enPassantTarget, position.halfmoveClock]
    (Exec.decodeBoard position.board) (BoardView_encodeBoard position.board)
  simpa only [Data.encodePosition, BoardView, liftBoard, eval, Nat.add_zero,
    List.length_cons, List.length_nil] using h

/-- Appended arguments do not alter a complete literal-offset board block. -/
theorem BoardView_append (offset : Nat) (v tail : List Nat) (board : Board)
    (view : BoardView (.literal offset) v board) (bound : offset + 64 ≤ v.length) :
    BoardView (.literal offset) (v ++ tail) board := by
  intro square
  change (v ++ tail)[offset + index square]?.getD 0 = _
  rw [List.getElem?_append_left (by have := index_lt square; omega)]
  exact view square

theorem BoardView_encodePosition_append (position : Exec.Position) (tail : List Nat) :
    BoardView (.literal 7) (Data.encodePosition position ++ tail)
      (Exec.decodeBoard position.board) := by
  exact BoardView_append 7 _ tail _ (BoardView_encodePosition position) (by simp)

@[simp] theorem encodeCell_eq_zero (cell : Option Piece) :
    Data.encodeCell cell = 0 ↔ cell = none := by
  cases cell with
  | none => simp [Data.encodeCell]
  | some piece => simp [Data.encodeCell]

/-- A single 64-square scan checks all blockers in the frozen open segment. -/
def pathClear (base src dst : Expr) : Expr :=
  all 64 (or
    (not (onOpenSegment (.drop 2 src) (.drop 2 dst) (.input 0)))
    (.eq (boardAt (liftBoard 2 base) (.input 0)) (.literal 0)))

attribute [local irreducible] all

theorem eval_pathClear (base src dst : Expr) (v : List Nat) (board : Board) (s d : Square)
    (view : BoardView base v board) (hs : eval src v = index s) (hd : eval dst v = index d) :
    eval (pathClear base src dst) v = truth (Chess.PathClear board s d) := by
  let body := or (not (onOpenSegment (.drop 2 src) (.drop 2 dst) (.input 0)))
    (.eq (boardAt (liftBoard 2 base) (.input 0)) (.literal 0))
  let P := fun i ↦ ¬Chess.OnOpenSegment s d (squareAt i) ∨ board (squareAt i) = none
  have hb : ∀ i, i < 64 → ∀ a, eval body (i :: a :: v) = truth (P i) := by
    intro i hi a
    apply eval_or
    · apply eval_not
      exact eval_onOpenSegment _ _ _ _ _ _ _ hs hd (index_squareAt i hi).symm
    · simpa only [eval_eq,
        eval_boardAt _ (.input 0) _ _ (BoardView_lift_two _ _ i a _ view)
          (squareAt i) (index_squareAt i hi).symm, eval, truth] using
        truth_congr (encodeCell_eq_zero (board (squareAt i)))
  have hscan := eval_all 64 body v P hb
  have hc : (∀ i, i < 64 → P i) ↔ Chess.PathClear board s d := by
    constructor
    · intro h square hsegment
      have hsquare := h (index square) (index_lt square)
      simp only [P, squareAt_index] at hsquare
      exact hsquare.resolve_left (fun h ↦ h hsegment)
    · intro h i _
      by_cases hsegment : Chess.OnOpenSegment s d (squareAt i)
      · exact Or.inr (h _ hsegment)
      · exact Or.inl hsegment
  exact hscan.trans (truth_congr hc)

/-- Pawn attack geometry uses color zero for White and one for Black. -/
def pawnAttacks (color src dst : Expr) : Expr :=
  and (.eq (fileDistance src dst) (.literal 1))
    (.ifZero color
      (.eq (.add (rank src) (.literal 1)) (rank dst))
      (.eq (.add (rank dst) (.literal 1)) (rank src)))

theorem eval_pawnAttacks (color src dst : Expr) (v : List Nat) (c : Color) (s d : Square)
    (hc : eval color v = Data.encodeColor c)
    (hs : eval src v = index s) (hd : eval dst v = index d) :
    eval (pawnAttacks color src dst) v = truth (Chess.PawnAttacks c s d) := by
  cases c <;> unfold pawnAttacks Chess.PawnAttacks <;> apply eval_and
  all_goals simp [eval_fileDistance _ _ _ _ _ hs hd, eval, rank, hc, hs, hd,
    Data.encodeColor, truth]

theorem eval_sameSquare (src dst : Expr) (v : List Nat) (s d : Square)
    (hs : eval src v = index s) (hd : eval dst v = index d) :
    eval (.eq src dst) v = truth (s = d) := by
  simp only [eval_eq, hs, hd, index_injective.eq_iff]

def kingAttacks (src dst : Expr) : Expr :=
  and (not (.eq src dst))
    (and (.le (fileDistance src dst) (.literal 1))
      (.le (rankDistance src dst) (.literal 1)))

theorem eval_kingAttacks (src dst : Expr) (v : List Nat) (s d : Square)
    (hs : eval src v = index s) (hd : eval dst v = index d) :
    eval (kingAttacks src dst) v =
      truth (s ≠ d ∧ Chess.fileDistance s d ≤ 1 ∧ Chess.rankDistance s d ≤ 1) := by
  unfold kingAttacks
  apply eval_and
  · exact eval_not _ _ _ (eval_sameSquare _ _ _ _ _ hs hd)
  · apply eval_and
    · simp only [eval_fileDistance _ _ _ _ _ hs hd, eval, truth]
    · simp only [eval_rankDistance _ _ _ _ _ hs hd, eval, truth]

def knightAttacks (src dst : Expr) : Expr :=
  or (and (.eq (fileDistance src dst) (.literal 1))
      (.eq (rankDistance src dst) (.literal 2)))
    (and (.eq (fileDistance src dst) (.literal 2))
      (.eq (rankDistance src dst) (.literal 1)))

theorem eval_knightAttacks (src dst : Expr) (v : List Nat) (s d : Square)
    (hs : eval src v = index s) (hd : eval dst v = index d) :
    eval (knightAttacks src dst) v =
      truth ((Chess.fileDistance s d = 1 ∧ Chess.rankDistance s d = 2) ∨
        (Chess.fileDistance s d = 2 ∧ Chess.rankDistance s d = 1)) := by
  unfold knightAttacks
  apply eval_or <;> apply eval_and
  all_goals simp only [eval_fileDistance _ _ _ _ _ hs hd,
    eval_rankDistance _ _ _ _ _ hs hd, eval, truth]

def bishopAttacks (base src dst : Expr) : Expr :=
  and (not (.eq src dst))
    (and (.eq (fileDistance src dst) (rankDistance src dst)) (pathClear base src dst))

theorem eval_bishopAttacks (base src dst : Expr) (v : List Nat) (board : Board) (s d : Square)
    (view : BoardView base v board) (hs : eval src v = index s) (hd : eval dst v = index d) :
    eval (bishopAttacks base src dst) v =
      truth (s ≠ d ∧ Chess.fileDistance s d = Chess.rankDistance s d ∧
        Chess.PathClear board s d) := by
  unfold bishopAttacks
  apply eval_and
  · exact eval_not _ _ _ (eval_sameSquare _ _ _ _ _ hs hd)
  · apply eval_and
    · simp only [eval_eq, eval_fileDistance _ _ _ _ _ hs hd,
        eval_rankDistance _ _ _ _ _ hs hd]
    · exact eval_pathClear _ _ _ _ _ _ _ view hs hd

def rookAttacks (base src dst : Expr) : Expr :=
  and (not (.eq src dst))
    (and (or (.eq (file src) (file dst)) (.eq (rank src) (rank dst)))
      (pathClear base src dst))

theorem eval_rookAttacks (base src dst : Expr) (v : List Nat) (board : Board) (s d : Square)
    (view : BoardView base v board) (hs : eval src v = index s) (hd : eval dst v = index d) :
    eval (rookAttacks base src dst) v =
      truth (s ≠ d ∧ (s.file = d.file ∨ s.rank = d.rank) ∧ Chess.PathClear board s d) := by
  unfold rookAttacks
  apply eval_and
  · exact eval_not _ _ _ (eval_sameSquare _ _ _ _ _ hs hd)
  · apply eval_and
    · apply eval_or
      · simp only [eval_eq, eval_file _ _ _ hs, eval_file _ _ _ hd, Fin.val_inj]
      · simp only [eval_eq, eval_rank _ _ _ hs, eval_rank _ _ _ hd, Fin.val_inj]
    · exact eval_pathClear _ _ _ _ _ _ _ view hs hd

def queenAttacks (base src dst : Expr) : Expr :=
  and (not (.eq src dst))
    (and (or (.eq (file src) (file dst))
      (or (.eq (rank src) (rank dst)) (.eq (fileDistance src dst) (rankDistance src dst))))
      (pathClear base src dst))

theorem eval_queenAttacks (base src dst : Expr) (v : List Nat) (board : Board) (s d : Square)
    (view : BoardView base v board) (hs : eval src v = index s) (hd : eval dst v = index d) :
    eval (queenAttacks base src dst) v =
      truth (s ≠ d ∧ (s.file = d.file ∨ s.rank = d.rank ∨
        Chess.fileDistance s d = Chess.rankDistance s d) ∧ Chess.PathClear board s d) := by
  unfold queenAttacks
  apply eval_and
  · exact eval_not _ _ _ (eval_sameSquare _ _ _ _ _ hs hd)
  · apply eval_and
    · apply eval_or
      · simp only [eval_eq, eval_file _ _ _ hs, eval_file _ _ _ hd, Fin.val_inj]
      · apply eval_or
        · simp only [eval_eq, eval_rank _ _ _ hs, eval_rank _ _ _ hd, Fin.val_inj]
        · simp only [eval_eq, eval_fileDistance _ _ _ _ _ hs hd,
            eval_rankDistance _ _ _ _ _ hs hd]
    · exact eval_pathClear _ _ _ _ _ _ _ view hs hd

def ifEq (value : Expr) (n : Nat) (yes no : Expr) : Expr :=
  .ifZero (.eq value (.literal n)) no yes

/-- All six piece cases, with a zero fallback for malformed piece-kind words. -/
def pieceAttacks (base color kind src dst : Expr) : Expr :=
  ifEq kind 0 (kingAttacks src dst)
    (ifEq kind 1 (queenAttacks base src dst)
      (ifEq kind 2 (rookAttacks base src dst)
        (ifEq kind 3 (bishopAttacks base src dst)
          (ifEq kind 4 (knightAttacks src dst)
            (ifEq kind 5 (pawnAttacks color src dst) (.literal 0))))))

theorem eval_pieceAttacks (base color kind src dst : Expr) (v : List Nat) (board : Board)
    (piece : Piece) (s d : Square) (view : BoardView base v board)
    (hc : eval color v = Data.encodeColor piece.color)
    (hk : eval kind v = Data.encodeKind piece.kind)
    (hs : eval src v = index s) (hd : eval dst v = index d) :
    eval (pieceAttacks base color kind src dst) v = truth (Chess.PieceAttacks board piece s d) := by
  rcases piece with ⟨c, k⟩
  cases k
  all_goals simp only [pieceAttacks, ifEq, eval, hk, Data.encodeKind,
    ↓reduceIte, Nat.reduceEqDiff]
  case king => exact eval_kingAttacks _ _ _ _ _ hs hd
  case queen => exact eval_queenAttacks _ _ _ _ _ _ _ view hs hd
  case rook => exact eval_rookAttacks _ _ _ _ _ _ _ view hs hd
  case bishop => exact eval_bishopAttacks _ _ _ _ _ _ _ view hs hd
  case knight => exact eval_knightAttacks _ _ _ _ _ hs hd
  case pawn => exact eval_pawnAttacks _ _ _ _ _ _ _ hc hs hd

/-- Existential board scans use the proved universal scan and Boolean complement. -/
def any (count : Nat) (body : Expr) : Expr := not (all count (not body))

theorem eval_any (count : Nat) (body : Expr) (v : List Nat) (P : Nat → Prop)
    [DecidablePred P]
    (hb : ∀ i, i < count → ∀ a, eval body (i :: a :: v) = truth (P i)) :
    eval (any count body) v = truth (∃ i, i < count ∧ P i) := by
  have hall := eval_all count (not body) v (fun i ↦ ¬P i)
    (fun i hi a ↦ eval_not _ _ _ (hb i hi a))
  have hnot := eval_not _ _ _ hall
  apply hnot.trans
  apply truth_congr
  classical
  simp only [not_forall, not_not, exists_prop]

/-- Color and kind fields in a nonempty cell word. -/
def cellColor (cell : Expr) : Expr := .div (.sub cell (.literal 1)) (.literal 6)
def cellKind (cell : Expr) : Expr := .mod (.sub cell (.literal 1)) (.literal 6)

theorem cellColor_encode (piece : Piece) :
    (Data.encodeCell (some piece) - 1) / 6 = Data.encodeColor piece.color := by
  rcases piece with ⟨c, k⟩
  cases c <;> cases k <;> rfl

theorem cellKind_encode (piece : Piece) :
    (Data.encodeCell (some piece) - 1) % 6 = Data.encodeKind piece.kind := by
  rcases piece with ⟨c, k⟩
  cases c <;> cases k <;> rfl

theorem encodeColor_injective : Function.Injective Data.encodeColor := by
  intro a b h
  cases a <;> cases b <;> simp_all [Data.encodeColor]

def attacker (base color src dst : Expr) : Expr :=
  let cell := boardAt base src
  and (.lt (.literal 0) cell)
    (and (.eq (cellColor cell) color)
      (pieceAttacks base (cellColor cell) (cellKind cell) src dst))

theorem eval_attacker (base color src dst : Expr) (v : List Nat) (board : Board)
    (c : Color) (s d : Square) (view : BoardView base v board)
    (hc : eval color v = Data.encodeColor c)
    (hs : eval src v = index s) (hd : eval dst v = index d) :
    eval (attacker base color src dst) v =
      truth (∃ piece, board s = some piece ∧ piece.color = c ∧
        Chess.PieceAttacks board piece s d) := by
  cases hcell : board s with
  | none =>
    simp only [attacker, and, eval, eval_boardAt _ _ _ _ view _ hs, hcell,
      Data.encodeCell, lt_self_iff_false, ↓reduceIte, truth,
      reduceCtorEq, false_and, exists_false]
  | some piece =>
    have hcolor : eval (cellColor (boardAt base src)) v = Data.encodeColor piece.color := by
      simp only [cellColor, eval, eval_boardAt _ _ _ _ view _ hs, hcell, cellColor_encode]
    have hkind : eval (cellKind (boardAt base src)) v = Data.encodeKind piece.kind := by
      simp only [cellKind, eval, eval_boardAt _ _ _ _ view _ hs, hcell, cellKind_encode]
    have hpiece := eval_pieceAttacks base _ _ src dst v board piece s d view hcolor hkind hs hd
    have hpair : eval (and (.eq (cellColor (boardAt base src)) color)
        (pieceAttacks base (cellColor (boardAt base src))
          (cellKind (boardAt base src)) src dst)) v =
        truth (piece.color = c ∧ Chess.PieceAttacks board piece s d) := by
      apply eval_and
      · simp only [eval_eq, hcolor, hc, encodeColor_injective.eq_iff]
      · exact hpiece
    have hpositive : eval (.lt (.literal 0) (boardAt base src)) v = truth True := by
      simp only [eval, eval_boardAt _ _ _ _ view _ hs, hcell, Data.encodeCell, truth,
        Nat.lt_add_right, Nat.zero_lt_one, ↓reduceIte]
    have htotal := eval_and _ _ _ True _ hpositive hpair
    simpa only [attacker, true_and, Option.some.injEq, exists_eq_left'] using htotal

/-- Test each possible attacker square; piece data comes from the encoded board. -/
def isAttackedBy (base color square : Expr) : Expr :=
  any 64 (attacker (liftBoard 2 base) (.drop 2 color) (.input 0) (.drop 2 square))

theorem eval_isAttackedBy (base color square : Expr) (v : List Nat) (board : Board)
    (c : Color) (d : Square) (view : BoardView base v board)
    (hc : eval color v = Data.encodeColor c) (hd : eval square v = index d) :
    eval (isAttackedBy base color square) v = truth (Chess.IsAttackedBy board c d) := by
  let body := attacker (liftBoard 2 base) (.drop 2 color) (.input 0) (.drop 2 square)
  let P := fun i ↦ ∃ piece, board (squareAt i) = some piece ∧ piece.color = c ∧
    Chess.PieceAttacks board piece (squareAt i) d
  have hb : ∀ i, i < 64 → ∀ a, eval body (i :: a :: v) = truth (P i) := by
    intro i hi a
    exact eval_attacker _ _ (.input 0) _ _ _ c (squareAt i) d
      (BoardView_lift_two _ _ i a _ view) hc (index_squareAt i hi).symm hd
  have hscan := eval_any 64 body v P hb
  have heq : (∃ i, i < 64 ∧ P i) ↔ Chess.IsAttackedBy board c d := by
    constructor
    · rintro ⟨i, _, piece, hpiece⟩
      exact ⟨squareAt i, piece, hpiece⟩
    · rintro ⟨square, piece, hpiece⟩
      exact ⟨index square, index_lt square, piece, by simpa only [squareAt_index] using hpiece⟩
  exact hscan.trans (truth_congr heq)

def otherColor (color : Expr) : Expr := .sub (.literal 1) color

theorem eval_otherColor (color : Expr) (v : List Nat) (c : Color)
    (hc : eval color v = Data.encodeColor c) :
    eval (otherColor color) v = Data.encodeColor c.other := by
  cases c <;> simp [otherColor, eval, hc, Data.encodeColor, Color.other]

def kingCell (color : Expr) : Expr := .add (.literal 1) (.mul (.literal 6) color)

theorem eval_kingCell (color : Expr) (v : List Nat) (c : Color)
    (hc : eval color v = Data.encodeColor c) :
    eval (kingCell color) v = Data.encodeCell (some ⟨c, .king⟩) := by
  simp [kingCell, eval, hc, Data.encodeCell, Data.encodeKind]

/-- Exact encoded-cell equality is injective, including empty and both colors. -/
theorem encodeCell_injective : Function.Injective Data.encodeCell := by
  intro a b h
  have := congrArg Data.cellOfNat h
  simpa only [Data.cellOfNat_encodeCell] using this

def checkedKing (base color square : Expr) : Expr :=
  and (.eq (boardAt base square) (kingCell color))
    (isAttackedBy base (otherColor color) square)

theorem eval_checkedKing (base color square : Expr) (v : List Nat) (board : Board)
    (c : Color) (s : Square) (view : BoardView base v board)
    (hc : eval color v = Data.encodeColor c) (hs : eval square v = index s) :
    eval (checkedKing base color square) v =
      truth (board s = some ⟨c, .king⟩ ∧ Chess.IsAttackedBy board c.other s) := by
  unfold checkedKing
  apply eval_and
  · simp only [eval_eq, eval_boardAt _ _ _ _ view _ hs, eval_kingCell _ _ _ hc,
      encodeCell_injective.eq_iff]
  · exact eval_isAttackedBy _ _ _ _ _ _ _ view (eval_otherColor _ _ _ hc) hs

/-- Scan every king square, preserving the frozen existential semantics on raw boards. -/
def inCheck (base color : Expr) : Expr :=
  any 64 (checkedKing (liftBoard 2 base) (.drop 2 color) (.input 0))

theorem eval_inCheck (base color : Expr) (v : List Nat) (board : Board) (c : Color)
    (view : BoardView base v board) (hc : eval color v = Data.encodeColor c) :
    eval (inCheck base color) v = truth (Chess.InCheck board c) := by
  let body := checkedKing (liftBoard 2 base) (.drop 2 color) (.input 0)
  let P := fun i ↦ board (squareAt i) = some ⟨c, .king⟩ ∧
    Chess.IsAttackedBy board c.other (squareAt i)
  have hb : ∀ i, i < 64 → ∀ a, eval body (i :: a :: v) = truth (P i) := by
    intro i hi a
    exact eval_checkedKing _ _ (.input 0) _ _ c (squareAt i)
      (BoardView_lift_two _ _ i a _ view) hc (index_squareAt i hi).symm
  have hscan := eval_any 64 body v P hb
  have heq : (∃ i, i < 64 ∧ P i) ↔ Chess.InCheck board c := by
    constructor
    · rintro ⟨i, _, hking⟩
      exact ⟨squareAt i, hking⟩
    · rintro ⟨square, hking⟩
      exact ⟨index square, index_lt square, by simpa only [P, squareAt_index] using hking⟩
  exact hscan.trans (truth_congr heq)

/-- The compiled path procedure has the exact partial-function result, on every raw board view. -/
theorem compile_pathClear_eval (base src dst : Expr) (v : List Nat) (board : Board) (s d : Square)
    (view : BoardView base v board) (hs : eval src v = index s) (hd : eval dst v = index d) :
    (compile (pathClear base src dst)).eval v = pure [truth (Chess.PathClear board s d)] := by
  rw [compile_eval, eval_pathClear _ _ _ _ _ _ _ view hs hd]

theorem compile_pawnAttacks_eval (color src dst : Expr) (v : List Nat) (c : Color) (s d : Square)
    (hc : eval color v = Data.encodeColor c)
    (hs : eval src v = index s) (hd : eval dst v = index d) :
    (compile (pawnAttacks color src dst)).eval v = pure [truth (Chess.PawnAttacks c s d)] := by
  rw [compile_eval, eval_pawnAttacks _ _ _ _ _ _ _ hc hs hd]

theorem compile_pieceAttacks_eval (base color kind src dst : Expr) (v : List Nat) (board : Board)
    (piece : Piece) (s d : Square) (view : BoardView base v board)
    (hc : eval color v = Data.encodeColor piece.color)
    (hk : eval kind v = Data.encodeKind piece.kind)
    (hs : eval src v = index s) (hd : eval dst v = index d) :
    (compile (pieceAttacks base color kind src dst)).eval v =
      pure [truth (Chess.PieceAttacks board piece s d)] := by
  rw [compile_eval, eval_pieceAttacks _ _ _ _ _ _ _ _ _ _ view hc hk hs hd]

theorem compile_isAttackedBy_eval (base color square : Expr) (v : List Nat) (board : Board)
    (c : Color) (d : Square) (view : BoardView base v board)
    (hc : eval color v = Data.encodeColor c) (hd : eval square v = index d) :
    (compile (isAttackedBy base color square)).eval v =
      pure [truth (Chess.IsAttackedBy board c d)] := by
  rw [compile_eval, eval_isAttackedBy _ _ _ _ _ _ _ view hc hd]

theorem compile_inCheck_eval (base color : Expr) (v : List Nat) (board : Board) (c : Color)
    (view : BoardView base v board) (hc : eval color v = Data.encodeColor c) :
    (compile (inCheck base color)).eval v = pure [truth (Chess.InCheck board c)] := by
  rw [compile_eval, eval_inCheck _ _ _ _ _ view hc]

namespace Fixtures

/-- White king e1 and black rook e8, with optional e4 blocker and a second White king a1. -/
def rookBoard (blocked secondKing : Bool) : List Nat :=
  List.ofFn fun i : Fin 64 ↦
    if i.val = 4 then 1
    else if i.val = 60 then 9
    else if i.val = 28 ∧ blocked then 6
    else if i.val = 0 ∧ secondKing then 1
    else 0

/-- The rook attacks e1 along an empty file. Checked by kernel reduction of the scalar program. -/
theorem rook_check : eval (inCheck (.literal 0) (.literal 0)) (rookBoard false false) = 1 := by
  decide +kernel

theorem rook_blocked : eval (inCheck (.literal 0) (.literal 0)) (rookBoard true false) = 0 := by
  decide +kernel

/-- On raw boards with multiple same-color kings, the frozen check predicate remains existential. -/
theorem multiple_kings : eval (inCheck (.literal 0) (.literal 0)) (rookBoard false true) = 1 := by
  decide +kernel

/-- A missing king makes the frozen existential check predicate false. -/
theorem missing_king : eval (inCheck (.literal 0) (.literal 0))
    (List.ofFn fun i : Fin 64 ↦ if i.val = 60 then 9 else 0) = 0 := by
  decide +kernel

theorem pawn_white_boundary :
    eval (pawnAttacks (.literal 0) (.literal 63) (.literal 0)) [] = 0 := by
  decide +kernel

theorem pawn_black_boundary :
    eval (pawnAttacks (.literal 1) (.literal 0) (.literal 63)) [] = 0 := by
  decide +kernel

theorem knight_attack : eval (knightAttacks (.literal 0) (.literal 17)) [] = 1 := by
  decide +kernel

theorem rook_no_wrap :
    eval (rookAttacks (.literal 0) (.literal 7) (.literal 8)) (List.replicate 64 0) = 0 := by
  decide +kernel

/-- These fixture equations also certify actual `ToPartrec.Code.eval`, via compiler refinement. -/
theorem compiled_rook_check :
    (compile (inCheck (.literal 0) (.literal 0))).eval (rookBoard false false) = pure [1] := by
  rw [compile_eval, rook_check]

theorem compiled_rook_blocked :
    (compile (inCheck (.literal 0) (.literal 0))).eval (rookBoard true false) = pure [0] := by
  rw [compile_eval, rook_blocked]

theorem compiled_multiple_kings :
    (compile (inCheck (.literal 0) (.literal 0))).eval (rookBoard false true) = pure [1] := by
  rw [compile_eval, multiple_kings]

theorem compiled_missing_king :
    (compile (inCheck (.literal 0) (.literal 0))).eval
      (List.ofFn fun i : Fin 64 ↦ if i.val = 60 then 9 else 0) = pure [0] := by
  rw [compile_eval, missing_king]

end Fixtures

end Chess.Compilation.Geometry
