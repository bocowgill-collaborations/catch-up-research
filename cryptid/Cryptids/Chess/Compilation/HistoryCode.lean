/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Compilation.History
public import Cryptids.Chess.Compilation.Geometry
public import Cryptids.Chess.Compilation.WithoutDead
public import Cryptids.Chess.Compilation.Updates
public import Cryptids.Chess.Compilation.Program
public import Cryptids.Compilation.Commands

/-! # Concrete full-history procedures

Candidate loops use the frozen file-then-rank square order and all seven promotion requests.
Modular callees are actual `ToPartrec.Code` terms with explicit semantic contracts; they are
not additional machine instructions. The final chess program must instantiate every callee.
-/

@[expose] public section

namespace Chess.Compilation.HistoryCode

open ConjectureMachines.Compilation Turing.ToPartrec
open Scalar (Expr)
open Geometry (truth index)

set_option backward.isDefEq.respectTransparency false

attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some

/-- The unchecked promotion word used by the position-update interface. -/
def promotionWord : Option PieceKind → Nat
  | none => 0
  | some kind => 1 + Data.encodeKind kind

/-- Three words in the same raw move format as `Updates.encodePly`. -/
def plyWords (ply : Ply) : List Nat :=
  [index ply.src, index ply.dst, promotionWord ply.promotion]

theorem plyWords_eq (ply : Ply) : plyWords ply = Updates.encodePly ply := rfl

/-- File-then-rank square grouping, with a total modulo interpretation outside the scan. -/
def candidateSquare (n : Nat) : Square :=
  ⟨⟨n / 8 % 8, Nat.mod_lt _ (by decide)⟩, ⟨n % 8, Nat.mod_lt _ (by decide)⟩⟩

/-- All seven promotion requests; king and pawn requests are retained for raw positions. -/
def candidatePromotion (n : Nat) : Option PieceKind :=
  match n % 7 with
  | 0 => none
  | 1 => some .king
  | 2 => some .queen
  | 3 => some .rook
  | 4 => some .bishop
  | 5 => some .knight
  | _ => some .pawn

/-- The promotion index is the innermost loop, then destination, then source. -/
def candidate (n : Nat) : Ply :=
  ⟨candidateSquare (n / 448), candidateSquare (n / 7), candidatePromotion n⟩

/-- The inverse candidate index, before the positive action-code offset. -/
def candidateIndex (ply : Ply) : Nat :=
  7 * (64 * (8 * ply.src.file.val + ply.src.rank.val) +
    (8 * ply.dst.file.val + ply.dst.rank.val)) + promotionWord ply.promotion

theorem promotionWord_lt (promotion : Option PieceKind) : promotionWord promotion < 7 := by
  cases promotion with
  | none => decide
  | some kind => cases kind <;> decide

theorem candidateIndex_lt (ply : Ply) : candidateIndex ply < 28672 := by
  have := ply.src.file.isLt
  have := ply.src.rank.isLt
  have := ply.dst.file.isLt
  have := ply.dst.rank.isLt
  have := promotionWord_lt ply.promotion
  unfold candidateIndex
  omega

@[simp] theorem candidatePromotion_word (promotion : Option PieceKind) :
    candidatePromotion (promotionWord promotion) = promotion := by
  cases promotion with
  | none => rfl
  | some kind => cases kind <;> rfl

@[simp] theorem promotionWord_candidate (n : Nat) :
    promotionWord (candidatePromotion n) = n % 7 := by
  have hn : n % 7 < 7 := Nat.mod_lt _ (by decide)
  generalize h : n % 7 = m at *
  interval_cases m <;> simp [candidatePromotion, h, promotionWord, Data.encodeKind]

@[simp] theorem candidate_inverse (ply : Ply) : candidate (candidateIndex ply) = ply := by
  rcases ply with ⟨src, dst, promotion⟩
  rcases src with ⟨sf, sr⟩
  rcases dst with ⟨df, dr⟩
  have hp := promotionWord_lt promotion
  have hs := sf.isLt
  have hr := sr.isLt
  have hd := df.isLt
  have hd' := dr.isLt
  have hsquare : candidateSquare
      ((7 * (64 * (8 * sf.val + sr.val) + (8 * df.val + dr.val)) +
        promotionWord promotion) / 448) = ⟨sf, sr⟩ := by
    dsimp only [candidateSquare]
    apply congrArg₂ Square.mk <;> apply Fin.ext <;> dsimp only <;> omega
  have dsquare : candidateSquare
      ((7 * (64 * (8 * sf.val + sr.val) + (8 * df.val + dr.val)) +
        promotionWord promotion) / 7) = ⟨df, dr⟩ := by
    dsimp only [candidateSquare]
    apply congrArg₂ Square.mk <;> apply Fin.ext <;> dsimp only <;> omega
  have hpromo : (7 * (64 * (8 * sf.val + sr.val) + (8 * df.val + dr.val)) +
      promotionWord promotion) % 7 = promotionWord promotion := by omega
  have hpromotion : candidatePromotion
      (7 * (64 * (8 * sf.val + sr.val) + (8 * df.val + dr.val)) +
        promotionWord promotion) = promotion := by
    simpa [candidatePromotion, hpromo, Nat.mod_eq_of_lt hp] using candidatePromotion_word promotion
  simp only [candidate, candidateIndex, hsquare, dsquare, hpromotion]

/-- No raw move is lost by the candidate loop. -/
theorem candidate_surjective (ply : Ply) : ∃ i, i < 28672 ∧ candidate i = ply :=
  ⟨candidateIndex ply, candidateIndex_lt ply, candidate_inverse ply⟩

theorem product_lookup {α β : Type} (xs : List α) (ys : List β) (i : Nat)
    (hy : 0 < ys.length) :
    (xs.product ys)[i]? = (xs[i / ys.length]?).bind
      (fun x ↦ (ys[i % ys.length]?).map (fun y ↦ (x, y))) := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    change ((ys.map (fun y ↦ (x, y))) ++ xs.product ys)[i]? = _
    by_cases hi : i < ys.length
    · simp [List.getElem?_append_left, hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · have hge : ys.length ≤ i := by omega
      have hd : i / ys.length = (i - ys.length) / ys.length + 1 :=
        Nat.div_eq_sub_div hy hge
      have hm : i % ys.length = (i - ys.length) % ys.length := Nat.mod_eq_sub_mod hge
      simp [List.getElem?_append_right, hge, hd, hm, ih]

@[simp] theorem candidateSquare_mod64 (i : Nat) : candidateSquare (i % 64) = candidateSquare i := by
  unfold candidateSquare
  apply congrArg₂ Square.mk <;> apply Fin.ext <;> dsimp only <;> omega

theorem squares_lookup (i : Nat) (hi : i < 64) :
    Exec.squares[i]? = some (candidateSquare i) := by
  have hd : i / 8 < 8 := by omega
  have hm : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have lookup (j : Nat) (hj : j < 8) :
      (List.finRange 8)[j]? = some (⟨j, hj⟩ : Fin 8) := by
    rw [List.getElem?_eq_getElem (by simpa using hj)]
    simp
  unfold Exec.squares
  rw [List.getElem?_map, product_lookup _ _ _ (by simp)]
  rw [show (List.finRange 8).length = 8 by simp, lookup _ hd, lookup _ hm]
  simp [candidateSquare, Nat.mod_eq_of_lt hd]

theorem promotions_lookup (i : Nat) (hi : i < 7) :
    Exec.promotions[i]? = some (candidatePromotion i) := by
  interval_cases i <;> rfl

theorem candidates_lookup (i : Nat) (hi : i < 28672) :
    Exec.candidates[i]? = some (candidate i) := by
  have product_length {α β : Type} (xs : List α) (ys : List β) :
      (xs.product ys).length = xs.length * ys.length := List.length_product xs ys
  have hs : Exec.squares.length = 64 := by simp [Exec.squares, product_length]
  have hp : Exec.promotions.length = 7 := rfl
  unfold Exec.candidates
  rw [List.getElem?_map, product_lookup _ _ _ (by decide)]
  simp only [hp]
  rw [product_lookup _ _ _ (by omega)]
  simp only [hs]
  rw [squares_lookup _ (by omega), squares_lookup _ (by omega),
    promotions_lookup _ (Nat.mod_lt _ (by decide))]
  simp [candidate, candidatePromotion, Nat.div_div_eq_div_mul]

/-- This is exact list order, not merely membership or permutation. -/
theorem candidate_order : Exec.candidates = (List.range 28672).map candidate := by
  apply List.ext_getElem
  · simp [Exec.candidates_length]
  · intro i hi hi'
    have h := candidates_lookup i (by simpa [Exec.candidates_length] using hi)
    simpa [List.getElem?_eq_getElem hi] using h

/-- Rank-major square word for one file-then-rank grouping counter. -/
def squareExpression (group : Expr) : Expr :=
  .add (.mul (.literal 8) (.mod group (.literal 8)))
    (.mod (.div group (.literal 8)) (.literal 8))

def candidateExpressions (i : Expr) : List Expr :=
  [squareExpression (.div i (.literal 448)),
    squareExpression (.div i (.literal 7)), .mod i (.literal 7)]

/-- Actual code for all three words of the move specified by the first input word. -/
def candidateCode : Code := NatCode.tuple ((candidateExpressions (.input 0)).map Scalar.compile)

theorem candidateCode_eval (n : Nat) (v : List Nat) :
    candidateCode.eval (n :: v) = pure (plyWords (candidate n)) := by
  rw [candidateCode, Updates.compile_tuple_eval]
  simp [candidateExpressions, squareExpression, Scalar.eval, plyWords, candidate,
    candidateSquare, index, promotionWord_candidate, Nat.add_comm]

/-- Copy a fixed interval of input registers before a suffix procedure's result. -/
def prefixFrom (start : Nat) : Nat → Code → Code
  | 0, suffix => suffix
  | n + 1, suffix => .cons (NatCode.nth start) (prefixFrom (start + 1) n suffix)

theorem prefixFrom_eval (start count : Nat) (suffix : Code) (v out : List Nat)
    (h : suffix.eval v = pure out) :
    (prefixFrom start count suffix).eval v =
      pure ((List.range count).map (fun i ↦ v[start + i]?.getD 0) ++ out) := by
  induction count generalizing start with
  | zero => simpa [prefixFrom] using h
  | succ count ih =>
    simp [prefixFrom, ih, List.range_succ_eq_map, List.map_map, Bind.bind,
      Function.comp_def, Nat.add_comm, Nat.add_left_comm]

theorem readBack (v : List Nat) :
    (List.range v.length).map (fun i ↦ v[i]?.getD 0) = v := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [hi']

/-- Build the exact 74-word concrete-callee context from `candidateIndex :: positionWords`. -/
def candidateContext : Code := prefixFrom 1 71 candidateCode

theorem candidateContext_eval (n : Nat) (position : Exec.Position) :
    candidateContext.eval (n :: Data.encodePosition position) =
      pure (Data.encodePosition position ++ plyWords (candidate n)) := by
  have h := prefixFrom_eval 1 71 candidateCode (n :: Data.encodePosition position)
    (plyWords (candidate n)) (candidateCode_eval n _)
  have hr := readBack (Data.encodePosition position)
  simpa [candidateContext, Data.encodePosition_length, Nat.add_comm] using
    h.trans (congrArg pure (congrArg (· ++ plyWords (candidate n)) hr))

/-- Callees are concrete code syntax and exact raw-position refinements. -/
structure Callees where
  legal : Code
  update : Code
  check : Code
  legal_refines : ∀ position ply,
    legal.eval (Data.encodePosition position ++ plyWords ply) =
      pure [truth (IsLegalPly (Exec.decode position) ply)]
  update_refines : ∀ position ply,
    update.eval (Data.encodePosition position ++ plyWords ply) =
      pure (Data.encodePosition (Exec.applyPly position ply))
  check_refines : ∀ position,
    check.eval (Data.encodePosition position) =
      pure [truth (InCheck (Exec.decode position).board position.turn)]

/-- Primitive recursion at one fixed environment, suitable for modular partial callees. -/
theorem prec_eval_at (f g : Code) (z : Nat) (G : Nat → Nat → Nat) (v : List Nat)
    (hf : f.eval v = pure [z])
    (hg : ∀ a b, g.eval (a :: b :: v) = pure [G a b]) (n : Nat) :
    (Code.prec f g).eval (n :: v) = pure [Nat.rec z G n] := by
  cases n with
  | zero => simp [Code.prec, hf, Bind.bind]
  | succ n =>
    suffices ∀ a b, a + b = n →
        ((n + 1) :: 0 :: G n (Nat.rec z G n) :: v : List Nat) ∈
          PFun.fix
            (fun w : List Nat ↦ Part.bind (g.eval (w.headI :: w.tail.tail))
              (fun x ↦ Part.some (if w.tail.headI = 0
                then Sum.inl (w.headI.succ :: w.tail.headI.pred :: x.headI :: w.tail.tail.tail)
                else Sum.inr (w.headI.succ :: w.tail.headI.pred :: x.headI :: w.tail.tail.tail))))
            (a :: b :: Nat.rec z G a :: v) by
      have h := Part.eq_some_iff.mpr (this 0 n (Nat.zero_add n))
      simp [Code.prec, hf, Part.bind_assoc, Bind.bind]
      simp_all
    intro a b e
    induction b generalizing a with
    | zero =>
      refine PFun.mem_fix_iff.2 (Or.inl <| Part.eq_some_iff.1 ?_)
      simp only [hg, ← e, Part.bind_some, List.tail_cons, pure]
      rfl
    | succ b ih =>
      refine PFun.mem_fix_iff.2 (Or.inr ⟨_, ?_, ih (a + 1) (by omega)⟩)
      simp only [hg, Part.bind_some, List.tail_cons, pure]
      exact Part.mem_some_iff.2 rfl

/-- A concrete bounded existential scan; the supplied procedure takes `index :: environment`. -/
def anyCode (count : Code) (predicate : Code) : Code :=
  .comp (Code.prec .zero
    (NatCode.ifZero (NatCode.nth 1)
      (.comp predicate (.cons .head (NatCode.drop 2))) ListCode.one))
    (.cons count .id)

theorem bounded_exists_succ (P : Nat → Prop) (n : Nat) :
    (∃ i, i < n + 1 ∧ P i) ↔ (∃ i, i < n ∧ P i) ∨ P n := by
  constructor
  · rintro ⟨i, hi, hp⟩
    by_cases e : i = n
    · exact Or.inr (e ▸ hp)
    · exact Or.inl ⟨i, by omega, hp⟩
  · rintro (⟨i, hi, hp⟩ | hp)
    · exact ⟨i, by omega, hp⟩
    · exact ⟨n, by omega, hp⟩

theorem anyCode_eval (count predicate : Code) (n : Nat) (v : List Nat)
    (P : Nat → Prop) [DecidablePred P]
    (hc : count.eval v = pure [n])
    (hp : ∀ i, predicate.eval (i :: v) = pure [truth (P i)]) :
    (anyCode count predicate).eval v = pure [truth (∃ i, i < n ∧ P i)] := by
  let G := fun i a ↦ if a = 0 then truth (P i) else 1
  have hg : ∀ i a, (NatCode.ifZero (NatCode.nth 1)
      (.comp predicate (.cons .head (NatCode.drop 2))) ListCode.one).eval
        (i :: a :: v) = pure [G i a] := by
    intro i a
    rw [NatCode.ifZero_eval _ _ _ _ [a] (by simp)]
    by_cases ha : a = 0 <;> simp [ha, G, hp, Bind.bind]
  have hrec : ∀ k, Nat.rec 0 G k = truth (∃ i, i < k ∧ P i) := by
    intro k
    induction k with
    | zero => simp [truth]
    | succ k ih =>
      change (if Nat.rec 0 G k = 0 then truth (P k) else 1) = _
      rw [ih]
      have he := bounded_exists_succ P k
      rw [Geometry.truth_congr he]
      by_cases h : ∃ i, i < k ∧ P i <;> by_cases hk : P k <;>
        simp [truth, h, hk]
  simpa [anyCode, hc, Bind.bind, pure, hrec] using prec_eval_at .zero _ 0 G v (by simp) hg n

/-- The raw en-passant test is reused from the independently checked update formulas. -/
def enPassantCaptureCode : Code :=
  Scalar.compile (Geometry.and (Geometry.not (.eq Updates.sourceCell (.literal 0)))
    Updates.enPassant)

theorem enPassantCaptureCode_eval (position : Exec.Position) (ply : Ply) :
    enPassantCaptureCode.eval (Data.encodePosition position ++ plyWords ply) =
      pure [truth (∃ piece, (Exec.decode position).board ply.src = some piece ∧
        IsEnPassant (Exec.decode position) piece ply)] := by
  simpa only [enPassantCaptureCode, Scalar.compile_eval, Updates.context, ← plyWords_eq] using
    congrArg (fun n ↦ (pure [n] : Part (List Nat)))
      (Updates.eval_enPassantCapture position ply)

/-- Check legality before the full raw en-passant predicate, retaining all promotions. -/
def legalEnPassantCode (callees : Callees) : Code :=
  NatCode.ifZero callees.legal .zero enPassantCaptureCode

theorem legalEnPassantCode_eval (callees : Callees) (position : Exec.Position) (ply : Ply) :
    (legalEnPassantCode callees).eval (Data.encodePosition position ++ plyWords ply) =
      pure [truth (IsLegalPly (Exec.decode position) ply ∧ ∃ piece,
        (Exec.decode position).board ply.src = some piece ∧
        IsEnPassant (Exec.decode position) piece ply)] := by
  rw [legalEnPassantCode, NatCode.ifZero_eval _ _ _ _ _ (callees.legal_refines position ply)]
  by_cases h : IsLegalPly (Exec.decode position) ply <;>
    simp [truth, h, enPassantCaptureCode_eval]

/-- Exhaust all 28,672 raw requests with a fixed-size runtime loop. -/
def hasLegalEnPassantCode (callees : Callees) : Code :=
  anyCode (NatCode.literal 28672) (.comp (legalEnPassantCode callees) candidateContext)

set_option maxRecDepth 10000 in
-- Matching the explicit binary-literal scan syntax requires deeper definitional comparison.
theorem hasLegalEnPassantCode_eval (callees : Callees) (position : Exec.Position) :
    (hasLegalEnPassantCode callees).eval (Data.encodePosition position) =
      pure [truth (History.HasLegalEnPassant (Exec.decode position))] := by
  have h := anyCode_eval (NatCode.literal 28672)
    (.comp (legalEnPassantCode callees) candidateContext) 28672 (Data.encodePosition position)
    (fun i ↦ IsLegalPly (Exec.decode position) (candidate i) ∧ ∃ piece,
      (Exec.decode position).board (candidate i).src = some piece ∧
      IsEnPassant (Exec.decode position) piece (candidate i)) (by simp)
    (by intro i; simp [candidateContext_eval, legalEnPassantCode_eval, Bind.bind])
  have he : (∃ i, i < 28672 ∧ IsLegalPly (Exec.decode position) (candidate i) ∧ ∃ piece,
      (Exec.decode position).board (candidate i).src = some piece ∧
        IsEnPassant (Exec.decode position) piece (candidate i)) ↔
      History.HasLegalEnPassant (Exec.decode position) := by
    constructor
    · rintro ⟨i, _, h⟩
      exact ⟨candidate i, h⟩
    · rintro ⟨ply, h⟩
      exact ⟨candidateIndex ply, candidateIndex_lt ply, by simpa only [candidate_inverse] using h⟩
  unfold hasLegalEnPassantCode
  exact h.trans (congrArg (fun n ↦ (pure [n] : Part (List Nat))) (Geometry.truth_congr he))

/-- Only en-passant metadata and the clock are erased by this comparison key. -/
def normalise (position : Exec.Position) : Exec.Position :=
  {position with enPassantTarget := none, halfmoveClock := 0}

theorem normalise_word (position : Exec.Position) (i : Nat) :
    (Data.encodePosition (normalise position))[i]?.getD 0 =
      if i = 5 ∨ i = 6 then 0 else (Data.encodePosition position)[i]?.getD 0 := by
  by_cases hi : i < 7
  · interval_cases i <;> rfl
  · have hmask : ¬(i = 5 ∨ i = 6) := by omega
    simp only [hmask, ↓reduceIte, Data.encodePosition, normalise]
    rw [List.getElem?_append_right (by simp; omega),
      List.getElem?_append_right (by simp; omega)]
    rfl

theorem normalise_eq_iff (first second : Exec.Position) :
    normalise first = normalise second ↔
      ∀ i, i < 71 → (i = 5 ∨ i = 6) ∨
        (Data.encodePosition first)[i]?.getD 0 = (Data.encodePosition second)[i]?.getD 0 := by
  constructor
  · intro equal i _
    by_cases mask : i = 5 ∨ i = 6
    · exact Or.inl mask
    · right
      have h := congrArg (fun p ↦ (Data.encodePosition p)[i]?.getD 0) equal
      simpa only [normalise_word, mask, ↓reduceIte] using h
  · intro words
    apply Data.encodePosition_injective
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      have hib : i < 71 := by simpa using hi
      have equal : (Data.encodePosition (normalise first))[i]?.getD 0 =
          (Data.encodePosition (normalise second))[i]?.getD 0 := by
        rw [normalise_word, normalise_word]
        by_cases mask : i = 5 ∨ i = 6
        · simp [mask]
        · simpa only [mask, ↓reduceIte] using (words i hib).resolve_left mask
      simpa only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi',
        Option.getD_some] using equal

theorem normalise_condition (first second : Exec.Position) :
    normalise first = normalise second ↔
      (∀ square, (Exec.decode first).board square = (Exec.decode second).board square) ∧
      first.turn = second.turn ∧ first.castlingRights = second.castlingRights := by
  constructor
  · intro equal
    have hb := congrArg Exec.Position.board equal
    have ht := congrArg Exec.Position.turn equal
    have hr := congrArg Exec.Position.castlingRights equal
    exact ⟨fun square ↦ congrArg (fun board ↦ Exec.decodeBoard board square) hb, ht, hr⟩
  · rintro ⟨board, turn, rights⟩
    have hb : first.board = second.board := by
      have h := congrArg Exec.encodeBoard (funext board)
      simpa only [Exec.decode, Exec.encode_decodeBoard] using h
    change Exec.Position.mk first.board first.turn first.castlingRights none 0 =
      Exec.Position.mk second.board second.turn second.castlingRights none 0
    rw [hb, turn, rights]

/-- Compare every non-erased field; zero-valued board cells are ordinary data. -/
def sameCoreExpr : Expr := Geometry.all 71
  (.ifZero (.eq (.input 0) (.literal 5))
    (.ifZero (.eq (.input 0) (.literal 6))
      (.eq (.lookup (.add (.input 0) (.literal 2)))
        (.lookup (.add (.input 0) (.literal 73)))) (.literal 1)) (.literal 1))

theorem sameCoreExpr_eval (first second : Exec.Position) :
    Scalar.eval sameCoreExpr (Data.encodePosition first ++ Data.encodePosition second) =
      truth (normalise first = normalise second) := by
  have h := Geometry.eval_all 71
    (.ifZero (.eq (.input 0) (.literal 5))
      (.ifZero (.eq (.input 0) (.literal 6))
        (.eq (.lookup (.add (.input 0) (.literal 2)))
          (.lookup (.add (.input 0) (.literal 73)))) (.literal 1)) (.literal 1))
    (Data.encodePosition first ++ Data.encodePosition second)
    (fun i ↦ (i = 5 ∨ i = 6) ∨ (Data.encodePosition first)[i]?.getD 0 =
      (Data.encodePosition second)[i]?.getD 0) (by
      intro i hi a
      have hf : (Data.encodePosition first ++ Data.encodePosition second)[i]?.getD 0 =
          (Data.encodePosition first)[i]?.getD 0 := by
        rw [List.getElem?_append_left (by simpa using hi)]
      have hs : (Data.encodePosition first ++ Data.encodePosition second)[i + 71]?.getD 0 =
          (Data.encodePosition second)[i]?.getD 0 := by
        rw [List.getElem?_append_right (by simp)]
        simp only [Data.encodePosition_length, Nat.add_sub_cancel_right]
      by_cases h5 : i = 5 <;> by_cases h6 : i = 6 <;>
        simp [Scalar.eval, hf, hs, truth, h5, h6])
  exact h.trans (Geometry.truth_congr (normalise_eq_iff first second).symm)

def sameCoreCode : Code := Scalar.compile sameCoreExpr

theorem sameCoreCode_eval (first second : Exec.Position) :
    sameCoreCode.eval (Data.encodePosition first ++ Data.encodePosition second) =
      pure [truth (normalise first = normalise second)] := by
  simp [sameCoreCode, Scalar.compile_eval, sameCoreExpr_eval]

/-- Select the first complete position, discarding all remaining data. -/
def firstPositionCode : Code := .comp ListCode.take (.cons (NatCode.literal 71) .id)

theorem firstPositionCode_eval (position : Exec.Position) (suffix : List Nat) :
    firstPositionCode.eval (Data.encodePosition position ++ suffix) =
      pure (Data.encodePosition position) := by
  have h := ListCode.take_eval (Data.encodePosition position) suffix
  simpa [firstPositionCode, Data.encodePosition_length, Bind.bind] using h

def equalTargetCode : Code := Scalar.compile (.eq (.input 5) (.input 76))

theorem equalTargetCode_eval (first second : Exec.Position) :
    equalTargetCode.eval (Data.encodePosition first ++ Data.encodePosition second) =
      pure [truth (first.enPassantTarget = second.enPassantTarget)] := by
  have hf : (Data.encodePosition first ++ Data.encodePosition second)[5]?.getD 0 =
      Data.encodeTarget first.enPassantTarget := by
    rw [List.getElem?_append_left (by simp)]
    rfl
  have hs : (Data.encodePosition first ++ Data.encodePosition second)[76]?.getD 0 =
      Data.encodeTarget second.enPassantTarget := by
    rw [List.getElem?_append_right (by simp)]
    rfl
  have hinj : Function.Injective Data.encodeTarget := by
    intro a b h
    have decoded := congrArg Data.targetOfNat h
    simpa only [Data.targetOfNat_encodeTarget] using decoded
  simp only [equalTargetCode, Scalar.compile_eval, Scalar.eval]
  change pure [truth ((Data.encodePosition first ++ Data.encodePosition second)[5]?.getD 0 =
    (Data.encodePosition first ++ Data.encodePosition second)[76]?.getD 0)] = _
  apply congrArg (fun n ↦ (pure [n] : Part (List Nat)))
  apply Geometry.truth_congr
  rw [hf, hs]
  exact hinj.eq_iff

/-- The exact frozen repetition relation, with full legal en-passant capture scans. -/
def samePositionCode (callees : Callees) : Code :=
  NatCode.ifZero sameCoreCode .zero
    (NatCode.ifZero equalTargetCode
      (NatCode.ifZero (.comp (hasLegalEnPassantCode callees) firstPositionCode)
        (NatCode.ifZero (.comp (hasLegalEnPassantCode callees) (NatCode.drop 71))
          ListCode.one .zero) .zero)
      ListCode.one)

set_option maxRecDepth 10000 in
-- These nested concrete callee compositions contain the binary-literal scan syntax.
theorem samePositionCode_eval (callees : Callees) (first second : Exec.Position) :
    (samePositionCode callees).eval (Data.encodePosition first ++ Data.encodePosition second) =
      pure [truth (SamePosition (Exec.decode first) (Exec.decode second))] := by
  have hform : SamePosition (Exec.decode first) (Exec.decode second) ↔
      normalise first = normalise second ∧
      (first.enPassantTarget = second.enPassantTarget ∨
        (¬History.HasLegalEnPassant (Exec.decode first) ∧
          ¬History.HasLegalEnPassant (Exec.decode second))) := by
    rw [normalise_condition]
    simpa only [Exec.decode, and_assoc] using
      History.samePosition_iff (Exec.decode first) (Exec.decode second)
  rw [Geometry.truth_congr hform]
  have hd : (Data.encodePosition first ++ Data.encodePosition second).drop 71 =
      Data.encodePosition second := by
    simpa only [Data.encodePosition_length] using
      (show (Data.encodePosition first ++ Data.encodePosition second).drop
        (Data.encodePosition first).length = Data.encodePosition second from List.drop_left)
  by_cases hc : normalise first = normalise second <;>
    by_cases he : first.enPassantTarget = second.enPassantTarget <;>
    by_cases hf : History.HasLegalEnPassant (Exec.decode first) <;>
    by_cases hs : History.HasLegalEnPassant (Exec.decode second) <;>
    simp [samePositionCode, NatCode.ifZero, sameCoreCode_eval, equalTargetCode_eval,
      firstPositionCode_eval, hasLegalEnPassantCode_eval, Bind.bind, hd, truth, hc, he, hf, hs]

theorem prefixFrom_exact (front segment tail : List Nat) (suffix : Code) (out : List Nat)
    (h : suffix.eval (front ++ (segment ++ tail)) = pure out) :
    (prefixFrom front.length segment.length suffix).eval (front ++ (segment ++ tail)) =
      pure (segment ++ out) := by
  have reads : (List.range segment.length).map
      (fun i ↦ (front ++ (segment ++ tail))[front.length + i]?.getD 0) = segment := by
    calc
      _ = (List.range segment.length).map (fun i ↦ segment[i]?.getD 0) := by
        apply List.map_congr_left
        intro i hi
        have hib : i < segment.length := List.mem_range.mp hi
        rw [List.getElem?_append_right (by omega)]
        simp only [Nat.add_sub_cancel_left]
        rw [List.getElem?_append_left hib]
      _ = segment := readBack segment
  simpa only [reads] using prefixFrom_eval front.length segment.length suffix _ out h

/-- A list-fold count with precisely the frozen repetition predicate. -/
def countMatches (target : Chess.Position) : List Chess.Position → Nat
  | [] => 0
  | position :: positions => truth (SamePosition position target) + countMatches target positions

theorem matches_card (target : Chess.Position) (positions : List Chess.Position) :
    countMatches target positions =
      Fintype.card {i : Fin positions.length // SamePosition (positions.get i) target} := by
  induction positions with
  | nil => simp [countMatches]
  | cons position positions ih =>
    simp only [countMatches, Fintype.card_subtype, Fin.card_filter_univ_succ',
      List.get_eq_getElem, List.length_cons, List.getElem_cons_zero, Fin.val_zero,
      Fin.val_succ, List.getElem_cons_succ, ih, truth]

/-- Extract two full positions from the counting state in source/target order. -/
def countContext : Code :=
  prefixFrom 73 71 (.comp firstPositionCode (NatCode.drop 2))

theorem countContext_eval (n acc : Nat) (target position : Exec.Position) (rest : List Nat) :
    countContext.eval (n :: acc :: (Data.encodePosition target ++
      (Data.encodePosition position ++ rest))) =
      pure (Data.encodePosition position ++ Data.encodePosition target) := by
  have h := prefixFrom_exact ([n, acc] ++ Data.encodePosition target)
    (Data.encodePosition position) rest (.comp firstPositionCode (NatCode.drop 2))
    (Data.encodePosition target) (by
      simp [Bind.bind, firstPositionCode_eval])
  simpa [countContext, Data.encodePosition_length, List.append_assoc] using h

/-- Keep the complete target position and discard exactly one counted source block. -/
def countRemainder : Code := prefixFrom 2 71 (NatCode.drop 144)

theorem countRemainder_eval (n acc : Nat) (target position : Exec.Position) (rest : List Nat) :
    countRemainder.eval (n :: acc :: (Data.encodePosition target ++
      (Data.encodePosition position ++ rest))) = pure (Data.encodePosition target ++ rest) := by
  have h := prefixFrom_exact [n, acc] (Data.encodePosition target)
    (Data.encodePosition position ++ rest) (NatCode.drop 144) rest (by
      simp only [NatCode.drop_eval]
      apply congrArg (fun w ↦ (pure w : Part (List Nat)))
      have hlen : ([n, acc] ++ Data.encodePosition target ++
          Data.encodePosition position).length = 144 := by simp
      have hdrop :=
        (show
          (([n, acc] ++ Data.encodePosition target ++ Data.encodePosition position) ++ rest).drop
          ([n, acc] ++ Data.encodePosition target ++ Data.encodePosition position).length = rest
          from List.drop_left)
      simp only [hlen] at hdrop
      simpa only [List.append_assoc] using hdrop)
  simpa [countRemainder] using h

def countBody (callees : Callees) : Code :=
  .case (.cons .zero .head)
    (.cons ListCode.one (.cons .head
      (.cons (.comp NatCode.add (NatCode.tuple
        [NatCode.nth 1, .comp (samePositionCode callees) countContext])) countRemainder)))

theorem countBody_zero (callees : Callees) (acc : Nat) (rest : List Nat) :
    (countBody callees).eval (0 :: acc :: rest) = pure [0, acc] := by
  simp [countBody, Bind.bind]

theorem countBody_succ (callees : Callees) (n acc : Nat)
    (target position : Exec.Position) (rest : List Nat) :
    (countBody callees).eval ((n + 1) :: acc :: (Data.encodePosition target ++
      (Data.encodePosition position ++ rest))) =
      pure (1 :: n :: (acc + truth (SamePosition (Exec.decode position) (Exec.decode target))) ::
        (Data.encodePosition target ++ rest)) := by
  simp [countBody, NatCode.tuple, Bind.bind, countContext_eval,
    samePositionCode_eval, countRemainder_eval]

def countLoop (callees : Callees) : Code := .fix (countBody callees)

theorem countLoop_eval (callees : Callees) (target : Exec.Position)
    (positions : List Exec.Position) (acc : Nat) :
    (countLoop callees).eval (positions.length :: acc ::
      (Data.encodePosition target ++ Data.encodePositions positions)) =
      pure [acc + countMatches (Exec.decode target) (positions.map Exec.decode)] := by
  induction positions generalizing acc with
  | nil => simpa [countLoop, countMatches, Data.encodePositions] using
      ListCode.fix_stop (countBody callees) _ _ (countBody_zero callees acc _)
  | cons position positions ih =>
    rw [List.length_cons, Data.encodePositions, countLoop,
      ListCode.fix_next _ _ _ (countBody_succ callees positions.length acc target position _)]
    simpa [countLoop, List.map_cons, countMatches, Nat.add_assoc] using
      ih (acc + truth (SamePosition (Exec.decode position) (Exec.decode target)))

/-- Count all current and historical occurrences; duplicates and order are retained. -/
def occurrencesCode (callees : Callees) : Code :=
  .comp (countLoop callees) (.cons (.comp .succ .head)
    (.cons .zero (prefixFrom 1 71 .tail)))

theorem occurrencesCode_eval (callees : Callees) (game : Adjudication.Game) :
    (occurrencesCode callees).eval (Data.encodeGame game) = pure [game.occurrences] := by
  have hp := prefixFrom_exact [game.previous.length] (Data.encodePosition game.current)
    (Data.encodePositions game.previous) .tail
    (Data.encodePosition game.current ++ Data.encodePositions game.previous) (by simp)
  have hp' : (prefixFrom 1 71 .tail).eval (game.previous.length ::
      (Data.encodePosition game.current ++ Data.encodePositions game.previous)) =
      pure (Data.encodePosition game.current ++ (Data.encodePosition game.current ++
        Data.encodePositions game.previous)) := by
    simpa [Data.encodePosition_length] using hp
  have h := countLoop_eval callees game.current (game.current :: game.previous) 0
  simpa [occurrencesCode, Data.encodeGame, hp',
    Bind.bind, Data.encodePositions, matches_card, Adjudication.Game.occurrences,
    Adjudication.occurrences, Adjudication.decodeGame, Chess.Game.positions] using h

/-- Reverse a scalar stack while retaining all unencoded trailing words. -/
def reverseStackCode : Code :=
  .comp (ListCode.foldStack ListCode.packCode) (.cons .head (.cons .zero .tail))

theorem reverseStackCode_eval (xs suffix : List Nat) :
    reverseStackCode.eval (ListCode.stack xs :: suffix) =
      pure (ListCode.stack xs.reverse :: suffix) := by
  have h := ListCode.foldStack_eval ListCode.packCode (fun x acc _ ↦ ListCode.pack x acc)
    (fun x acc v ↦ ListCode.packCode_eval x acc v) xs 0 suffix
  have hs : xs.foldl (fun a x ↦ ListCode.pack x a) 0 = ListCode.stack xs.reverse := by
    simpa [ListCode.stack] using ListCode.foldl_pack xs []
  simpa [reverseStackCode, Bind.bind, hs] using h

/-- Decode the first scalar stack into its original list order. -/
def decodeStackCode : Code := .comp ListCode.restore (.comp reverseStackCode .head)

theorem decodeStackCode_eval (xs suffix : List Nat) :
    decodeStackCode.eval (ListCode.stack xs :: suffix) = pure xs := by
  simp [decodeStackCode, Bind.bind, reverseStackCode_eval, ListCode.restore_eval]

/-- Encode an exactly length-framed list in original order. -/
def encodeFramedCode : Code := .comp .head (.comp reverseStackCode ListCode.split)

theorem encodeFramedCode_eval (xs : List Nat) :
    encodeFramedCode.eval (xs.length :: xs) = pure [ListCode.stack xs] := by
  have h := ListCode.split_eval xs []
  simp only [List.append_nil] at h
  simp [encodeFramedCode, Bind.bind, h, reverseStackCode_eval]

def gameLengthExpr : Expr :=
  .add (.literal 1) (.mul (.literal 71) (.add (.input 0) (.literal 1)))

/-- Full histories include their own exact length frame; no boundary oracle is used. -/
def encodeGameCode : Code :=
  .comp encodeFramedCode (.cons (Scalar.compile gameLengthExpr) .id)

theorem encodeGameCode_eval (game : Adjudication.Game) :
    encodeGameCode.eval (Data.encodeGame game) = pure [ListCode.stack (Data.encodeGame game)] := by
  have he : Scalar.eval gameLengthExpr (Data.encodeGame game) =
      (Data.encodeGame game).length := by
    rw [Data.encodeGame_length]
    rfl
  simpa only [encodeGameCode, Code.comp_eval, Code.cons_eval, Scalar.compile_eval, he,
    Code.id_eval, Bind.bind, Part.pure_eq_some, Part.bind_some, List.headI_cons] using
      encodeFramedCode_eval (Data.encodeGame game)

/-- Candidate context from `candidateIndex :: encodedGame`. -/
def candidateGameContext : Code := prefixFrom 2 71 candidateCode

theorem candidateGameContext_eval (n : Nat) (game : Adjudication.Game) :
    candidateGameContext.eval (n :: Data.encodeGame game) =
      pure (Data.encodePosition game.current ++ plyWords (candidate n)) := by
  have h := prefixFrom_exact [n, game.previous.length] (Data.encodePosition game.current)
    (Data.encodePositions game.previous) candidateCode (plyWords (candidate n))
    (candidateCode_eval n _)
  simpa [candidateGameContext, Data.encodePosition_length, Data.encodeGame] using h

/-- Pack the reversed updated position so it can be restored before the unchanged full history. -/
def updatedReverseCode (callees : Callees) : Code :=
  .comp .head (.comp ListCode.split
    (.cons (NatCode.literal 71) (.comp callees.update candidateGameContext)))

theorem updatedReverseCode_eval (callees : Callees) (n : Nat) (game : Adjudication.Game) :
    (updatedReverseCode callees).eval (n :: Data.encodeGame game) =
      pure [ListCode.stack
        (Data.encodePosition (Exec.applyPly game.current (candidate n))).reverse] := by
  have h := ListCode.split_eval (Data.encodePosition (Exec.applyPly game.current (candidate n))) []
  simp only [List.append_nil, Data.encodePosition_length] at h
  simp [updatedReverseCode, candidateGameContext_eval, callees.update_refines, h, Bind.bind]

/-- Extend full history by a raw candidate update; legality is checked by the caller. -/
def playFlatCode (callees : Callees) : Code :=
  .cons (.comp .succ (NatCode.nth 1))
    (.comp ListCode.restore (.cons (updatedReverseCode callees) (NatCode.drop 2)))

theorem playFlatCode_eval (callees : Callees) (n : Nat) (game : Adjudication.Game) :
    (playFlatCode callees).eval (n :: Data.encodeGame game) =
      pure (Data.encodeGame (game.play (candidate n))) := by
  have hc : (Code.comp .succ (NatCode.nth 1)).eval (n :: Data.encodeGame game) =
      pure [game.previous.length + 1] := by simp [Data.encodeGame, Bind.bind]
  have hd : (NatCode.drop 2).eval (n :: Data.encodeGame game) =
      pure (Data.encodePosition game.current ++ Data.encodePositions game.previous) := by
    simp [Data.encodeGame]
  simp only [playFlatCode, Code.cons_eval, Code.comp_eval, hc, updatedReverseCode_eval, hd,
    Bind.bind, Part.pure_eq_some, Part.bind_some, List.headI_cons, ListCode.restore_eval,
    List.reverse_reverse]
  rfl

def gameWord (game : Adjudication.Game) : Nat := ListCode.stack (Data.encodeGame game)

def plyWord (ply : Ply) : Nat := candidateIndex ply + 1

/-- Packed interface consumed by the evaluator control machine. -/
def playCode (callees : Callees) : Code := .comp encodeGameCode
  (.comp (playFlatCode callees)
    (.cons (.comp .pred (NatCode.nth 1)) (.comp decodeStackCode .head)))

theorem playCode_eval (callees : Callees) (game : Adjudication.Game) (ply : Ply) :
    (playCode callees).eval [gameWord game, plyWord ply] = pure [gameWord (game.play ply)] := by
  simp [playCode, gameWord, plyWord, decodeStackCode_eval, Bind.bind, playFlatCode_eval,
    encodeGameCode_eval]

def turnFlatCode : Code := NatCode.nth 1

theorem turnFlatCode_eval (game : Adjudication.Game) :
    turnFlatCode.eval (Data.encodeGame game) = pure [Data.encodeColor game.current.turn] := by
  simp [turnFlatCode, Data.encodeGame, Data.encodePosition]

def turnCode : Code := .comp turnFlatCode decodeStackCode

theorem turnCode_eval (game : Adjudication.Game) :
    turnCode.eval [gameWord game] = pure [Data.encodeColor game.current.turn] := by
  simp [turnCode, gameWord, decodeStackCode_eval, turnFlatCode_eval, Bind.bind]

def repeatedCode (callees : Callees) (threshold : Nat) : Code :=
  .comp NatCode.le (NatCode.tuple [NatCode.literal threshold, occurrencesCode callees])

theorem repeatedCode_eval (callees : Callees) (threshold : Nat) (game : Adjudication.Game) :
    (repeatedCode callees threshold).eval (Data.encodeGame game) =
      pure [truth ((Adjudication.decodeGame game).RepeatedAtLeast threshold)] := by
  have h := Adjudication.repeated_iff_occurrences (Adjudication.decodeGame game) threshold
  simp only [repeatedCode, Code.comp_eval, NatCode.tuple, Code.cons_eval,
    NatCode.literal_eval, occurrencesCode_eval, Code.nil_eval]
  simp [Bind.bind, truth, Adjudication.Game.occurrences, ← h]

def hasLegalCode (callees : Callees) : Code :=
  anyCode (NatCode.literal 28672) (.comp callees.legal candidateContext)

theorem hasLegalCode_eval (callees : Callees) (position : Exec.Position) :
    (hasLegalCode callees).eval (Data.encodePosition position) =
      pure [truth (HasLegalPly (Exec.decode position))] := by
  have h := anyCode_eval (NatCode.literal 28672) (.comp callees.legal candidateContext)
    28672 (Data.encodePosition position) (fun i ↦ IsLegalPly (Exec.decode position) (candidate i))
    (by simp) (by intro i; simp [candidateContext_eval, callees.legal_refines, Bind.bind])
  have he : (∃ i, i < 28672 ∧ IsLegalPly (Exec.decode position) (candidate i)) ↔
      HasLegalPly (Exec.decode position) := by
    constructor
    · rintro ⟨i, _, legal⟩
      exact ⟨candidate i, legal⟩
    · rintro ⟨ply, legal⟩
      exact ⟨candidateIndex ply, candidateIndex_lt ply, by simpa using legal⟩
  exact h.trans (congrArg (fun n ↦ (pure [n] : Part (List Nat))) (Geometry.truth_congr he))

def currentPositionCode : Code := .comp firstPositionCode .tail

theorem currentPositionCode_eval (game : Adjudication.Game) :
    currentPositionCode.eval (Data.encodeGame game) = pure (Data.encodePosition game.current) := by
  simp only [currentPositionCode, Code.comp_eval, Code.tail_eval, Data.encodeGame,
    List.tail_cons, Bind.bind, Part.pure_eq_some, Part.bind_some]
  exact firstPositionCode_eval _ _

def clockCode (threshold : Nat) : Code := Scalar.compile (.le (.literal threshold) (.input 7))

theorem clockCode_eval (threshold : Nat) (game : Adjudication.Game) :
    (clockCode threshold).eval (Data.encodeGame game) =
      pure [truth (threshold ≤ game.current.halfmoveClock)] := by
  rw [clockCode, Scalar.compile_eval]
  rfl

def automaticWord : Option Outcome → Nat
  | none => 0
  | some outcome => Program.encodeOutcome outcome + 1

/-- Mate wins have priority; only the proved value-preserving dead-position test is deferred. -/
def automaticFlatCode (callees : Callees) : Code :=
  NatCode.ifZero (.comp (hasLegalCode callees) currentPositionCode)
    (NatCode.ifZero (.comp callees.check currentPositionCode) ListCode.one
      (NatCode.ifZero turnFlatCode (NatCode.literal 3) (NatCode.literal 2)))
    (NatCode.ifZero (repeatedCode callees 5) (clockCode 150) ListCode.one)

theorem automaticFlatCode_eval (callees : Callees) (game : Adjudication.Game) :
    (automaticFlatCode callees).eval (Data.encodeGame game) =
      pure [automaticWord (WithoutDead.automaticWithoutDead game)] := by
  by_cases hl : HasLegalPly (Exec.decode game.current) <;>
    by_cases hc : InCheck (Exec.decode game.current).board game.current.turn <;>
    by_cases hr : (Adjudication.decodeGame game).RepeatedAtLeast 5 <;>
    by_cases hm : 150 ≤ game.current.halfmoveClock <;>
    cases ht : game.current.turn <;>
    simp_all [automaticFlatCode, NatCode.ifZero, currentPositionCode_eval, hasLegalCode_eval,
      callees.check_refines, turnFlatCode_eval, repeatedCode_eval, clockCode_eval, Bind.bind,
      automaticWord, WithoutDead.automaticWithoutDead, WithoutDead.DrawConditionWithoutDead,
      IsCheckmate, IsStalemate, Adjudication.decodeGame, Exec.decode, Program.encodeOutcome,
      truth, Data.encodeColor, Color.other]
  all_goals split_ifs <;> rfl

def automaticCode (callees : Callees) : Code := .comp (automaticFlatCode callees) decodeStackCode

theorem automaticCode_eval (callees : Callees) (game : Adjudication.Game) :
    (automaticCode callees).eval [gameWord game] =
      pure [automaticWord (WithoutDead.automaticWithoutDead game)] := by
  simp [automaticCode, gameWord, decodeStackCode_eval, automaticFlatCode_eval, Bind.bind]

/-- Current-position claim thresholds, without executing or requiring a claim action. -/
def CurrentClaim (game : Adjudication.Game) : Prop :=
  (Adjudication.decodeGame game).RepeatedAtLeast 3 ∨ 100 ≤ game.current.halfmoveClock

instance (game : Adjudication.Game) : Decidable (CurrentClaim game) := by
  unfold CurrentClaim
  infer_instance

theorem claimCondition_iff (game : Adjudication.Game) :
    CanClaimDraw (Adjudication.decodeGame game) ↔
      CurrentClaim game ∨ ∃ ply,
        IsLegalPly (Exec.decode game.current) ply ∧ CurrentClaim (game.play ply) := by
  have hc : (Adjudication.decodeGame game).current.halfmoveClock =
      game.current.halfmoveClock := rfl
  have hp (ply : Ply) : (game.play ply).current.halfmoveClock =
      (applyPly (Adjudication.decodeGame game).current ply).halfmoveClock := by
    have hclock := congrArg Chess.Position.halfmoveClock (Exec.decode_applyPly game.current ply)
    exact hclock
  simp only [CanClaimDraw, CanClaimThreefold, CanClaimFiftyMove, CurrentClaim,
    Adjudication.decode_play, hp, hc, and_or_left, exists_or]
  aesop

def currentClaimCode (callees : Callees) : Code :=
  NatCode.ifZero (repeatedCode callees 3) (clockCode 100) ListCode.one

theorem currentClaimCode_eval (callees : Callees) (game : Adjudication.Game) :
    (currentClaimCode callees).eval (Data.encodeGame game) = pure [truth (CurrentClaim game)] := by
  by_cases hr : (Adjudication.decodeGame game).RepeatedAtLeast 3 <;>
    by_cases hm : 100 ≤ game.current.halfmoveClock <;>
    simp [currentClaimCode, NatCode.ifZero, repeatedCode_eval, clockCode_eval,
      truth, CurrentClaim, hr, hm, Bind.bind]

/-- Intended-move claims inspect a legal raw continuation without replacing the current game. -/
def candidateClaimCode (callees : Callees) : Code :=
  NatCode.ifZero (.comp callees.legal candidateGameContext) .zero
    (.comp (currentClaimCode callees) (playFlatCode callees))

theorem candidateClaimCode_eval (callees : Callees) (i : Nat) (game : Adjudication.Game) :
    (candidateClaimCode callees).eval (i :: Data.encodeGame game) =
      pure [truth (IsLegalPly (Exec.decode game.current) (candidate i) ∧
        CurrentClaim (game.play (candidate i)))] := by
  rw [candidateClaimCode, NatCode.ifZero_eval _ _ _ _
    [truth (IsLegalPly (Exec.decode game.current) (candidate i))]
    (by simp [candidateGameContext_eval, callees.legal_refines, Bind.bind])]
  by_cases hl : IsLegalPly (Exec.decode game.current) (candidate i) <;>
    simp [truth, hl, playFlatCode_eval, currentClaimCode_eval, Bind.bind]

def intendedClaimCode (callees : Callees) : Code :=
  anyCode (NatCode.literal 28672) (candidateClaimCode callees)

theorem intendedClaimCode_eval (callees : Callees) (game : Adjudication.Game) :
    (intendedClaimCode callees).eval (Data.encodeGame game) =
      pure [truth (∃ ply, IsLegalPly (Exec.decode game.current) ply ∧
        CurrentClaim (game.play ply))] := by
  have h := anyCode_eval (NatCode.literal 28672) (candidateClaimCode callees) 28672
    (Data.encodeGame game) (fun i ↦ IsLegalPly (Exec.decode game.current) (candidate i) ∧
      CurrentClaim (game.play (candidate i))) (by simp)
    (fun i ↦ candidateClaimCode_eval callees i game)
  have he : (∃ i, i < 28672 ∧ IsLegalPly (Exec.decode game.current) (candidate i) ∧
      CurrentClaim (game.play (candidate i))) ↔
      ∃ ply, IsLegalPly (Exec.decode game.current) ply ∧ CurrentClaim (game.play ply) := by
    constructor
    · rintro ⟨i, _, h⟩
      exact ⟨candidate i, h⟩
    · rintro ⟨ply, h⟩
      exact ⟨candidateIndex ply, candidateIndex_lt ply, by simpa using h⟩
  exact h.trans (congrArg (fun n ↦ (pure [n] : Part (List Nat))) (Geometry.truth_congr he))

/-- The optional claim test preserves both current and announced-next-move claims. -/
def canClaimCode (callees : Callees) : Code :=
  NatCode.ifZero (currentClaimCode callees) (intendedClaimCode callees) ListCode.one

theorem canClaimCode_eval (callees : Callees) (game : Adjudication.Game) :
    (canClaimCode callees).eval (Data.encodeGame game) =
      pure [truth (CanClaimDraw (Adjudication.decodeGame game))] := by
  rw [Geometry.truth_congr (claimCondition_iff game)]
  by_cases hc : CurrentClaim game <;>
    by_cases hi : ∃ ply, IsLegalPly (Exec.decode game.current) ply ∧
      CurrentClaim (game.play ply) <;>
    simp [canClaimCode, NatCode.ifZero, currentClaimCode_eval, intendedClaimCode_eval,
      truth, hc, hi, Bind.bind]

theorem candidateIndex_candidate (i : Nat) (hi : i < 28672) :
    candidateIndex (candidate i) = i := by
  simp only [candidateIndex, candidate, candidateSquare, promotionWord_candidate]
  omega

def legalWords (game : Adjudication.Game) (n : Nat) : List Nat :=
  ((List.range n).filter (fun i ↦ Exec.isLegal game.current (candidate i))).map (fun i ↦ i + 1)

theorem legalWords_succ (game : Adjudication.Game) (n : Nat) :
    legalWords game (n + 1) = legalWords game n ++
      if IsLegalPly (Exec.decode game.current) (candidate n) then [n + 1] else [] := by
  by_cases h : IsLegalPly (Exec.decode game.current) (candidate n) <;>
    simp [legalWords, List.range_succ, List.filter_append, h, Exec.isLegal]

set_option maxRecDepth 10000 in
-- The exact-order rewrite matches the symbolic 28,672-element scan, without expanding its list.
theorem legalWords_eq (game : Adjudication.Game) :
    (Exec.legalPlies game.current).map plyWord = legalWords game 28672 := by
  unfold Exec.legalPlies legalWords
  rw [candidate_order, List.filter_map, List.map_map]
  apply List.map_congr_left
  intro i hi
  have hib : i < 28672 := List.mem_range.mp (List.mem_filter.mp hi).1
  simp [plyWord, candidateIndex_candidate i hib]

/-- Descending candidate inspection conses each retained action into ascending output order. -/
def actionsBody (callees : Callees) : Code :=
  let legal := .comp callees.legal
    (.comp candidateGameContext (.cons .head (NatCode.drop 2)))
  let acc := NatCode.ifZero legal (NatCode.nth 1)
    (.comp ListCode.packCode (NatCode.tuple [.comp .succ .head, NatCode.nth 1]))
  .case (.cons .zero .head) (.cons ListCode.one (.cons .head (.cons acc (NatCode.drop 2))))

theorem actionsBody_zero (callees : Callees) (acc : Nat) (v : List Nat) :
    (actionsBody callees).eval (0 :: acc :: v) = pure [0, acc] := by
  simp [actionsBody, Bind.bind]

theorem actionsBody_succ (callees : Callees) (n acc : Nat) (game : Adjudication.Game) :
    (actionsBody callees).eval ((n + 1) :: acc :: Data.encodeGame game) =
      pure (1 :: n ::
        (if IsLegalPly (Exec.decode game.current) (candidate n)
          then ListCode.pack (n + 1) acc else acc) :: Data.encodeGame game) := by
  by_cases h : IsLegalPly (Exec.decode game.current) (candidate n) <;>
    simp [actionsBody, NatCode.ifZero, candidateGameContext_eval, callees.legal_refines,
      NatCode.tuple, Bind.bind, truth, h]

def actionsLoop (callees : Callees) : Code := .fix (actionsBody callees)

theorem actionsLoop_eval (callees : Callees) (game : Adjudication.Game)
    (n : Nat) (acc : List Nat) :
    (actionsLoop callees).eval (n :: ListCode.stack acc :: Data.encodeGame game) =
      pure [ListCode.stack (legalWords game n ++ acc)] := by
  induction n generalizing acc with
  | zero =>
    simpa [actionsLoop, legalWords] using
      ListCode.fix_stop (actionsBody callees) _ _ (actionsBody_zero callees (ListCode.stack acc) _)
  | succ n ih =>
    rw [actionsLoop, ListCode.fix_next _ _ _ (actionsBody_succ callees n (ListCode.stack acc) game)]
    by_cases h : IsLegalPly (Exec.decode game.current) (candidate n)
    · simpa [actionsLoop, ListCode.stack, legalWords_succ, h, List.append_assoc] using
        ih ((n + 1) :: acc)
    · simpa [actionsLoop, legalWords_succ, h] using ih acc

def claimWords (game : Adjudication.Game) : List Nat :=
  if Adjudication.canClaimDraw game then [0] else []

def initialClaimCode (callees : Callees) : Code :=
  NatCode.ifZero (canClaimCode callees) .zero ListCode.one

theorem initialClaimCode_eval (callees : Callees) (game : Adjudication.Game) :
    (initialClaimCode callees).eval (Data.encodeGame game) =
      pure [ListCode.stack (claimWords game)] := by
  cases hc : Adjudication.canClaimDraw game <;>
    simp [initialClaimCode, NatCode.ifZero, canClaimCode_eval, claimWords, truth,
      ← Adjudication.canClaimDraw_iff, hc, Bind.bind, ListCode.stack, ListCode.pack]

def actionWord : Action → Nat
  | .claimDraw => 0
  | .play ply => plyWord ply

def actionsFlatCode (callees : Callees) : Code :=
  NatCode.ifZero (automaticFlatCode callees)
    (.comp (actionsLoop callees)
      (.cons (NatCode.literal 28672) (.cons (initialClaimCode callees) .id))) .zero

theorem actionsFlatCode_eval (callees : Callees) (game : Adjudication.Game) :
    (actionsFlatCode callees).eval (Data.encodeGame game) =
      pure [ListCode.stack ((WithoutDead.legalActions game).map actionWord)] := by
  cases ha : WithoutDead.automaticWithoutDead game with
  | none =>
    have hw : (WithoutDead.legalActions game).map actionWord =
        legalWords game 28672 ++ claimWords game := by
      simp only [WithoutDead.legalActions, ha, ↓reduceIte, List.map_append, List.map_map]
      rw [show (actionWord ∘ Action.play) = plyWord by rfl, legalWords_eq]
      cases hc : Adjudication.canClaimDraw game <;> simp [claimWords, hc, actionWord]
    simp [actionsFlatCode, NatCode.ifZero, automaticFlatCode_eval, ha, automaticWord,
      initialClaimCode_eval, actionsLoop_eval, Bind.bind, hw]
  | some outcome =>
    cases outcome with
    | draw =>
      simp [actionsFlatCode, NatCode.ifZero, automaticFlatCode_eval, ha, automaticWord,
        Program.encodeOutcome, Bind.bind, WithoutDead.legalActions, ListCode.stack]
    | win color =>
      cases color <;>
        simp [actionsFlatCode, NatCode.ifZero, automaticFlatCode_eval, ha, automaticWord,
          Program.encodeOutcome, Bind.bind, WithoutDead.legalActions, ListCode.stack]
      all_goals rfl

def actionsCode (callees : Callees) : Code := .comp (actionsFlatCode callees) decodeStackCode

theorem actionsCode_eval (callees : Callees) (game : Adjudication.Game) :
    (actionsCode callees).eval [gameWord game] =
      pure [ListCode.stack ((WithoutDead.legalActions game).map actionWord)] := by
  simp [actionsCode, gameWord, decodeStackCode_eval, actionsFlatCode_eval, Bind.bind]

namespace Fixtures

def empty (target : Option Square) : Exec.Position := Exec.encode
  {board := fun _ ↦ none, turn := .white, castlingRights := ⟨false, false, false, false⟩,
    enPassantTarget := target, halfmoveClock := 0}

theorem empty_no_capture (target : Option Square) :
    ¬History.HasLegalEnPassant (Exec.decode (empty target)) := by
  rintro ⟨ply, _, piece, present, _⟩
  simp [empty, Exec.decode, Exec.decodeBoard, Exec.encode, Exec.encodeBoard] at present

theorem empty_same (first second : Option Square) :
    SamePosition (Exec.decode (empty first)) (Exec.decode (empty second)) := by
  apply (History.samePosition_iff _ _).mpr
  exact ⟨fun _ ↦ rfl, rfl, rfl, Or.inr ⟨empty_no_capture first, empty_no_capture second⟩⟩

def epPosition (promotion : Bool) : Exec.Position := Exec.encode
  { board := fun square ↦
      if square = (⟨0, 0⟩ : Square) then some ⟨.white, .king⟩
      else if square = (⟨7, 5⟩ : Square) then some ⟨.black, .king⟩
      else if square = (⟨4, if promotion then 6 else 4⟩ : Square) then some ⟨.white, .pawn⟩
      else if square = (⟨3, if promotion then 6 else 4⟩ : Square) then some ⟨.black, .pawn⟩
      else none
    turn := .white, castlingRights := ⟨false, false, false, false⟩,
    enPassantTarget := some ⟨3, if promotion then 7 else 5⟩, halfmoveClock := 0 }

def epPly (promotion : Bool) : Ply :=
  ⟨⟨4, if promotion then 6 else 4⟩, ⟨3, if promotion then 7 else 5⟩,
    if promotion then some .queen else none⟩

theorem ep_legal (promotion : Bool) :
    IsLegalPly (Exec.decode (epPosition promotion)) (epPly promotion) := by
  cases promotion <;> decide +kernel

theorem ep_exists (promotion : Bool) :
    History.HasLegalEnPassant (Exec.decode (epPosition promotion)) := by
  refine ⟨epPly promotion, ep_legal promotion, ⟨.white, .pawn⟩, ?_, ?_⟩
  · cases promotion <;> decide +kernel
  · cases promotion <;> decide +kernel

theorem ep_distinct (promotion : Bool) :
    ¬SamePosition (Exec.decode (epPosition promotion))
      (Exec.decode {epPosition promotion with enPassantTarget := none}) := by
  intro h
  have conditions := (History.samePosition_iff _ _).mp h
  rcases conditions.2.2.2 with equal | absent
  · cases promotion <;> cases equal
  · exact absent.1 (ep_exists promotion)

def historyGame : Adjudication.Game :=
  ⟨Exec.initial, [{Exec.initial with halfmoveClock := 7}, Exec.initial,
    {Exec.initial with turn := .black}]⟩

theorem history_count : historyGame.occurrences = 3 := by decide +kernel

def intendedGame : Adjudication.Game :=
  ⟨{Exec.initial with halfmoveClock := 99}, []⟩

def quietKnight : Ply := ⟨⟨6, 0⟩, ⟨5, 2⟩, none⟩

theorem knight_legal : IsLegalPly (Exec.decode intendedGame.current) quietKnight := by
  decide +kernel

theorem intended_current_false : ¬CurrentClaim intendedGame := by decide +kernel

theorem intended_claim : CanClaimDraw (Adjudication.decodeGame intendedGame) := by
  right
  right
  refine ⟨quietKnight, knight_legal, ?_⟩
  have hc := congrArg Chess.Position.halfmoveClock
    (Exec.decode_applyPly intendedGame.current quietKnight)
  change 100 ≤ (applyPly (Exec.decode intendedGame.current) quietKnight).halfmoveClock
  rw [← hc]
  decide +kernel

/-- Exact modular-code regressions include a raw last-rank en-passant promotion. -/
theorem code_fixtures (callees : Callees) :
    (samePositionCode callees).eval
      (Data.encodePosition (empty none) ++
        Data.encodePosition (empty (some ⟨3, 5⟩))) = pure [1] ∧
    (samePositionCode callees).eval
      (Data.encodePosition (epPosition false) ++
        Data.encodePosition {epPosition false with enPassantTarget := none}) = pure [0] ∧
    (samePositionCode callees).eval
      (Data.encodePosition (epPosition true) ++
        Data.encodePosition {epPosition true with enPassantTarget := none}) = pure [0] ∧
    (occurrencesCode callees).eval (Data.encodeGame historyGame) = pure [3] ∧
    (canClaimCode callees).eval (Data.encodeGame intendedGame) = pure [1] := by
  exact ⟨by simp [samePositionCode_eval, truth, empty_same],
    by simp [samePositionCode_eval, truth, ep_distinct],
    by simp [samePositionCode_eval, truth, ep_distinct],
    by simp [occurrencesCode_eval, history_count],
    by simp [canClaimCode_eval, truth, intended_claim]⟩

/-- Direct execution of framing helpers uses mathlib's sequential interpreter. -/
theorem framing_executions :
    ListCode.runCode 500 decodeStackCode [0] = some [] ∧
    ListCode.runCode 500 encodeFramedCode [0] = some [0] := by decide

end Fixtures

end Chess.Compilation.HistoryCode
