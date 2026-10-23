/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Exec.Rules

/-!
# Complete executable move enumeration

Candidates enumerate all source/destination squares and all seven optional promotion values.
Filtering uses the constructive legal-ply decision. This deliberately simple baseline also
specifies the order and proves that there are no duplicates. It performs no terminal or history
checks: these are raw legal plies, as required by the reference's `IsLegalPly` predicate.
-/

@[expose] public section
namespace Chess.Exec

/-- All squares, ordered by file and then rank. -/
def squares : List Square :=
  ((List.finRange 8).product (List.finRange 8)).map fun pair ↦ ⟨pair.1, pair.2⟩

@[simp] theorem mem_squares (square : Square) : square ∈ squares := by
  cases square
  simp [squares, List.mem_finRange]

theorem squares_nodup : squares.Nodup :=
  ((List.nodup_finRange 8).product (List.nodup_finRange 8)).map
    (fun a b h ↦ by simpa only [Square.mk.injEq, Prod.ext_iff] using h)

/-- All raw promotion requests. Legality excludes king/pawn promotions and spurious requests. -/
def promotions : List (Option PieceKind) :=
  [none, some .king, some .queen, some .rook, some .bishop, some .knight, some .pawn]

@[simp] theorem mem_promotions (promotion : Option PieceKind) : promotion ∈ promotions := by
  cases promotion with
  | none => simp [promotions]
  | some kind => cases kind <;> simp [promotions]

theorem promotions_nodup : promotions.Nodup := by decide +kernel

/-- Exhaustive raw moves. The seven promotion requests are the innermost loop. -/
def candidates : List Ply :=
  ((squares.product squares).product promotions).map fun pair ↦
    ⟨pair.1.1, pair.1.2, pair.2⟩

@[simp] theorem mem_candidates (ply : Ply) : ply ∈ candidates := by
  cases ply
  simp [candidates]

theorem candidates_nodup : candidates.Nodup :=
  ((squares_nodup.product squares_nodup).product promotions_nodup).map
    (fun a b h ↦ by simpa only [Ply.mk.injEq, Prod.ext_iff, and_assoc] using h)

theorem candidates_length : candidates.length = 28672 := by
  have product_length {α β : Type} (a : List α) (b : List β) :
      (a.product b).length = a.length * b.length := List.length_product a b
  simp [candidates, squares, promotions, product_length]

/-- All and only raw legal plies, in candidate order. -/
def legalPlies (position : Position) : List Ply := candidates.filter (isLegal position)

/-- Soundness and completeness have no reachability or well-formedness hypothesis. -/
@[simp] theorem mem_legalPlies (position : Position) (ply : Ply) :
    ply ∈ legalPlies position ↔ IsLegalPly (decode position) ply := by
  simp [legalPlies]

theorem legalPlies_nodup (position : Position) : (legalPlies position).Nodup :=
  candidates_nodup.filter _

end Chess.Exec
