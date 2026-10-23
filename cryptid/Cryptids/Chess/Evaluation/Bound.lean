/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Adjudication
public import Mathlib.Data.Fintype.Fin

/-!
# A finite rank for full, history-dependent games

The finite key is used only in this termination proof. Evaluation retains the full game.
Each key has four slots before its fifth occurrence forces an automatic result. The remaining
capacity is a proof-only finite sum; no enumeration of the enormous key space is executed.
The terminal/nonterminal bit accounts for a final move into an already saturated key.
-/

@[expose] public section
namespace Chess.Evaluation
open Adjudication

abbrev Game := Adjudication.Game

/-- All raw position keys, newest first, with multiplicities preserved. -/
def keys (game : Game) : List Key := (decodeGame game).positions.map project

@[simp] theorem keys_play (game : Game) (ply : Ply) :
    keys (game.play ply) = project (Exec.decode (Exec.applyPly game.current ply)) ::
      keys game := rfl

theorem count_map_card (positions : List Chess.Position) (key : Key) :
    (positions.map project).count key =
      Fintype.card {i : Fin positions.length // project (positions.get i) = key} := by
  induction positions with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.count_cons, beq_iff_eq, Fintype.card_subtype,
        Fin.card_filter_univ_succ', List.get_eq_getElem, List.length_cons,
        List.getElem_cons_zero, Fin.val_zero, Fin.val_succ, List.getElem_cons_succ, ih]
      exact Nat.add_comm _ _

/-- Equality of raw keys is sufficient for the reference's repetition relation. -/
theorem key_count_le_occurrences (game : Game) :
    (keys game).count (project (decodeGame game).current) ≤ occurrences (decodeGame game) := by
  rw [keys, count_map_card]
  exact Fintype.card_le_of_injective
    (fun i ↦ (⟨i.val, samePosition_of_project_eq i.property⟩ :
      {i : Fin (decodeGame game).positions.length //
        SamePosition ((decodeGame game).positions.get i) (decodeGame game).current}))
    (fun i j equal ↦ by
      injection equal with h
      exact Subtype.ext h)

theorem nonterminal_count (game : Game) (live : automatic game = none) :
    (keys game).count (project (decodeGame game).current) < 5 := by
  by_contra! five
  have repeated := (repeated_iff_occurrences (decodeGame game) 5).mpr
    (five.trans (key_count_le_occurrences game))
  by_cases mate : IsCheckmate (decodeGame game).current
  · exact (automatic_none_iff game).mp live ⟨_, .checkmate mate⟩
  · exact (automatic_none_iff game).mp live ⟨_, .fivefoldRepetition mate repeated⟩

/-- Proof-only capacity: four visits per key suffice before a fifth ends play. -/
noncomputable def capacity (history : List Key) : ℕ :=
  let _ := Fintype.ofFinite Key
  ∑ key : Key, (4 - history.count key)

theorem capacity_le (history : List Key) : capacity history ≤ 4 * Nat.card Key := by
  classical
  let _ := Fintype.ofFinite Key
  unfold capacity
  calc
    _ ≤ ∑ _ : Key, 4 := Finset.sum_le_sum (fun _ _ ↦ Nat.sub_le _ _)
    _ = _ := by simp [Nat.card_eq_fintype_card, Nat.mul_comm]

theorem capacity_cons_le (history : List Key) (key : Key) :
    capacity (key :: history) ≤ capacity history := by
  classical
  unfold capacity
  exact Finset.sum_le_sum (fun k _ ↦ Nat.sub_le_sub_left
    (by simp only [List.count_cons]; split_ifs <;> omega) 4)

theorem capacity_cons_lt (history : List Key) (key : Key) (space : history.count key < 4) :
    capacity (key :: history) < capacity history := by
  classical
  let _ := Fintype.ofFinite Key
  unfold capacity
  apply Finset.sum_lt_sum
  · intro k _
    exact Nat.sub_le_sub_left (by simp only [List.count_cons]; split_ifs <;> omega) 4
  · exact ⟨key, Finset.mem_univ _, by simp only [List.count_cons_self]; omega⟩

/-- A proof-only natural rank; the bit allows a final move to a saturated key. -/
noncomputable def rank (game : Game) : ℕ :=
  2 * capacity (keys game) + if automatic game = none then 1 else 0

theorem rank_le (game : Game) : rank game ≤ 8 * Nat.card Key + 1 := by
  have bound := capacity_le (keys game)
  unfold rank
  split_ifs <;> omega

theorem rank_play_lt (game : Game) (ply : Ply) (live : automatic game = none) :
    rank (game.play ply) < rank game := by
  have monotone := capacity_cons_le (keys game)
    (project (Exec.decode (Exec.applyPly game.current ply)))
  by_cases nextLive : automatic (game.play ply) = none
  · have count := nonterminal_count (game.play ply) nextLive
    have strict := capacity_cons_lt (keys game)
      (project (Exec.decode (Exec.applyPly game.current ply))) (by
        change (keys (game.play ply)).count
          (project (Exec.decode (Exec.applyPly game.current ply))) < 5 at count
        rw [keys_play, List.count_cons_self] at count
        omega)
    simp only [rank, live, nextLive, ite_true, keys_play]
    omega
  · simp only [rank, live, nextLive, ite_true, ite_false, keys_play]
    omega

/-- A prefix counts played plies, including a possible final move into a terminal game. -/
inductive LegalPrefix : Game → ℕ → Game → Prop
  | nil (game) : LegalPrefix game 0 game
  | cons {game finish n ply} (legal : IsLegalAction (decodeGame game) (.play ply))
      (rest : LegalPrefix (game.play ply) n finish) : LegalPrefix game (n + 1) finish

theorem prefix_rank {game finish : Game} {n : ℕ} (path : LegalPrefix game n finish) :
    n + rank finish ≤ rank game := by
  induction path with
  | nil => omega
  | @cons game finish n ply legal _ ih =>
      have decrease := rank_play_lt game ply ((automatic_none_iff game).mpr legal.1)
      omega

/-- Uniform finite continuation bound, valid even on arbitrary input histories. -/
theorem uniform_play_bound {game finish : Game} {n : ℕ}
    (path : LegalPrefix game n finish) : n ≤ 8 * Nat.card Key + 1 :=
  (Nat.le_add_right n (rank finish)).trans ((prefix_rank path).trans (rank_le game))

/-- A claim ends the play and counts as one action, without creating another position. -/
theorem uniform_claim_bound {game finish : Game} {n : ℕ}
    (path : LegalPrefix game n finish) (claim : IsLegalAction (decodeGame finish) .claimDraw) :
    n + 1 ≤ 8 * Nat.card Key + 1 := by
  have live := (automatic_none_iff finish).mpr claim.1
  have positive : 1 ≤ rank finish := by simp only [rank, live, ite_true]; omega
  have bound := (prefix_rank path).trans (rank_le game)
  omega

/-- The enumerated action set is finite; strategies themselves are not enumerated. -/
theorem finite_branching (game : Game) : Set.Finite {a | IsLegalAction (decodeGame game) a} := by
  exact (legalActions game).finite_toSet.subset (fun _ h ↦ (mem_legalActions game _).mpr h)

end Chess.Evaluation
