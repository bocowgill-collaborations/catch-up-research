/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Evaluation.Bound

/-! # Finite maximization of a player's outcome -/

@[expose] public section
namespace Chess.Evaluation

/-- Each player ranks their win above a draw above their opponent's win. -/
def utility (color : Color) : Outcome → ℕ
  | .draw => 1
  | .win winner => if winner = color then 2 else 0

/-- Select an actual candidate, retaining the earlier one when values tie. -/
def choose {α : Type} (color : Color) (value : α → Outcome) (first : α) (rest : List α) : α :=
  match rest with
  | [] => first
  | next :: rest =>
      let best := choose color value next rest
      if utility color (value best) ≤ utility color (value first) then first else best
termination_by structural rest

theorem choose_mem {α : Type} (color : Color) (value : α → Outcome) (first : α) (rest : List α) :
    choose color value first rest ∈ first :: rest := by
  induction rest generalizing first with
  | nil => simp [choose]
  | cons next rest ih =>
      simp only [choose]
      split_ifs
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih next)

theorem choose_ge {α : Type} (color : Color) (value : α → Outcome) (first : α) (rest : List α)
    (candidate : α) (member : candidate ∈ first :: rest) :
    utility color (value candidate) ≤ utility color (value (choose color value first rest)) := by
  induction rest generalizing first with
  | nil =>
      cases List.mem_singleton.mp member
      exact le_rfl
  | cons next rest ih =>
      simp only [choose]
      split_ifs with better
      · rcases List.mem_cons.mp member with rfl | member
        · exact le_rfl
        · exact (ih next member).trans better
      · rcases List.mem_cons.mp member with rfl | member
        · exact (Nat.le_of_lt (Nat.lt_of_not_ge better))
        · exact ih next member

end Chess.Evaluation
