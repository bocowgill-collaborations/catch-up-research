/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Evaluation.Choice

/-!
# Total backward induction

Recursive calls keep the complete game, including clocks, history, and optional claims.
The proof-only rank makes recursion total without a fuel cutoff or fallback draw result.
The chosen action is legal at every nonterminal raw game, including off-trajectory histories.
-/

@[expose] public section
namespace Chess.Evaluation
open Adjudication

theorem actions_nonempty (game : Game) (live : automatic game = none) :
    legalActions game ≠ [] := by
  obtain ⟨action, legal⟩ := nonterminal_has_action (decodeGame game)
    ((automatic_none_iff game).mp live)
  exact List.ne_nil_of_mem ((mem_legalActions game action).mpr legal)

/-- A value and an optimal action. At terminal games the action is unused. -/
def analyse (game : Game) : Outcome × Action :=
  if live : automatic game = none then
    let value (action : {a // a ∈ legalActions game}) : Outcome :=
      match action.val with
      | .claimDraw => .draw
      | .play ply => (analyse (game.play ply)).1
    let first : {a // a ∈ legalActions game} :=
      ⟨(legalActions game).head (actions_nonempty game live), List.head_mem _⟩
    let best := choose game.current.turn value first (legalActions game).attach
    (value best, best.val)
  else ((automatic game).get (by cases h : automatic game <;> simp_all), .claimDraw)
termination_by rank game
decreasing_by all_goals exact rank_play_lt game _ live

/-- The game-theoretic result; computing the standard initial value is not required. -/
def solve (game : Game) : Outcome := (analyse game).1

/-- A pointwise choice at every history, not a strategy patched along one play. -/
def policy (game : Game) : Action := (analyse game).2

/-- Evaluate a single action; claims end immediately and played moves retain full state. -/
def actionValue (game : Game) : Action → Outcome
  | .claimDraw => .draw
  | .play ply => solve (game.play ply)

/-- The finite maximizing choice, with membership carried as an erased proof. -/
def bestAction (game : Game) (live : automatic game = none) :
    {a // a ∈ legalActions game} :=
  choose game.current.turn (fun a ↦ actionValue game a.val)
    ⟨(legalActions game).head (actions_nonempty game live), List.head_mem _⟩
    (legalActions game).attach

theorem analyse_live (game : Game) (live : automatic game = none) :
    analyse game = (actionValue game (bestAction game live).val, (bestAction game live).val) := by
  rw [analyse]
  simp only [dite_eq_left live]
  rfl

theorem solve_terminal (game : Game) (outcome : Outcome)
    (terminal : automatic game = some outcome) : solve game = outcome := by
  unfold solve
  rw [analyse]
  simp [terminal]

theorem policy_legal (game : Game) (live : automatic game = none) :
    IsLegalAction (decodeGame game) (policy game) := by
  rw [policy, analyse_live game live]
  exact (mem_legalActions game _).mp (bestAction game live).property

theorem solve_policy (game : Game) (live : automatic game = none) :
    solve game = actionValue game (policy game) := by
  rw [solve, policy, analyse_live game live]

theorem optimal (game : Game) (live : automatic game = none) (action : Action)
    (legal : IsLegalAction (decodeGame game) action) :
    utility game.current.turn (actionValue game action) ≤
      utility game.current.turn (solve game) := by
  rw [solve, analyse_live game live]
  exact choose_ge game.current.turn
    (fun a : {a // a ∈ legalActions game} ↦ actionValue game a.val) _ _
    ⟨action, (mem_legalActions game action).mpr legal⟩
    (List.mem_cons_of_mem _ (by simp only [List.mem_attach]))

end Chess.Evaluation
