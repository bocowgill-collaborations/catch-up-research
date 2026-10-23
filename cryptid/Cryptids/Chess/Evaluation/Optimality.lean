/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Evaluation.Strategies

/-!
# Strategic guarantees

A policy is chosen at every full history. Its guarantee quantifies over every legal opponent
strategy, rather than over one favorable line. Opponent legality is needed for result existence;
the inequalities hold for any derivable result, because each result already carries legal moves.
-/

@[expose] public section
namespace Chess.Evaluation
open Adjudication

@[simp] theorem utility_other (color : Color) (outcome : Outcome) :
    utility color outcome + utility color.other outcome = 2 := by
  cases color <;> cases outcome with
  | draw => rfl
  | win winner => cases winner <;> rfl

theorem other_of_ne {first second : Color} (different : first ≠ second) :
    first = second.other := by cases first <;> cases second <;> simp_all [Color.other]

/-- The reference-level value of an action. -/
noncomputable def moveValue (game : Chess.Game) : Action → Outcome
  | .claimDraw => .draw
  | .play ply => value (game.play ply)

theorem actionValue_encode (game : Chess.Game) (action : Action) :
    actionValue (encodeGame game) action = moveValue game action := by
  cases action <;> simp only [actionValue, moveValue, value, encode_play]

theorem value_policy {game : Chess.Game} (live : ¬∃ o, AutomaticOutcome game o) :
    value game = moveValue game (strategy game) := by
  have h := solve_policy (encodeGame game) ((automatic_none_iff _).mpr
    (by simpa only [decode_encodeGame] using live))
  simpa only [value, strategy, actionValue_encode] using h

theorem value_optimal {game : Chess.Game} {action : Action} (legal : IsLegalAction game action) :
    utility game.current.turn (moveValue game action) ≤ utility game.current.turn (value game) := by
  have live : ¬∃ o, AutomaticOutcome game o := by cases action <;> exact legal.1
  have h := optimal (encodeGame game) ((automatic_none_iff _).mpr
    (by simpa only [decode_encodeGame] using live)) action
    (by simpa only [decode_encodeGame] using legal)
  rw [actionValue_encode] at h
  exact h

/-- On this player's turns the selected action agrees with the pointwise optimal policy. -/
def UsesPolicy (color : Color) (white black : Strategy) : Prop :=
  ∀ game, game.current.turn = color → selectedAction white black game = strategy game

theorem white_uses (black : Strategy) : UsesPolicy .white strategy black :=
  fun _ turn ↦ by simp only [selectedAction, turn]

theorem black_uses (white : Strategy) : UsesPolicy .black white strategy :=
  fun _ turn ↦ by simp only [selectedAction, turn]

/-- Against any opponent, a policy user's actual result is at least their computed value. -/
theorem policy_guarantee (color : Color) {white black : Strategy}
    (uses : UsesPolicy color white black) {game : Chess.Game} {outcome : Outcome}
    (result : ResultsIn white black game outcome) :
    utility color (value game) ≤ utility color outcome := by
  induction result with
  | automatic terminal => rw [value_terminal terminal]
  | @claimDraw game selected legal =>
      by_cases turn : game.current.turn = color
      · have chosen := (uses game turn).symm.trans selected
        rw [value_policy legal.1, chosen]
        exact le_rfl
      · have bound := value_optimal legal
        have opposite := other_of_ne turn
        rw [opposite] at bound
        have one := utility_other color (value game)
        have two := utility_other color .draw
        change utility color.other .draw ≤ utility color.other (value game) at bound
        omega
  | @play game outcome ply selected legal _ ih =>
      by_cases turn : game.current.turn = color
      · have chosen := (uses game turn).symm.trans selected
        simpa only [value_policy legal.1, chosen, moveValue] using ih
      · have bound := value_optimal legal
        have opposite := other_of_ne turn
        rw [opposite] at bound
        have one := utility_other color (value game)
        have two := utility_other color (value (game.play ply))
        change utility color.other (value (game.play ply)) ≤
          utility color.other (value game) at bound
        omega

theorem utility_injective (color : Color) : Function.Injective (utility color) := by
  intro a b equal
  cases color <;> rcases a with ⟨(_ | _)⟩ | _ <;> rcases b with ⟨(_ | _)⟩ | _ <;>
    simp_all [utility]

/-- Both optimal policies give exactly the evaluated result wherever a result is derivable. -/
theorem optimal_pair_value {game : Chess.Game} {outcome : Outcome}
    (result : ResultsIn strategy strategy game outcome) : outcome = value game := by
  have white := policy_guarantee .white (white_uses strategy) result
  have black := policy_guarantee .black (black_uses strategy) result
  have one := utility_other .white (value game)
  have two := utility_other .white outcome
  apply utility_injective .white
  change utility .black (value game) ≤ utility .black outcome at black
  change utility .white (value game) + utility .black (value game) = 2 at one
  change utility .white outcome + utility .black outcome = 2 at two
  omega

theorem optimal_pair_result (game : Chess.Game) (reachable : Reachable game) :
    ResultsIn strategy strategy game (value game) := by
  obtain ⟨outcome, result⟩ := results_exist strategy strategy (strategy_legal .white)
    (strategy_legal .black) (encodeGame game)
    (by simpa only [decode_encodeGame] using reachable)
  have raw : ResultsIn strategy strategy game outcome := decode_encodeGame game ▸ result
  exact optimal_pair_value raw ▸ raw

end Chess.Evaluation
