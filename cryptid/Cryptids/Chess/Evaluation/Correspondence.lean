/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Evaluation.Optimality

/-!
# Correspondence with the frozen strategic proposition

These theorems characterize all three possible evaluated values. None evaluates the standard
initial game or assumes the open draw conjecture. Strategies are total functions on histories;
legality is global on all reachable histories and opponents range over all legal strategies.
-/

@[expose] public section
namespace Chess.Evaluation
open Adjudication

/-- A globally legal strategy guarantees the predicate against every globally legal opponent. -/
def CanGuarantee (color : Color) (predicate : Outcome → Prop) : Prop :=
  match color with
  | .white => ∃ white, IsLegalStrategy .white white ∧
      ∀ black, IsLegalStrategy .black black →
        ∃ outcome, ResultsIn white black Chess.Game.initial outcome ∧ predicate outcome
  | .black => ∃ black, IsLegalStrategy .black black ∧
      ∀ white, IsLegalStrategy .white white →
        ∃ outcome, ResultsIn white black Chess.Game.initial outcome ∧ predicate outcome

theorem guarantee_iff_threshold (color : Color) (threshold : ℕ) :
    CanGuarantee color (fun o ↦ threshold ≤ utility color o) ↔
      threshold ≤ utility color (value Chess.Game.initial) := by
  cases color with
  | white =>
      constructor
      · rintro ⟨white, _, guaranteed⟩
        obtain ⟨outcome, result, score⟩ := guaranteed strategy (strategy_legal .black)
        have bound := policy_guarantee .black (black_uses white) result
        have one := utility_other .white (value Chess.Game.initial)
        have two := utility_other .white outcome
        change utility .black (value Chess.Game.initial) ≤ utility .black outcome at bound
        change utility .white (value Chess.Game.initial) +
          utility .black (value Chess.Game.initial) = 2 at one
        change utility .white outcome + utility .black outcome = 2 at two
        omega
      · intro score
        refine ⟨strategy, strategy_legal .white, fun black legal ↦ ?_⟩
        obtain ⟨outcome, result⟩ := results_exist strategy black (strategy_legal .white) legal
          Adjudication.Game.initial (decode_initialGame.symm ▸ Reachable.initial)
        have raw : ResultsIn strategy black Chess.Game.initial outcome :=
          decode_initialGame ▸ result
        exact ⟨outcome, raw, score.trans (policy_guarantee .white (white_uses black) raw)⟩
  | black =>
      constructor
      · rintro ⟨black, _, guaranteed⟩
        obtain ⟨outcome, result, score⟩ := guaranteed strategy (strategy_legal .white)
        have bound := policy_guarantee .white (white_uses black) result
        have one := utility_other .white (value Chess.Game.initial)
        have two := utility_other .white outcome
        change utility .white (value Chess.Game.initial) +
          utility .black (value Chess.Game.initial) = 2 at one
        change utility .white outcome + utility .black outcome = 2 at two
        omega
      · intro score
        refine ⟨strategy, strategy_legal .black, fun white legal ↦ ?_⟩
        obtain ⟨outcome, result⟩ := results_exist white strategy legal (strategy_legal .black)
          Adjudication.Game.initial (decode_initialGame.symm ▸ Reachable.initial)
        have raw : ResultsIn white strategy Chess.Game.initial outcome :=
          decode_initialGame ▸ result
        exact ⟨outcome, raw, score.trans (policy_guarantee .black (black_uses white) raw)⟩

theorem utility_pos_iff (color : Color) (outcome : Outcome) :
    1 ≤ utility color outcome ↔ outcome ≠ .win color.other := by
  cases color <;> rcases outcome with ⟨(_ | _)⟩ | _ <;> decide +kernel

theorem utility_two_iff (color : Color) (outcome : Outcome) :
    2 ≤ utility color outcome ↔ outcome = .win color := by
  cases color <;> rcases outcome with ⟨(_ | _)⟩ | _ <;> decide +kernel

theorem white_avoid_loss_iff :
    WhiteCanAvoidLoss ↔ value Chess.Game.initial ≠ .win .black := by
  simpa only [CanGuarantee, utility_pos_iff, Color.other, WhiteCanAvoidLoss] using
    guarantee_iff_threshold .white 1

theorem black_avoid_loss_iff :
    BlackCanAvoidLoss ↔ value Chess.Game.initial ≠ .win .white := by
  simpa only [CanGuarantee, utility_pos_iff, Color.other, BlackCanAvoidLoss] using
    guarantee_iff_threshold .black 1

/-- Forced victory against every legal opponent, with a unique result for each pair. -/
def CanForceWin (color : Color) : Prop := CanGuarantee color (fun o ↦ o = .win color)

theorem force_win_iff (color : Color) :
    CanForceWin color ↔ value Chess.Game.initial = .win color := by
  simpa only [CanForceWin, utility_two_iff] using guarantee_iff_threshold color 2

@[simp] theorem value_initial : value Chess.Game.initial = solve Adjudication.Game.initial := by
  have h := congrArg encodeGame decode_initialGame
  simpa only [encode_decodeGame, value] using congrArg solve h.symm

/-- Main M4 contract: the executable value is exactly the frozen draw proposition. -/
theorem solve_initial_draw_iff :
    solve Adjudication.Game.initial = .draw ↔ (WhiteCanAvoidLoss ∧ BlackCanAvoidLoss) := by
  rw [← value_initial, white_avoid_loss_iff, black_avoid_loss_iff]
  rcases value Chess.Game.initial with ⟨(_ | _)⟩ | _ <;> simp

theorem solve_initial_white_win_iff :
    solve Adjudication.Game.initial = .win .white ↔ CanForceWin .white := by
  rw [force_win_iff, value_initial]

theorem solve_initial_black_win_iff :
    solve Adjudication.Game.initial = .win .black ↔ CanForceWin .black := by
  rw [force_win_iff, value_initial]

end Chess.Evaluation
