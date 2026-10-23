/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Evaluation.Solver

/-! # Globally legal strategies and their unique results -/

@[expose] public section
namespace Chess.Evaluation
open Adjudication

/-- Evaluate a frozen-reference game through the proved lossless encoding. -/
def value (game : Chess.Game) : Outcome := solve (encodeGame game)

/-- A total strategy defined on every frozen-reference history. -/
def strategy : Strategy := fun game ↦ policy (encodeGame game)

theorem encode_play (game : Chess.Game) (ply : Ply) :
    encodeGame (game.play ply) = (encodeGame game).play ply := by
  have h := congrArg encodeGame (decode_play (encodeGame game) ply)
  simpa only [decode_encodeGame, encode_decodeGame] using h.symm

theorem value_terminal {game : Chess.Game} {outcome : Outcome}
    (terminal : AutomaticOutcome game outcome) : value game = outcome :=
  solve_terminal (encodeGame game) outcome ((automatic_some_iff _ _).mpr
    (by simpa only [decode_encodeGame] using terminal))

/-- The same policy is legal for either player at every reachable history. -/
theorem strategy_legal (color : Color) : IsLegalStrategy color strategy := by
  intro game _ _ live
  have h := policy_legal (encodeGame game) ((automatic_none_iff _).mpr
    (by simpa only [decode_encodeGame] using live))
  simpa only [decode_encodeGame, strategy] using h

theorem selected_legal {white black : Strategy} (whiteLegal : IsLegalStrategy .white white)
    (blackLegal : IsLegalStrategy .black black) {game : Chess.Game}
    (reachable : Reachable game) (live : ¬∃ o, AutomaticOutcome game o) :
    IsLegalAction game (selectedAction white black game) := by
  cases turn : game.current.turn with
  | white => simpa only [selectedAction, turn] using whiteLegal game reachable turn live
  | black => simpa only [selectedAction, turn] using blackLegal game reachable turn live

/-- Strategy-pair results are deterministic, even before assuming global strategy legality. -/
theorem results_unique {white black : Strategy} {game : Chess.Game} {first second : Outcome}
    (one : ResultsIn white black game first) (two : ResultsIn white black game second) :
    first = second := by
  induction one with
  | automatic terminal =>
      cases two with
      | automatic other => exact automatic_unique terminal other
      | claimDraw _ legal => exact (legal.1 ⟨_, terminal⟩).elim
      | play _ legal _ => exact (legal.1 ⟨_, terminal⟩).elim
  | claimDraw selected legal =>
      cases two with
      | automatic terminal => exact (legal.1 ⟨_, terminal⟩).elim
      | claimDraw => rfl
      | play other _ _ => cases selected.symm.trans other
  | play selected legal _ ih =>
      cases two with
      | automatic terminal => exact (legal.1 ⟨_, terminal⟩).elim
      | claimDraw other _ => cases selected.symm.trans other
      | play other _ next =>
          cases Action.play.inj (selected.symm.trans other)
          exact ih next

/-- Any globally legal pair produces a result from every reachable full history. -/
theorem results_exist (white black : Strategy) (whiteLegal : IsLegalStrategy .white white)
    (blackLegal : IsLegalStrategy .black black) (game : Game)
    (reachable : Reachable (decodeGame game)) :
    ∃ outcome, ResultsIn white black (decodeGame game) outcome := by
  induction game using (measure rank).wf.induction with
  | h game ih =>
      by_cases live : automatic game = none
      · have legal := selected_legal whiteLegal blackLegal reachable
          ((automatic_none_iff game).mp live)
        cases selected : selectedAction white black (decodeGame game) with
        | claimDraw => exact ⟨.draw, .claimDraw selected (selected ▸ legal)⟩
        | play ply =>
            have moveLegal : IsLegalAction (decodeGame game) (.play ply) := selected ▸ legal
            have nextReach : Reachable (decodeGame (game.play ply)) :=
              (decode_play game ply).symm ▸ Reachable.play reachable moveLegal
            obtain ⟨outcome, result⟩ := ih (game.play ply) (rank_play_lt game ply live) nextReach
            exact ⟨outcome, .play selected moveLegal ((decode_play game ply) ▸ result)⟩
      · cases terminal : automatic game with
        | none => exact (live terminal).elim
        | some outcome => exact ⟨outcome, .automatic ((automatic_some_iff _ _).mp terminal)⟩

/-- The initial result exists and is unique for every globally legal pair. -/
theorem initial_result_unique (white black : Strategy)
    (whiteLegal : IsLegalStrategy .white white) (blackLegal : IsLegalStrategy .black black) :
    ∃! outcome, ResultsIn white black Chess.Game.initial outcome := by
  obtain ⟨outcome, result⟩ := results_exist white black whiteLegal blackLegal
    Adjudication.Game.initial (decode_initialGame.symm ▸ Reachable.initial)
  exact ⟨outcome, decode_initialGame ▸ result, fun _ other ↦
    results_unique other (decode_initialGame ▸ result)⟩

end Chess.Evaluation
