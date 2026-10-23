/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Adjudication.Claims

/-!
# Exact automatic outcomes and legal actions

Checkmate has priority. Other immediately decidable draws are checked before the potentially
expensive exact dead-position search. Claims remain optional actions, never automatic results.
The uniqueness and action-existence theorems hold even on raw games.
-/

@[expose] public section
namespace Chess.Adjudication

theorem dead_not_checkmate {position : Chess.Position} (dead : IsDeadPosition position) :
    ¬IsCheckmate position := dead position .refl

theorem automatic_unique {game : Chess.Game} {first second : Outcome}
    (one : AutomaticOutcome game first) (two : AutomaticOutcome game second) : first = second := by
  cases one <;> cases two <;> first
    | rfl
    | solve | aesop (add safe dead_not_checkmate) (add simp [IsCheckmate, IsStalemate])

/-- These conditions all give an automatic draw in the absence of checkmate. -/
def DrawCondition (game : Chess.Game) : Prop :=
  IsStalemate game.current ∨ game.RepeatedAtLeast 5 ∨
    150 ≤ game.current.halfmoveClock ∨ IsDeadPosition game.current

instance (game : Chess.Game) : Decidable (DrawCondition game) := by
  unfold DrawCondition
  infer_instance

theorem drawCondition_iff {game : Chess.Game} (notMate : ¬IsCheckmate game.current) :
    DrawCondition game ↔ AutomaticOutcome game .draw := by
  constructor
  · rintro (stale | repeated | clock | dead)
    · exact .stalemate stale
    · exact .fivefoldRepetition notMate repeated
    · exact .seventyFiveMoveRule notMate clock
    · exact .deadPosition dead
  · intro outcome
    cases outcome with
    | stalemate h => exact Or.inl h
    | deadPosition h => exact Or.inr (Or.inr (Or.inr h))
    | fivefoldRepetition _ h => exact Or.inr (Or.inl h)
    | seventyFiveMoveRule _ h => exact Or.inr (Or.inr (Or.inl h))

/-- Exact automatic result. Finite dead-position search is evaluated only if needed. -/
def automatic (game : Game) : Option Outcome :=
  if IsCheckmate (decodeGame game).current then some (.win game.current.turn.other)
  else if DrawCondition (decodeGame game) then some .draw else none

theorem automatic_some_iff (game : Game) (outcome : Outcome) :
    automatic game = some outcome ↔ AutomaticOutcome (decodeGame game) outcome := by
  unfold automatic
  split_ifs with mate draw
  · constructor
    · intro equal
      cases Option.some.inj equal
      exact .checkmate mate
    · intro given
      exact congrArg some (automatic_unique (.checkmate mate) given)
  · have automaticDraw := (drawCondition_iff mate).mp draw
    constructor
    · intro equal
      cases Option.some.inj equal
      exact automaticDraw
    · intro given
      exact congrArg some (automatic_unique automaticDraw given)
  · constructor
    · exact fun impossible ↦ impossible.elim
    · intro given
      cases given with
      | checkmate h => exact (mate h).elim
      | stalemate h => exact (draw (Or.inl h)).elim
      | deadPosition h => exact (draw (Or.inr (Or.inr (Or.inr h)))).elim
      | fivefoldRepetition _ h => exact (draw (Or.inr (Or.inl h))).elim
      | seventyFiveMoveRule _ h => exact (draw (Or.inr (Or.inr (Or.inl h)))).elim

theorem automatic_none_iff (game : Game) :
    automatic game = none ↔ ¬∃ outcome, AutomaticOutcome (decodeGame game) outcome := by
  simp only [← automatic_some_iff]
  cases automatic game <;> simp

instance (game : Chess.Game) (outcome : Outcome) : Decidable (AutomaticOutcome game outcome) :=
  decidable_of_iff (automatic (encodeGame game) = some outcome)
    (by simpa only [decode_encodeGame] using automatic_some_iff (encodeGame game) outcome)

/-- All legal raw moves, and a draw claim exactly when available, unless already terminal. -/
def legalActions (game : Game) : List Action :=
  if automatic game = none then
    (Exec.legalPlies game.current).map Action.play ++
      if canClaimDraw game then [.claimDraw] else []
  else []

@[simp] theorem mem_legalActions (game : Game) (action : Action) :
    action ∈ legalActions game ↔ IsLegalAction (decodeGame game) action := by
  cases action <;> simp [legalActions, IsLegalAction, automatic_none_iff, decodeGame]

theorem legalActions_nodup (game : Game) : (legalActions game).Nodup := by
  have mapped := (Exec.legalPlies_nodup game.current).map
    (fun a b h ↦ Action.play.inj h)
  unfold legalActions
  split_ifs <;> simp_all [List.nodup_append]

instance (game : Chess.Game) (action : Action) : Decidable (IsLegalAction game action) :=
  decidable_of_iff (action ∈ legalActions (encodeGame game))
    (by simpa only [decode_encodeGame] using mem_legalActions (encodeGame game) action)

theorem no_action_after_automatic {game : Chess.Game} {outcome : Outcome}
    (terminal : AutomaticOutcome game outcome) (action : Action) : ¬IsLegalAction game action := by
  cases action <;> exact fun legal ↦ legal.1 ⟨outcome, terminal⟩

theorem nonterminal_has_action (game : Chess.Game)
    (nonterminal : ¬∃ outcome, AutomaticOutcome game outcome) :
    ∃ action, IsLegalAction game action := by
  classical
  by_cases has : HasLegalPly game.current
  · obtain ⟨ply, legal⟩ := has
    exact ⟨.play ply, nonterminal, legal⟩
  · by_cases checked : InCheck game.current.board game.current.turn
    · exact (nonterminal ⟨_, .checkmate ⟨checked, has⟩⟩).elim
    · exact (nonterminal ⟨_, .stalemate ⟨checked, has⟩⟩).elim

end Chess.Adjudication
