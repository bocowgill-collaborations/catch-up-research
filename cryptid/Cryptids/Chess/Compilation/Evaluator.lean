/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Evaluation.Solver

/-!
# First-order fuelled evaluation of full chess games

Fuel exhaustion is explicit. The executed recursion uses the exact adjudication procedures
and retains the entire raw game. The finite-key rank appears only in correctness proofs.
This source refinement does not assert a translation to a Turing-machine program.
-/

@[expose] public section
namespace Chess.Compilation.Evaluator
open Adjudication Evaluation

/-- Prefer the first value on a tie, using the current player's ordering. -/
def better (color : Color) (first second : Outcome) : Outcome :=
  if utility color second ≤ utility color first then first else second

mutual
  /-- Exact backward induction with an explicit exhaustion result. -/
  def evaluate (fuel : ℕ) (game : Adjudication.Game) : Option Outcome :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match automatic game with
      | some outcome => some outcome
      | none => evaluateActions fuel game (legalActions game)
  termination_by (fuel, 0)

  /-- A first-order, value-only fold over an ordinary list of actions. -/
  def evaluateActions (fuel : ℕ) (game : Adjudication.Game)
      (actions : List Action) : Option Outcome :=
    match actions with
    | [] => none
    | action :: rest =>
      let result := match action with
        | .claimDraw => some Outcome.draw
        | .play ply => evaluate fuel (game.play ply)
      match result with
      | none => none
      | some first =>
        match rest with
        | [] => some first
        | next :: tail =>
          match evaluateActions fuel game (next :: tail) with
          | none => none
          | some second => some (better game.current.turn first second)
  termination_by (fuel, actions.length + 1)
end

@[simp] theorem evaluate_zero (game : Adjudication.Game) : evaluate 0 game = none := by
  simp [evaluate]

@[simp] theorem evaluateActions_nil (fuel : ℕ) (game : Adjudication.Game) :
    evaluateActions fuel game [] = none := by
  simp [evaluateActions]

/-- Positive fuel immediately preserves any automatic outcome. -/
theorem evaluate_terminal (fuel : ℕ) (game : Adjudication.Game) (outcome : Outcome)
    (terminal : automatic game = some outcome) : evaluate (fuel + 1) game = some outcome := by
  simp [evaluate, terminal]

/-- The outcome fold used only to relate ordinary values to M4's maximizing choice. -/
def foldValues (color : Color) (first : Outcome) (rest : List Outcome) : Outcome :=
  match rest with
  | [] => first
  | next :: rest => better color first (foldValues color next rest)

theorem choose_foldValues {α : Type} (color : Color) (value : α → Outcome)
    (first : α) (rest : List α) :
    value (choose color value first rest) = foldValues color (value first) (rest.map value) := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
    simp only [choose, List.map_cons, foldValues, better]
    simp only [apply_ite value, ih]

theorem better_duplicate (color : Color) (first second : Outcome) :
    better color first (better color first second) = better color first second := by
  unfold better
  split_ifs <;> simp_all

theorem better_foldValues (color : Color) (first : Outcome) (rest : List Outcome) :
    better color first (foldValues color first rest) = foldValues color first rest := by
  cases rest with
  | nil => simp [foldValues, better]
  | cons next rest => exact better_duplicate _ _ _

theorem solve_foldValues (game : Adjudication.Game) (live : automatic game = none)
    (first : Action) (rest : List Action) (actions : legalActions game = first :: rest) :
    solve game = foldValues game.current.turn (actionValue game first)
      (rest.map (actionValue game)) := by
  rw [solve, analyse_live game live]
  change (fun a : {a // a ∈ legalActions game} ↦ actionValue game a.val)
    (bestAction game live) = _
  unfold bestAction
  refine (choose_foldValues game.current.turn
    (fun a : {a // a ∈ legalActions game} ↦ actionValue game a.val) _ _).trans ?_
  simp only [List.attach_map_val, actions, List.head_cons, List.map_cons, foldValues]
  exact better_foldValues _ _ _

theorem evaluateActions_correct (fuel : ℕ) (game : Adjudication.Game)
    (children : ∀ ply, evaluate fuel (game.play ply) = some (solve (game.play ply)))
    (first : Action) (rest : List Action) :
    evaluateActions fuel game (first :: rest) =
      some (foldValues game.current.turn (actionValue game first)
        (rest.map (actionValue game))) := by
  induction rest generalizing first with
  | nil =>
    cases first <;> simp [evaluateActions, actionValue, foldValues, children]
  | cons next rest ih =>
    cases first <;> simp [evaluateActions, actionValue, foldValues, children, ih]

/-- Any fuel strictly above M4's proof-only rank returns its exact value, on every raw game. -/
theorem evaluate_correct (fuel : ℕ) (game : Adjudication.Game) (enough : rank game < fuel) :
    evaluate fuel game = some (solve game) := by
  induction fuel generalizing game with
  | zero => omega
  | succ fuel ih =>
    cases terminal : automatic game with
    | some outcome =>
      simp [evaluate, terminal, solve_terminal game outcome terminal]
    | none =>
      have children (ply : Ply) : evaluate fuel (game.play ply) = some (solve (game.play ply)) :=
        ih _ (by have lower := rank_play_lt game ply terminal; omega)
      obtain ⟨first, rest, actions⟩ := List.exists_cons_of_ne_nil (actions_nonempty game terminal)
      simpa only [evaluate, terminal, actions, solve_foldValues game terminal first rest actions]
        using evaluateActions_correct fuel game children first rest

/-- Executable count of raw clock-free keys; no key enumeration is performed. -/
def keyBound : ℕ := 13 ^ 64 * 2 * 16 * 65

/-- An executable uniform fuel amount, independent of the full input history. -/
def uniformFuel : ℕ := 8 * keyBound + 2

/-- The raw key space fits the literal count of boards, turns, rights, and raw EP targets. -/
theorem key_card_le : Nat.card Key ≤ keyBound := by
  let flatten (key : Key) :=
    (key.board, key.turn, key.castlingRights.whiteKingside,
      key.castlingRights.whiteQueenside, key.castlingRights.blackKingside,
      key.castlingRights.blackQueenside, key.enPassantTarget)
  have injective : Function.Injective flatten := by
    intro a b equal
    cases a with | mk ab aturn ar ae =>
      cases b with | mk bb bt br be =>
        cases ar
        cases br
        simpa only [flatten, Prod.mk.injEq, Key.mk.injEq,
          CastlingRights.mk.injEq, and_assoc] using equal
  have bound := Nat.card_le_card_of_injective flatten injective
  have colorCard : Nat.card Color = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have cellCard : Nat.card (Option Piece) = 13 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have squareCard : Nat.card Square = 64 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have epCard : Nat.card (Option Square) = 65 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have boolCard : Nat.card Bool = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  simpa only [Nat.card_prod, Board, Nat.card_fun, colorCard, cellCard, squareCard, epCard,
    boolCard, keyBound, Nat.mul_assoc, show 2 * (2 * (2 * (2 * 65))) = 16 * 65 by decide]
    using bound

/-- The numerical fuel is strictly above every full-history rank. -/
theorem rank_lt_uniformFuel (game : Adjudication.Game) : rank game < uniformFuel := by
  have rankBound := rank_le game
  have cardBound := key_card_le
  unfold uniformFuel
  omega

/-- Uniform first-order evaluation agrees with unchanged M4 on every raw game. -/
theorem evaluate_uniform (game : Adjudication.Game) :
    evaluate uniformFuel game = some (solve game) :=
  evaluate_correct uniformFuel game (rank_lt_uniformFuel game)

end Chess.Compilation.Evaluator
