/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Compilation.Evaluator

/-!
# Value-preserving deferral of dead-position termination

The evaluator omits only the dead-position automatic test. All other automatic results,
legal plies, optional claims, and full-history updates remain exact. A proof shows that
continuing a dead game produces only draw values before the finite repetition bound.
This is a source refinement; it contains no claim of actual machine-code translation.
-/

@[expose] public section
namespace Chess.Compilation.WithoutDead
open Adjudication Evaluation

/-- Automatic draw conditions with only the dead-position test deferred. -/
def DrawConditionWithoutDead (game : Chess.Game) : Prop :=
  IsStalemate game.current ∨ game.RepeatedAtLeast 5 ∨ 150 ≤ game.current.halfmoveClock

instance (game : Chess.Game) : Decidable (DrawConditionWithoutDead game) := by
  unfold DrawConditionWithoutDead
  infer_instance

/-- Checkmate keeps priority; all automatic draws other than dead position are tested. -/
def automaticWithoutDead (game : Adjudication.Game) : Option Outcome :=
  if IsCheckmate (decodeGame game).current then some (.win game.current.turn.other)
  else if DrawConditionWithoutDead (decodeGame game) then some .draw else none

/-- Actions use this evaluator's live gate and the unchanged move/claim procedures. -/
def legalActions (game : Adjudication.Game) : List Action :=
  if automaticWithoutDead game = none then
    (Exec.legalPlies game.current).map Action.play ++
      if canClaimDraw game then [.claimDraw] else []
  else []

/-- Deadness is hereditary along every raw legal-ply continuation. -/
theorem dead_closed {source target : Chess.Position} (dead : IsDeadPosition source)
    (path : Relation.ReflTransGen Chess.Position.Next source target) : IsDeadPosition target := by
  intro finish continuation
  exact dead finish (path.trans continuation)

/-- A legal move from a dead game retains deadness without imposing a history invariant. -/
theorem dead_play (game : Adjudication.Game) (ply : Ply)
    (dead : IsDeadPosition (decodeGame game).current)
    (legal : IsLegalPly (decodeGame game).current ply) :
    IsDeadPosition (decodeGame (game.play ply)).current := by
  rw [decode_play]
  exact dead_closed dead (Relation.ReflTransGen.single ⟨ply, legal, rfl⟩)

theorem automatic_none_iff (game : Adjudication.Game) :
    automaticWithoutDead game = none ↔
      ¬IsCheckmate (decodeGame game).current ∧ ¬DrawConditionWithoutDead (decodeGame game) := by
  simp only [automaticWithoutDead]
  split_ifs <;> simp_all

/-- Deferring deadness changes no automatic result at a nondead raw game. -/
theorem automatic_eq_of_not_dead (game : Adjudication.Game)
    (notDead : ¬IsDeadPosition (decodeGame game).current) :
    automaticWithoutDead game = Adjudication.automatic game := by
  simp [automaticWithoutDead, Adjudication.automatic, DrawConditionWithoutDead,
    Adjudication.DrawCondition, notDead]

theorem legalActions_eq_of_not_dead (game : Adjudication.Game)
    (notDead : ¬IsDeadPosition (decodeGame game).current) :
    legalActions game = Adjudication.legalActions game := by
  simp only [legalActions, Adjudication.legalActions, automatic_eq_of_not_dead game notDead]

/-- No deferred automatic result can be a win at a dead position. -/
theorem dead_not_win (game : Adjudication.Game)
    (dead : IsDeadPosition (decodeGame game).current) (color : Color) :
    automaticWithoutDead game ≠ some (.win color) := by
  simp only [automaticWithoutDead, ite_eq_right (dead_not_checkmate dead)]
  split_ifs <;> simp

theorem dead_automatic_value (game : Adjudication.Game)
    (dead : IsDeadPosition (decodeGame game).current) (outcome : Outcome)
    (terminal : automaticWithoutDead game = some outcome) : outcome = .draw := by
  cases outcome with
  | draw => rfl
  | win color => exact (dead_not_win game dead color terminal).elim

@[simp] theorem mem_legalActions_play (game : Adjudication.Game) (ply : Ply) :
    .play ply ∈ legalActions game ↔
      automaticWithoutDead game = none ∧ IsLegalPly (decodeGame game).current ply := by
  by_cases live : automaticWithoutDead game = none <;>
    simp [legalActions, live, Exec.mem_legalPlies, decodeGame]

@[simp] theorem mem_legalActions_claim (game : Adjudication.Game) :
    .claimDraw ∈ legalActions game ↔
      automaticWithoutDead game = none ∧ CanClaimDraw (decodeGame game) := by
  by_cases live : automaticWithoutDead game = none <;>
    simp [legalActions, live, List.mem_map]

theorem actions_nonempty (game : Adjudication.Game) (live : automaticWithoutDead game = none) :
    legalActions game ≠ [] := by
  have conditions := (automatic_none_iff game).mp live
  by_cases has : HasLegalPly (decodeGame game).current
  · obtain ⟨ply, legal⟩ := has
    exact List.ne_nil_of_mem ((mem_legalActions_play game ply).mpr ⟨live, legal⟩)
  · by_cases checked : InCheck (decodeGame game).current.board (decodeGame game).current.turn
    · exact (conditions.1 ⟨checked, has⟩).elim
    · exact (conditions.2 (Or.inl ⟨checked, has⟩)).elim

/-- Omitting deadness does not weaken the fifth-occurrence stopping condition. -/
theorem nonterminal_count (game : Adjudication.Game) (live : automaticWithoutDead game = none) :
    (keys game).count (project (decodeGame game).current) < 5 := by
  by_contra! five
  have repeated := (repeated_iff_occurrences (decodeGame game) 5).mpr
    (five.trans (key_count_le_occurrences game))
  exact ((automatic_none_iff game).mp live).2 (Or.inr (Or.inl repeated))

/-- Proof-only capacity rank with this evaluator's own terminal bit. -/
noncomputable def rankNoDead (game : Adjudication.Game) : ℕ :=
  2 * capacity (keys game) + if automaticWithoutDead game = none then 1 else 0

theorem rankNoDead_le (game : Adjudication.Game) : rankNoDead game ≤ 8 * Nat.card Key + 1 := by
  have bound := capacity_le (keys game)
  unfold rankNoDead
  split_ifs <;> omega

theorem rankNoDead_play_lt (game : Adjudication.Game) (ply : Ply)
    (live : automaticWithoutDead game = none) : rankNoDead (game.play ply) < rankNoDead game := by
  have monotone := capacity_cons_le (keys game)
    (project (Exec.decode (Exec.applyPly game.current ply)))
  by_cases nextLive : automaticWithoutDead (game.play ply) = none
  · have count := nonterminal_count (game.play ply) nextLive
    have strict := capacity_cons_lt (keys game)
      (project (Exec.decode (Exec.applyPly game.current ply))) (by
        change (keys (game.play ply)).count
          (project (Exec.decode (Exec.applyPly game.current ply))) < 5 at count
        rw [keys_play, List.count_cons_self] at count
        omega)
    simp only [rankNoDead, live, nextLive, ite_true, keys_play]
    omega
  · simp only [rankNoDead, live, nextLive, ite_true, ite_false, keys_play]
    omega

mutual
  /-- Fuelled value evaluation that defers only dead-position automatic termination. -/
  def evaluate (fuel : ℕ) (game : Adjudication.Game) : Option Outcome :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match automaticWithoutDead game with
      | some outcome => some outcome
      | none => evaluateActions fuel game (legalActions game)
  termination_by (fuel, 0)

  /-- A first-order fold; any exhausted played child propagates failure. -/
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
          | some second => some (Evaluator.better game.current.turn first second)
  termination_by (fuel, actions.length + 1)
end

@[simp] theorem evaluate_zero (game : Adjudication.Game) : evaluate 0 game = none := by
  simp [evaluate]

@[simp] theorem evaluateActions_nil (fuel : ℕ) (game : Adjudication.Game) :
    evaluateActions fuel game [] = none := by
  simp [evaluateActions]

/-- A list consisting entirely of draw-valued actions folds to draw. -/
theorem evaluateActions_draw (fuel : ℕ) (game : Adjudication.Game) (actions : List Action)
    (nonempty : actions ≠ [])
    (values : ∀ action ∈ actions, (match action with
      | .claimDraw => some Outcome.draw
      | .play ply => evaluate fuel (game.play ply)) = some .draw) :
    evaluateActions fuel game actions = some .draw := by
  induction actions with
  | nil => exact (nonempty rfl).elim
  | cons first rest ih =>
    have firstValue := values first (List.mem_cons_self)
    cases rest with
    | nil => cases first <;> simp_all [evaluateActions]
    | cons next rest =>
      have tailValue := ih (by simp) (fun action member ↦
        values action (List.mem_cons_of_mem _ member))
      cases first <;> simp_all [evaluateActions, Evaluator.better]

/-- Legal continuation from a dead game returns a draw, using the evaluator's own rank. -/
theorem evaluate_dead (fuel : ℕ) (game : Adjudication.Game)
    (dead : IsDeadPosition (decodeGame game).current) (enough : rankNoDead game < fuel) :
    evaluate fuel game = some .draw := by
  induction fuel generalizing game with
  | zero => omega
  | succ fuel ih =>
    cases terminal : automaticWithoutDead game with
    | some outcome =>
      simp [evaluate, terminal, dead_automatic_value game dead outcome terminal]
    | none =>
      have values (action : Action) (member : action ∈ legalActions game) :
          (match action with
            | .claimDraw => some Outcome.draw
            | .play ply => evaluate fuel (game.play ply)) = some .draw := by
        cases action with
        | claimDraw => rfl
        | play ply =>
          exact ih _ (dead_play game ply dead ((mem_legalActions_play game ply).mp member).2)
            (by have lower := rankNoDead_play_lt game ply terminal; omega)
      simpa only [evaluate, terminal] using
        evaluateActions_draw fuel game (legalActions game) (actions_nonempty game terminal) values

theorem evaluateActions_correct (fuel : ℕ) (game : Adjudication.Game)
    (children : ∀ ply, evaluate fuel (game.play ply) = some (solve (game.play ply)))
    (first : Action) (rest : List Action) :
    evaluateActions fuel game (first :: rest) =
      some (Evaluator.foldValues game.current.turn (actionValue game first)
        (rest.map (actionValue game))) := by
  induction rest generalizing first with
  | nil =>
    cases first <;> simp [evaluateActions, actionValue, Evaluator.foldValues, children]
  | cons next rest ih =>
    cases first <;> simp [evaluateActions, actionValue, Evaluator.foldValues, children, ih]

/-- Deferring dead-position termination preserves unchanged M4's value at every raw game. -/
theorem evaluate_correct (fuel : ℕ) (game : Adjudication.Game) (enough : rankNoDead game < fuel) :
    evaluate fuel game = some (solve game) := by
  induction fuel generalizing game with
  | zero => omega
  | succ fuel ih =>
    by_cases dead : IsDeadPosition (decodeGame game).current
    · have terminal := (Adjudication.automatic_some_iff game .draw).mpr
        (AutomaticOutcome.deadPosition dead)
      simpa only [solve_terminal game .draw terminal] using
        evaluate_dead (fuel + 1) game dead enough
    · cases terminal : automaticWithoutDead game with
      | some outcome =>
        have oldTerminal := (automatic_eq_of_not_dead game dead).symm.trans terminal
        simp [evaluate, terminal, solve_terminal game outcome oldTerminal]
      | none =>
        have oldLive := (automatic_eq_of_not_dead game dead).symm.trans terminal
        have children (ply : Ply) : evaluate fuel (game.play ply) = some (solve (game.play ply)) :=
          ih _ (by have lower := rankNoDead_play_lt game ply terminal; omega)
        obtain ⟨first, rest, actions⟩ := List.exists_cons_of_ne_nil
          (Evaluation.actions_nonempty game oldLive)
        have ownActions := (legalActions_eq_of_not_dead game dead).trans actions
        simpa only [evaluate, terminal, ownActions,
          Evaluator.solve_foldValues game oldLive first rest actions] using
          evaluateActions_correct fuel game children first rest

/-- The same executable numerical fuel as the exact source evaluator. -/
def uniformFuel : ℕ := Evaluator.uniformFuel

theorem rankNoDead_lt_uniformFuel (game : Adjudication.Game) : rankNoDead game < uniformFuel := by
  have rankBound := rankNoDead_le game
  have cardBound := Evaluator.key_card_le
  unfold uniformFuel Evaluator.uniformFuel
  omega

/-- The deferred evaluator agrees unconditionally with unchanged M4 on every raw game. -/
theorem evaluate_uniform (game : Adjudication.Game) :
    evaluate uniformFuel game = some (solve game) :=
  evaluate_correct uniformFuel game (rankNoDead_lt_uniformFuel game)

/-- Every adequately fuelled evaluation of a dead game excludes either player's win. -/
theorem dead_evaluate_not_win (fuel : ℕ) (game : Adjudication.Game)
    (dead : IsDeadPosition (decodeGame game).current) (enough : rankNoDead game < fuel)
    (color : Color) : evaluate fuel game ≠ some (.win color) := by
  rw [evaluate_dead fuel game dead enough]
  simp

end Chess.Compilation.WithoutDead
