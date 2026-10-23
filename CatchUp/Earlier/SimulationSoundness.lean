/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import CatchUp.Reference

/-!
# Soundness of Catch-Up strategy simulations

This module proves a solver-independent strategy-transfer theorem. A safe small-game position may
act as a ghost state while a related large-game strategy proceeds to a separately proved target or
terminal position.
-/

namespace CatchUp

/-- The change in player one's score lead when a player receives one counter. -/
def Player.scoreCoefficient : Player → ℤ
  | .p1 => 1
  | .p2 => -1

/-- Player one's score minus player two's score, reconstructed from a normalized position. -/
def GamePosition.p1ScoreBalance (position : GamePosition) : ℤ :=
  match position.toMove with
  | .p1 => -(position.deficit : ℤ)
  | .p2 => position.deficit

/-- Picking `x` changes player one's score lead by the signed value of `x`. -/
theorem GamePosition.p1_score_balance_after_pick (position : GamePosition) (x : ℕ) :
    (position.afterPick x).p1ScoreBalance =
      position.p1ScoreBalance + position.toMove.scoreCoefficient * (x : ℤ) := by
  cases hplayer : position.toMove <;> by_cases hx : x < position.deficit <;>
    simp [GamePosition.p1ScoreBalance, Player.scoreCoefficient, GamePosition.afterPick,
      Position.afterPick, Player.other, hplayer, hx] <;> omega

/--
An aligned ghost step that is safe by construction when `actor` is `player`.

If `actor` is the opponent, safety of the result follows from safety of `before`, because every
legal move from an adversarial node must remain safe. A stuttering step is always allowed.
-/
def GamePosition.AlignedSafeGhostStep
    (player actor : Player) (before after : GamePosition) : Prop :=
  after = before ∨
    before.toMove = actor ∧ ¬before.IsTerminal ∧
      ∃ x, ∃ _ : before.LegalMove x,
        after = before.afterPick x ∧ (actor = player → CanAvoidLoss player after)

/-- An aligned safe ghost step preserves the ability to avoid a loss. -/
theorem GamePosition.AlignedSafeGhostStep.can_avoid_loss
    {player actor : Player} {before after : GamePosition}
    (hstep : before.AlignedSafeGhostStep player actor after)
    (hbefore : CanAvoidLoss player before) :
    CanAvoidLoss player after := by
  rcases hstep with rfl | ⟨halign, hterminal, x, hx, rfl, howner⟩
  · exact hbefore
  by_cases hactor : actor = player
  · exact howner hactor
  have htoMove : before.toMove ≠ player := by
    intro h
    exact hactor (halign.symm.trans h)
  exact (can_avoid_loss_iff_forall_safe_moves player before hterminal htoMove).mp hbefore x hx

/--
Local obligations for transferring a non-losing strategy along a relation between a safe ghost
position and a simulated position.
-/
structure StrategySimulation
    (player : Player) (target : GamePosition → Prop)
    (rel : GamePosition → GamePosition → Prop) : Prop where
  target_safe : ∀ large, target large → CanAvoidLoss player large
  terminal_safe : ∀ small large,
    rel small large →
      CanAvoidLoss player small →
      ¬target large →
      large.IsTerminal →
      large.terminalOutcomeFor player ≠ .loss
  owner_exists : ∀ small large,
    rel small large →
      CanAvoidLoss player small →
      ¬target large →
      ¬large.IsTerminal →
      large.toMove = player →
      ∃ x, ∃ _ : large.LegalMove x, ∃ small',
        small.AlignedSafeGhostStep player large.toMove small' ∧
          rel small' (large.afterPick x)
  opponent_forall : ∀ small large,
    rel small large →
      CanAvoidLoss player small →
      ¬target large →
      ¬large.IsTerminal →
      large.toMove ≠ player →
      ∀ x, large.LegalMove x → ∃ small',
        small.AlignedSafeGhostStep player large.toMove small' ∧
          rel small' (large.afterPick x)

/-- A locally closed strategy simulation transfers ghost safety to the simulated position. -/
theorem StrategySimulation.can_avoid_loss
    {player : Player} {target : GamePosition → Prop}
    {rel : GamePosition → GamePosition → Prop}
    (simulation : StrategySimulation player target rel)
    (small large : GamePosition) (hrel : rel small large)
    (hsmall : CanAvoidLoss player small) :
    CanAvoidLoss player large := by
  induction large using
      (measure fun position : GamePosition => position.remaining.card).wf.induction
      generalizing small with
  | h large ih =>
      by_cases htarget : target large
      · exact simulation.target_safe large htarget
      by_cases hterminal : large.IsTerminal
      · rw [can_avoid_loss_iff_terminal_outcome_ne_loss player large hterminal]
        exact simulation.terminal_safe small large hrel hsmall htarget hterminal
      by_cases howner : large.toMove = player
      · rw [can_avoid_loss_iff_exists_safe_move player large hterminal howner]
        obtain ⟨x, hx, small', hghost, hrel'⟩ :=
          simulation.owner_exists small large hrel hsmall htarget hterminal howner
        refine ⟨x, hx, ?_⟩
        exact ih (large.afterPick x) (large.remaining_card_after_pick_lt x hx)
          small' hrel' (hghost.can_avoid_loss hsmall)
      · rw [can_avoid_loss_iff_forall_safe_moves player large hterminal howner]
        intro x hx
        obtain ⟨small', hghost, hrel'⟩ :=
          simulation.opponent_forall small large hrel hsmall htarget hterminal howner x hx
        exact ih (large.afterPick x) (large.remaining_card_after_pick_lt x hx)
          small' hrel' (hghost.can_avoid_loss hsmall)

/--
Local strategy-simulation obligations for an arbitrary ghost state carrying persistent auxiliary
data. The `advance` proof is logically irrelevant to soundness but records the transition invariant
that a concrete simulation must preserve.
-/
structure GhostStrategySimulation
    (Ghost : Type) (player : Player) (target : GamePosition → Prop)
    (safe : Ghost → Prop) (advance : Ghost → GamePosition → ℕ → Ghost → Prop)
    (rel : Ghost → GamePosition → Prop) : Prop where
  target_safe : ∀ large, target large → CanAvoidLoss player large
  terminal_safe : ∀ ghost large,
    rel ghost large → safe ghost → ¬target large → large.IsTerminal →
      large.terminalOutcomeFor player ≠ .loss
  owner_exists : ∀ ghost large,
    rel ghost large → safe ghost → ¬target large → ¬large.IsTerminal →
      large.toMove = player →
      ∃ x, ∃ _ : large.LegalMove x, ∃ ghost',
        safe ghost' ∧ advance ghost large x ghost' ∧ rel ghost' (large.afterPick x)
  opponent_forall : ∀ ghost large,
    rel ghost large → safe ghost → ¬target large → ¬large.IsTerminal →
      large.toMove ≠ player →
      ∀ x, large.LegalMove x → ∃ ghost',
        safe ghost' ∧ advance ghost large x ghost' ∧ rel ghost' (large.afterPick x)

/-- A locally closed simulation with persistent ghost data gives a non-losing large strategy. -/
theorem GhostStrategySimulation.can_avoid_loss
    {Ghost : Type} {player : Player} {target : GamePosition → Prop}
    {safe : Ghost → Prop} {advance : Ghost → GamePosition → ℕ → Ghost → Prop}
    {rel : Ghost → GamePosition → Prop}
    (simulation : GhostStrategySimulation Ghost player target safe advance rel)
    (ghost : Ghost) (large : GamePosition) (hrel : rel ghost large) (hsafe : safe ghost) :
    CanAvoidLoss player large := by
  induction large using
      (measure fun position : GamePosition => position.remaining.card).wf.induction
      generalizing ghost with
  | h large ih =>
      by_cases htarget : target large
      · exact simulation.target_safe large htarget
      by_cases hterminal : large.IsTerminal
      · rw [can_avoid_loss_iff_terminal_outcome_ne_loss player large hterminal]
        exact simulation.terminal_safe ghost large hrel hsafe htarget hterminal
      by_cases howner : large.toMove = player
      · rw [can_avoid_loss_iff_exists_safe_move player large hterminal howner]
        obtain ⟨x, hx, ghost', hsafe', _, hrel'⟩ :=
          simulation.owner_exists ghost large hrel hsafe htarget hterminal howner
        refine ⟨x, hx, ?_⟩
        exact ih (large.afterPick x) (large.remaining_card_after_pick_lt x hx)
          ghost' hrel' hsafe'
      · rw [can_avoid_loss_iff_forall_safe_moves player large hterminal howner]
        intro x hx
        obtain ⟨ghost', hsafe', _, hrel'⟩ :=
          simulation.opponent_forall ghost large hrel hsafe htarget hterminal howner x hx
        exact ih (large.afterPick x) (large.remaining_card_after_pick_lt x hx)
          ghost' hrel' hsafe'

end CatchUp
