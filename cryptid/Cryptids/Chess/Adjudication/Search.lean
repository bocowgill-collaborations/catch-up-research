/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Exec

/-!
# Exact finite directed-graph search

Search grows the set of discovered vertices until it finds a target or reaches a fixed point.
Finiteness is used only in the termination proof: the executable code enumerates successors,
not the entire vertex type. No caller-supplied fuel or unproved search cutoff is used.
-/

@[expose] public section
namespace Chess.Adjudication.FiniteSearch
open Relation

variable {α : Type} [DecidableEq α]

/-- The directed edge relation specified by an executable successor list. -/
def Edge (next : α → List α) (a b : α) : Prop := b ∈ next a

/-- A target is reachable from one of the currently discovered vertices. -/
def CanReach (next : α → List α) (target : α → Bool) (seen : Finset α) : Prop :=
  ∃ a ∈ seen, ∃ b, ReflTransGen (Edge next) a b ∧ target b = true

/-- Add every immediate successor, retaining all previously discovered vertices. -/
def expand (next : α → List α) (seen : Finset α) : Finset α :=
  seen ∪ seen.biUnion (fun a ↦ (next a).toFinset)

theorem subset_expand (next : α → List α) (seen : Finset α) : seen ⊆ expand next seen :=
  Finset.subset_union_left

theorem expand_preserves (next : α → List α) (target : α → Bool) (seen : Finset α) :
    CanReach next target (expand next seen) ↔ CanReach next target seen := by
  exact ⟨fun ⟨a, ha, b, path, hb⟩ ↦ (Finset.mem_union.mp ha).elim
    (fun ha ↦ ⟨a, ha, b, path, hb⟩)
    (fun ha ↦ (Finset.mem_biUnion.mp ha).elim fun c ⟨hc, hca⟩ ↦
      ⟨c, hc, b, (ReflTransGen.single (List.mem_toFinset.mp hca)).trans path, hb⟩),
    fun ⟨a, ha, b, path, hb⟩ ↦ ⟨a, subset_expand next seen ha, b, path, hb⟩⟩

theorem closed_contains (next : α → List α) (seen : Finset α)
    (closed : expand next seen ⊆ seen) {a b : α} (ha : a ∈ seen)
    (path : ReflTransGen (Edge next) a b) : b ∈ seen := by
  induction path with
  | refl => exact ha
  | tail path edge ih =>
      exact closed (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨_, ih, List.mem_toFinset.mpr edge⟩))

theorem no_target_closed (next : α → List α) (target : α → Bool) (seen : Finset α)
    (absent : ¬∃ a ∈ seen, target a = true) (closed : expand next seen ⊆ seen) :
    ¬CanReach next target seen :=
  fun ⟨_, ha, _, path, hb⟩ ↦ absent ⟨_, closed_contains next seen closed ha path, hb⟩

/-- Exact finite search. The finite-cardinality measure is erased from executable code. -/
def search [Finite α] (next : α → List α) (target : α → Bool) (seen : Finset α) :
    {answer : Bool // answer = true ↔ CanReach next target seen} :=
  if found : ∃ a ∈ seen, target a = true then
    ⟨true, ⟨fun _ ↦ found.elim fun a ⟨ha, ht⟩ ↦ ⟨a, ha, a, .refl, ht⟩, fun _ ↦ rfl⟩⟩
  else if closed : expand next seen ⊆ seen then
    ⟨false, ⟨fun h ↦ (Bool.false_ne_true h).elim,
      fun h ↦ (no_target_closed next target seen found closed h).elim⟩⟩
  else
    let result := search next target (expand next seen)
    ⟨result.val, result.property.trans (expand_preserves next target seen)⟩
termination_by Nat.card α - seen.card
decreasing_by
  let _ := Fintype.ofFinite α
  have grow : seen.card < (expand next seen).card :=
    Finset.card_lt_card ⟨subset_expand next seen, closed⟩
  have bound : (expand next seen).card ≤ Nat.card α := by
    simpa only [Nat.card_eq_fintype_card] using Finset.card_le_univ (expand next seen)
  omega

/-- Search from one starting vertex. -/
def reachableTarget [Finite α] (next : α → List α) (target : α → Bool) (start : α) : Bool :=
  (search next target {start}).val

theorem reachableTarget_iff [Finite α] (next : α → List α) (target : α → Bool) (start : α) :
    reachableTarget next target start = true ↔
      ∃ finish, ReflTransGen (Edge next) start finish ∧ target finish = true := by
  simpa only [reachableTarget, CanReach, Finset.mem_singleton, exists_eq_left] using
    (search next target {start}).property

end Chess.Adjudication.FiniteSearch
