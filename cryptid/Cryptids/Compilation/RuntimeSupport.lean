/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.Runtime

/-! # Finite support of the fixed four-stack runtime

The ordered labels are independent of source Code and serialized input. Only return
dispatch differs from Mathlib's primitive macro machine.
-/

@[expose] public section
namespace ConjectureMachines.Compilation.RuntimeSupport
open Turing PartrecToTM2 K'

set_option backward.isDefEq.respectTransparency false

/-- Ordered macro descendants remain closed under taking descendants. -/
theorem trStmtsList_closed {first second : Λ'}
    (member : second ∈ CodeBackend.trStmtsList first) (third : Λ')
    (descendant : third ∈ CodeBackend.trStmtsList second) :
    third ∈ CodeBackend.trStmtsList first := by
  apply List.mem_toFinset.mp
  rw [CodeBackend.trStmtsList_toFinset]
  apply trStmts₁_trans (q := first) (q' := second)
  · simpa only [← CodeBackend.trStmtsList_toFinset, List.mem_toFinset] using member
  · simpa only [← CodeBackend.trStmtsList_toFinset, List.mem_toFinset] using descendant

/-- Every non-return macro jumps only to its listed descendants. -/
theorem nonreturn_supports (support : Finset Λ') (q : Λ')
    (included : trStmts₁ q ⊆ support) (nonreturn : ∀ k, q ≠ .ret k) :
    TM2.SupportsStmt support (Runtime.machine q) := by
  cases q <;> simp_all only [trStmts₁, unrev, Finset.union_insert,
    Finset.insert_subset_iff, Finset.union_subset_iff, Finset.biUnion_subset_iff_forall_subset,
    Finset.mem_univ, Finset.singleton_subset_iff, ne_eq, reduceCtorEq, not_false_eq_true,
    implies_true, Runtime.machine, tr, pop', push', peek', natEnd, default_Γ',
    TM2.SupportsStmt, forall_const, and_self, and_true, true_and, Λ'.ret.injEq, forall_eq']
  all_goals first
    | exact included.2 (trStmts₁_self _)
    | exact fun value ↦ included.2 value (trStmts₁_self _)
    | exact included.2.2.1 (trStmts₁_self _)

/-- A structural condition on every return leaf, ignoring non-return macro wrappers. -/
def ReturnLeaves (property : Cont' → Prop) : Λ' → Prop
  | .move _ _ _ next | .clear _ _ next | .copy next | .push _ _ next | .succ next =>
    ReturnLeaves property next
  | .read next => ∀ value, ReturnLeaves property (next value)
  | .pred zero successor => ReturnLeaves property zero ∧ ReturnLeaves property successor
  | .ret continuation => property continuation

/-- Synthetic unrev descendants contain no extra return leaves. -/
theorem return_leaf (property : Cont' → Prop) (q : Λ') (leaves : ReturnLeaves property q)
    (continuation : Cont') (member : Λ'.ret continuation ∈ CodeBackend.trStmtsList q) :
    property continuation := by
  induction q <;> simp_all only [ReturnLeaves, CodeBackend.trStmtsList, unrev,
    List.mem_cons, reduceCtorEq, false_or, List.mem_flatMap, CodeBackend.mem_stores,
    true_and, forall_const, List.mem_append, Λ'.ret.injEq, List.not_mem_nil, or_false]
  case read next ih =>
    obtain ⟨value, member⟩ := member
    exact ih value member
  case pred first second left right => exact member.elim left right

/-- Constant-symbol wrappers preserve the return leaves regardless of data size. -/
theorem returnLeaves_pushSymbols (property : Cont' → Prop) (dst : K')
    (symbols : List Γ') (next : Λ') :
    ReturnLeaves property (Runtime.pushSymbols dst symbols next) ↔ ReturnLeaves property next := by
  induction symbols generalizing next with
  | nil => rfl
  | cons symbol symbols ih =>
    exact ih (.push dst (fun _ ↦ some symbol) next)

/-- The only continuation syntax present in fixed phase bodies encodes a phase number. -/
def PhaseReturn (continuation : Cont') : Prop :=
  ∃ phase : Runtime.Phase, continuation = Runtime.returnCode (Runtime.phaseCode phase)

theorem label_returnLeaves (phase : Runtime.Phase) :
    ReturnLeaves PhaseReturn (Runtime.label phase) := ⟨phase, rfl⟩

/-- Each of the twenty concrete bodies returns only to declared phase roots. -/
theorem entry_returnLeaves (phase : Runtime.Phase) :
    ReturnLeaves PhaseReturn (Runtime.entry phase) := by
  cases phase <;> simp [Runtime.entry, Runtime.moveWord, Runtime.moveWord.unrevTo,
    Runtime.copyWord, Runtime.copyValues, Runtime.discardWord, Runtime.choose,
    Runtime.pushWord, returnLeaves_pushSymbols, ReturnLeaves, label_returnLeaves,
    move₂, moveExcl, head, unrev, ite_apply, apply_ite]

/-- Every return leaf of a fixed body is one of the fixed root labels. -/
theorem entry_return_label (phase : Runtime.Phase) (continuation : Cont')
    (member : Λ'.ret continuation ∈ CodeBackend.trStmtsList (Runtime.entry phase)) :
    ∃ target : Runtime.Phase, Λ'.ret continuation = Runtime.label target := by
  obtain ⟨target, equal⟩ := return_leaf PhaseReturn _ (entry_returnLeaves phase) _ member
  exact ⟨target, congrArg Λ'.ret equal⟩

theorem trStmtsList_self (q : Λ') : q ∈ CodeBackend.trStmtsList q := by
  simpa only [← CodeBackend.trStmtsList_toFinset, List.mem_toFinset] using trStmts₁_self q

theorem label_mem (phase : Runtime.Phase) : Runtime.label phase ∈ Runtime.labels := by
  exact List.mem_flatMap.mpr ⟨phase, Runtime.phases_cover phase, List.mem_cons_self⟩

theorem descendant_mem (phase : Runtime.Phase) (q : Λ')
    (member : q ∈ CodeBackend.trStmtsList (Runtime.entry phase)) : q ∈ Runtime.labels := by
  exact List.mem_flatMap.mpr ⟨phase, Runtime.phases_cover phase, List.mem_cons_of_mem _ member⟩

theorem entry_mem (phase : Runtime.Phase) : Runtime.entry phase ∈ Runtime.labels :=
  descendant_mem phase _ (trStmtsList_self _)

/-- Even malformed return numbers dispatch to a declared phase or the invalid phase. -/
theorem return_supports (continuation : Cont') :
    TM2.SupportsStmt Runtime.labels.toFinset (Runtime.machine (.ret continuation)) := by
  simp only [Runtime.machine]
  split_ifs
  · trivial
  · exact fun _ ↦ List.mem_toFinset.mpr (entry_mem _)

/-- Every listed macro instruction is closed under the actual overridden return machine. -/
theorem label_supports (q : Λ') (member : q ∈ Runtime.labels) :
    TM2.SupportsStmt Runtime.labels.toFinset (Runtime.machine q) := by
  obtain ⟨phase, _, member⟩ := List.mem_flatMap.mp member
  rcases List.mem_cons.mp member with root | member
  · rw [root]
    exact return_supports _
  · by_cases returned : ∃ continuation, q = Λ'.ret continuation
    · obtain ⟨continuation, rfl⟩ := returned
      exact return_supports continuation
    · apply nonreturn_supports
      · intro descendant found
        have foundList : descendant ∈ CodeBackend.trStmtsList q := by
          simpa only [← CodeBackend.trStmtsList_toFinset, List.mem_toFinset] using found
        exact List.mem_toFinset.mpr
          (descendant_mem phase descendant (trStmtsList_closed member descendant foundList))
      · exact fun continuation equal ↦ returned ⟨continuation, equal⟩

/-- The fixed ordered support, using the startup root as the machine's default label. -/
theorem supports :
    letI : Inhabited Λ' := ⟨Runtime.label .start⟩
    TM2.Supports Runtime.machine Runtime.labels.toFinset := by
  exact ⟨List.mem_toFinset.mpr (label_mem .start),
    fun q member ↦ label_supports q (List.mem_toFinset.mp member)⟩

set_option maxRecDepth 4096 in
/-- Ordered candidate count, with duplicates retained exactly as in the executable list. -/
theorem labels_length : Runtime.labels.length = 344 := by decide +kernel

end ConjectureMachines.Compilation.RuntimeSupport
