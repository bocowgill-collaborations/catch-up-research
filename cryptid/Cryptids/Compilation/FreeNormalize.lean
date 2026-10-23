/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.Normalize
public import Cryptids.Compilation.Block

/-! Tape-independent jumps for the supported shared-continuation stack compiler. -/
@[expose] public section

namespace ConjectureMachines.Compilation.FreeNormalize
open Turing

section General
variable {Γ Λ σ : Type*} [Inhabited Γ]

/-- Tape-independent jumps remain tape-independent inside every syntax substatement. -/
theorem subterm_allFree {q r : TM1.Stmt Γ Λ σ} (hq : Block.AllHeadFree q)
    (hr : r ∈ TM1.stmts₁ q) : Block.AllHeadFree r := by
  classical
  induction q with
    simp only [TM1.stmts₁, Block.AllHeadFree, Finset.mem_insert, Finset.mem_union,
      Finset.mem_singleton] at hr hq
  | branch p q s ihq ihs =>
    rcases hr with (rfl | hr | hr)
    · exact hq
    · exact ihq hq.1 hr
    · exact ihs hq.2 hr
  | goto f => subst hr; exact hq
  | halt => subst hr; trivial
  | _ _ q ih => rcases hr with rfl | hr <;> [exact hq; exact ih hq hr]

/-- Continuation sharing preserves a source statement's tape-independent jumps. -/
theorem normalize_preserves_allFree (M : Λ → TM1.Stmt Γ Λ σ)
    (q : TM1.Stmt Γ Λ σ) (hq : Block.AllHeadFree q) :
    Block.AllHeadFree (TM1Normalize.tr M q) := by
  cases q with
  | move d q => exact fun _ _ ↦ rfl
  | write f q => exact fun _ _ ↦ rfl
  | load f q => exact fun _ _ ↦ rfl
  | branch p q r => exact ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  | goto f => exact fun a v ↦ congrArg M (hq a v)
  | halt => trivial

/-- Only labels in the constructive source-substatement traversal need the jump property. -/
theorem normalize_supportList_allFree (M : Λ → TM1.Stmt Γ Λ σ)
    (hM : ∀ l, Block.AllHeadFree (M l)) (labels : List Λ) (q : TM1Normalize.Label M)
    (hq : q ∈ TM1Normalize.supportList M labels) :
    Block.AllHeadFree (TM1Normalize.tr M q) := by
  obtain ⟨l, _, hsub⟩ := (TM1Normalize.mem_supportList M labels q).1 hq
  exact normalize_preserves_allFree M q (subterm_allFree (hM l) hsub)
end General

section Stack
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- A source stack statement never computes a destination from the tape head. -/
theorem stackNormal_allFree (q : TM2.Stmt Γ Λ σ) :
    Block.AllHeadFree (TM2to1.trNormal q) := by
  induction q with
  | push k f q ih => exact fun _ _ ↦ rfl
  | peek k f q ih => exact fun _ _ ↦ rfl
  | pop k f q ih => exact fun _ _ ↦ rfl
  | load f q ih => exact ih
  | branch p q r ihq ihr => exact ⟨ihq, ihr⟩
  | goto f => exact fun _ _ ↦ rfl
  | halt => trivial

/-- Stack actions preserve the continuation's tape-independent jumps. -/
theorem stackAction_allFree [DecidableEq K] {k : K}
    (q : TM1.Stmt (TM2to1.Γ' K Γ) (TM2to1.Λ' K Γ Λ σ) σ)
    (a : TM2to1.StAct K Γ σ k) (hq : Block.AllHeadFree q) :
    Block.AllHeadFree (TM2to1.trStAct q a) := by
  cases a <;> simp only [TM2to1.trStAct, Block.AllHeadFree, hq, and_self]

/-- Every actual stack-simulator body has tape-independent jumps, including shuttle labels. -/
theorem stack_allFree [DecidableEq K] (M : Λ → TM2.Stmt Γ Λ σ)
    (l : TM2to1.Λ' K Γ Λ σ) : Block.AllHeadFree (TM2to1.tr M l) := by
  cases l with
  | normal l => exact stackNormal_allFree (M l)
  | go k a q =>
    constructor
    · exact stackAction_allFree _ a (fun _ _ ↦ rfl)
    · exact fun _ _ ↦ rfl
  | ret q => exact ⟨stackNormal_allFree q, fun _ _ ↦ rfl⟩

/-- The ordered normalized stack support contains only tape-independent-jump bodies. -/
theorem normalize_stackSupportList_allFree [DecidableEq K] (M : Λ → TM2.Stmt Γ Λ σ)
    (labels : List (TM2to1.Λ' K Γ Λ σ))
    (q : TM1Normalize.Label (TM2to1.tr M))
    (hq : q ∈ TM1Normalize.supportList (TM2to1.tr M) labels) :
    Block.AllHeadFree (TM1Normalize.tr (TM2to1.tr M) q) :=
  normalize_supportList_allFree (TM2to1.tr M) (stack_allFree M) labels q hq

variable [Fintype K] [DecidableEq K] [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)]
variable [Fintype σ] [DecidableEq σ] [DecidableEq Λ]

/-- The finite support used by assembly validates every jump bypass without runtime equality. -/
theorem normalize_allFree (M : Λ → TM2.Stmt Γ Λ σ)
    (labels : List (TM2to1.Λ' K Γ Λ σ))
    (q : TM1Normalize.Label (TM2to1.tr M))
    (hq : q ∈ TM1Normalize.support (TM2to1.tr M) labels) :
    Block.AllHeadFree (TM1Normalize.tr (TM2to1.tr M) q) := by
  apply normalize_stackSupportList_allFree M labels q
  exact List.mem_toFinset.1 hq
end Stack
end ConjectureMachines.Compilation.FreeNormalize
