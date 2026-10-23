/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.FreeNormalize

/-! Composition through shared continuations and the optimized binary block simulator. -/
@[expose] public section
namespace ConjectureMachines.Compilation
open Turing
set_option maxSynthPendingDepth 64

section
variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)]
variable [Fintype σ] [DecidableEq σ] [DecidableEq Λ] [Inhabited Λ] [Inhabited σ]
variable (M : Λ → TM2.Stmt Γ Λ σ) (C : BlockCode (TM2to1.Γ' K Γ))

def sharedBinary := Block.compilerFree C (TM1Normalize.tr (TM2to1.tr M))
def sharedPost := TM1to0.tr (sharedBinary M C)
instance sharedPostDecidableEq : DecidableEq (TM1to0.Λ' (sharedBinary M C)) :=
  postLabelDecidableEq (sharedBinary M C)
def sharedTapeLabels (labels : List Λ) :=
  TM1Normalize.supportList (TM2to1.tr M) (stackSupportList M labels)
def sharedBinaryLabels (labels : List Λ) (symbols : List (TM2to1.Γ' K Γ)) :=
  binarySupportList (TM1Normalize.tr (TM2to1.tr M)) (sharedTapeLabels M labels) symbols
def sharedLabels (labels : List Λ) (symbols : List (TM2to1.Γ' K Γ)) (stores : List σ) :=
  postSupportList (sharedBinary M C) (sharedBinaryLabels M labels symbols) stores

theorem shared_supported (labels : List Λ) (ss : TM2.Supports M labels.toFinset)
    (symbols : List (TM2to1.Γ' K Γ)) (cover : ∀ a, a ∈ symbols)
    (stores : List σ) (storeCover : ∀ v, v ∈ stores) :
    TM0.Supports (sharedPost M C) ↑(sharedLabels M C labels symbols stores).toFinset := by
  have hs : (stackSupportList M labels).toFinset = TM2to1.trSupp M labels.toFinset := by
    ext q
    simp only [List.mem_toFinset, mem_stackSupportList]
  have h1 : TM1.Supports (TM2to1.tr M) (stackSupportList M labels).toFinset := by
    rw [hs]
    exact TM2to1.tr_supports M ss
  have h2 := TM1Normalize.tr_supports (TM2to1.tr M) (stackSupportList M labels) h1
  have hb : (sharedBinaryLabels M labels symbols).toFinset =
      binarySupport (TM1Normalize.tr (TM2to1.tr M))
        (TM1Normalize.support (TM2to1.tr M) (stackSupportList M labels)) := by
    ext q
    simp only [sharedBinaryLabels, List.mem_toFinset,
      mem_binarySupportList _ _ _ cover, binarySupport_eq, TM1Normalize.support,
      sharedTapeLabels]
  have h3 : TM1.Supports (sharedBinary M C) (sharedBinaryLabels M labels symbols).toFinset := by
    rw [hb]
    exact Block.free_supports C _ h2
  have hp : (sharedLabels M C labels symbols stores).toFinset =
      TM1to0.trStmts (sharedBinary M C) (sharedBinaryLabels M labels symbols).toFinset := by
    ext q
    simp only [sharedLabels, List.mem_toFinset, mem_postSupportList _ _ _ storeCover]
  rw [hp]
  exact TM1to0.tr_supports (sharedBinary M C) h3

/-- An executable finite backend with shared source continuations. -/
def sharedStack (labels : List Λ) (symbols : List (TM2to1.Γ' K Γ)) (stores : List σ)
    (k : K) : NumberedPost where
  extraStates := (sharedLabels M C labels symbols stores).length
  machine := numberMachine (sharedPost M C) (sharedLabels M C labels symbols stores)
  input := blockInput C (TM2to1.trInit k [])

theorem sharedStack_halts (labels : List Λ) (ss : TM2.Supports M labels.toFinset)
    (symbols : List (TM2to1.Γ' K Γ)) (cover : ∀ a, a ∈ symbols)
    (stores : List σ) (storeCover : ∀ v, v ∈ stores) (k : K) :
    (sharedStack M C labels symbols stores k).Halts ↔ (TM2.eval M k []).Dom := by
  have hn := numberMachine_dom (sharedPost M C) (sharedLabels M C labels symbols stores)
    (↑(sharedLabels M C labels symbols stores).toFinset)
    (shared_supported M C labels ss symbols cover stores storeCover)
    (by intro q hq; exact List.mem_cons_of_mem _ (List.mem_toFinset.mp hq))
    (blockInput C (TM2to1.trInit k []))
  have hp : (TM0.eval (sharedPost M C) (blockInput C (TM2to1.trInit k []))).Dom ↔
      (TM2.eval M k []).Dom := by
    rw [sharedPost, TM1to0.tr_eval]
    have hs : (stackSupportList M labels).toFinset = TM2to1.trSupp M labels.toFinset := by
      ext q
      simp only [List.mem_toFinset, mem_stackSupportList]
    have h1 : TM1.Supports (TM2to1.tr M) (stackSupportList M labels).toFinset := by
      rw [hs]
      exact TM2to1.tr_supports M ss
    have h2 := TM1Normalize.tr_supports (TM2to1.tr M) (stackSupportList M labels) h1
    exact (Block.free_dom C _ h2 (FreeNormalize.normalize_allFree M _) _).trans
      ((TM1Normalize.tr_eval_dom _ _).trans (TM2to1.tr_eval_dom M k []))
  exact hn.trans hp
end
end ConjectureMachines.Compilation
