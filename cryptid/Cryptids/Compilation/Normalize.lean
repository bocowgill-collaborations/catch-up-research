/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.Finite

/-! Executable continuation sharing for TM1, with exact simulation and finite support. -/
@[expose] public section

namespace ConjectureMachines.Compilation.TM1Normalize
open Turing Relation StateTransition

variable {Γ Λ σ : Type*}

set_option linter.unusedVariables false in
/-- Statements are shared labels; the program parameter fixes the initial statement. -/
@[nolint unusedArguments]
def Label (M : Λ → TM1.Stmt Γ Λ σ) := TM1.Stmt Γ Λ σ

instance labelInhabited [Inhabited Λ] (M : Λ → TM1.Stmt Γ Λ σ) : Inhabited (Label M) :=
  ⟨M default⟩

/-- Every continuation becomes a jump to its original syntax, without recursive expansion. -/
def tr (M : Λ → TM1.Stmt Γ Λ σ) : Label M → TM1.Stmt Γ (Label M) σ
  | .move d q => .move d (.goto fun _ _ ↦ q)
  | .write f q => .write f (.goto fun _ _ ↦ q)
  | .load f q => .load f (.goto fun _ _ ↦ q)
  | .branch p q r => .branch p (.goto fun _ _ ↦ q) (.goto fun _ _ ↦ r)
  | .goto f => .goto fun a v ↦ M (f a v)
  | .halt => .halt

/-- The normalized syntax has at most one primitive before a jump or halt. -/
def OnePrimitive {Λ' : Type*} : TM1.Stmt Γ Λ' σ → Prop
  | .move _ (.goto _) | .write _ (.goto _) | .load _ (.goto _)
  | .branch _ (.goto _) (.goto _) | .goto _ | .halt => True
  | _ => False

theorem tr_onePrimitive (M : Λ → TM1.Stmt Γ Λ σ) (q : Label M) : OnePrimitive (tr M q) := by
  cases q <;> trivial

/-- The translated configuration has exactly the original store and tape. -/
def trCfg [Inhabited Γ] (M : Λ → TM1.Stmt Γ Λ σ) :
    TM1.Cfg Γ Λ σ → TM1.Cfg Γ (Label M) σ
  | ⟨l, v, T⟩ => ⟨l.map M, v, T⟩

theorem stepAux_reaches [Inhabited Γ] (M : Λ → TM1.Stmt Γ Λ σ)
    (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    Reaches₁ (TM1.step (tr M)) ⟨some q, v, T⟩ (trCfg M (TM1.stepAux q v T)) := by
  induction q generalizing v T with
  | move d q ih => exact TransGen.head rfl (ih _ _)
  | write f q ih => exact TransGen.head rfl (ih _ _)
  | load f q ih => exact TransGen.head rfl (ih _ _)
  | branch p q r ihq ihr =>
    cases h : p T.1 v
    · simp only [TM1.stepAux, h, Bool.cond_false]
      exact TransGen.head (by simp [TM1.step, tr, TM1.stepAux, h]) (ihr _ _)
    · simp only [TM1.stepAux, h, Bool.cond_true]
      exact TransGen.head (by simp [TM1.step, tr, TM1.stepAux, h]) (ihq _ _)
  | goto f => exact TransGen.single rfl
  | halt => exact TransGen.single rfl

/-- Each source transition is simulated by a nonempty finite normalized execution. -/
theorem tr_respects [Inhabited Γ] (M : Λ → TM1.Stmt Γ Λ σ) :
    Respects (TM1.step M) (TM1.step (tr M)) (fun a b ↦ trCfg M a = b) :=
  fun_respects.2 fun ⟨l, v, T⟩ ↦ by
    cases l with
    | none => rfl
    | some l => exact stepAux_reaches M (M l) v T

/-- Halting is equivalent at every pair of exactly related configurations. -/
theorem tr_eval_dom_cfg [Inhabited Γ] (M : Λ → TM1.Stmt Γ Λ σ)
    (c : TM1.Cfg Γ Λ σ) :
    (StateTransition.eval (TM1.step (tr M)) (trCfg M c)).Dom ↔
      (StateTransition.eval (TM1.step M) c).Dom :=
  StateTransition.tr_eval_dom (tr_respects M) rfl

theorem tr_init [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
    (M : Λ → TM1.Stmt Γ Λ σ) (l : List Γ) :
    trCfg M (TM1.init l) = TM1.init l := rfl

/-- Normalization preserves halting in both directions from every finite input tape. -/
theorem tr_eval_dom [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
    (M : Λ → TM1.Stmt Γ Λ σ) (l : List Γ) :
    (TM1.eval (tr M) l).Dom ↔ (TM1.eval M l).Dom :=
  StateTransition.tr_eval_dom (tr_respects M) (tr_init M l)

/-- Ordered source-substatement support, preserving duplicates and their source order. -/
def supportList (M : Λ → TM1.Stmt Γ Λ σ) (labels : List Λ) : List (Label M) :=
  labels.flatMap fun l ↦ subtermList (M l)

theorem mem_supportList (M : Λ → TM1.Stmt Γ Λ σ) (labels : List Λ) (q : Label M) :
    q ∈ supportList M labels ↔ ∃ l ∈ labels, q ∈ TM1.stmts₁ (M l) := by
  change q ∈ labels.flatMap (fun l ↦ subtermList (M l)) ↔ _
  dsimp only [Label] at q ⊢
  simp only [List.mem_flatMap, mem_subtermList]

/-- Only immediate continuations and the source goto destinations are used as new labels. -/
theorem supportsStmt_tr (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    (Q : Finset (Label M)) (body : ∀ l ∈ S, M l ∈ Q) (q : TM1.Stmt Γ Λ σ)
    (sub : ∀ r ∈ TM1.stmts₁ q, r ∈ Q) (hs : TM1.SupportsStmt S q) :
    TM1.SupportsStmt Q (tr M q) := by
  classical
  cases q with
  | move d q => exact fun _ _ ↦ sub q (Finset.mem_insert_of_mem TM1.stmts₁_self)
  | write f q => exact fun _ _ ↦ sub q (Finset.mem_insert_of_mem TM1.stmts₁_self)
  | load f q => exact fun _ _ ↦ sub q (Finset.mem_insert_of_mem TM1.stmts₁_self)
  | branch p q r =>
    constructor
    · exact fun _ _ ↦ sub q
        (Finset.mem_insert_of_mem (Finset.mem_union_left _ TM1.stmts₁_self))
    · exact fun _ _ ↦ sub r
        (Finset.mem_insert_of_mem (Finset.mem_union_right _ TM1.stmts₁_self))
  | goto f => exact fun a v ↦ body (f a v) (hs a v)
  | halt => trivial

section Support
variable [Fintype Γ] [Fintype σ] [DecidableEq Γ] [DecidableEq Λ] [DecidableEq σ]

instance labelDecidableEq (M : Λ → TM1.Stmt Γ Λ σ) : DecidableEq (Label M) :=
  inferInstanceAs (DecidableEq (TM1.Stmt Γ Λ σ))

/-- The executable finite support for the normalized program. -/
def support (M : Λ → TM1.Stmt Γ Λ σ) (labels : List Λ) : Finset (Label M) :=
  (supportList M labels).toFinset

theorem mem_support (M : Λ → TM1.Stmt Γ Λ σ) (labels : List Λ) (q : Label M) :
    q ∈ support M labels ↔ ∃ l ∈ labels, q ∈ TM1.stmts₁ (M l) := by
  simp only [support, List.mem_toFinset, mem_supportList]

/-- A proved source support yields a constructive finite support for the normalized program. -/
theorem tr_supports [Inhabited Λ] (M : Λ → TM1.Stmt Γ Λ σ) (labels : List Λ)
    (ss : TM1.Supports M labels.toFinset) : TM1.Supports (tr M) (support M labels) := by
  have body : ∀ l ∈ labels.toFinset, M l ∈ support M labels := by
    intro l hl
    exact (mem_support M labels (M l)).2
      ⟨l, List.mem_toFinset.1 hl, TM1.stmts₁_self⟩
  constructor
  · exact body default ss.1
  · intro q hq
    obtain ⟨l, hl, hsub⟩ := (mem_support M labels q).1 hq
    apply supportsStmt_tr M labels.toFinset (support M labels) body q
    · intro r hr
      exact (mem_support M labels r).2 ⟨l, hl, TM1.stmts₁_trans hsub hr⟩
    · exact TM1.stmts₁_supportsStmt_mono hsub (ss.2 l (List.mem_toFinset.2 hl))

end Support
end ConjectureMachines.Compilation.TM1Normalize
