/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Cryptids.Compilation.NumberTM1

/-! # Exact local certificates for independently numbered finite tables

A decoded row must preserve existing transitions and missing transitions. No inverse
numbering, global support traversal or particular native hash ordering is assumed.
-/

@[expose] public section
namespace ConjectureMachines.Compilation.LocalCertificate
open Turing StateTransition

section Binary
variable {p q : Nat}

/-- Decode control while retaining the complete tape. -/
def decodeCfg (decode : Fin p → Fin q) (cfg : Cfg p 2) : Cfg q 2 :=
  ⟨decode cfg.state, cfg.tape⟩

/-- Each literal row decodes to exactly the corresponding source row. -/
def Rows (literal : Machine p 2) (source : Machine q 2)
    (decode : Fin p → Fin q) : Prop :=
  ∀ state bit, (literal.transition state bit).map
    (fun (write, dir, next) ↦ (write, dir, decode next)) =
      source.transition (decode state) bit

theorem step_decode (literal : Machine p 2) (source : Machine q 2)
    (decode : Fin p → Fin q) (certificate : Rows literal source decode)
    (cfg : Cfg p 2) :
    (step literal cfg).map (decodeCfg decode) = step source (decodeCfg decode cfg) := by
  rcases cfg with ⟨state, tape⟩
  simp only [step, decodeCfg]
  rw [← certificate state tape.head]
  cases literal.transition state tape.head with
  | none => rfl
  | some instruction => rcases instruction with ⟨write, dir, next⟩; rfl

theorem respects (literal : Machine p 2) (source : Machine q 2)
    (decode : Fin p → Fin q) (certificate : Rows literal source decode) :
    Respects (step literal) (step source) (fun a b ↦ decodeCfg decode a = b) := by
  apply fun_respects.mpr
  intro cfg
  have equal := step_decode literal source decode certificate cfg
  cases move : step literal cfg with
  | none => simpa only [move, Option.map_none, FRespects] using equal.symm
  | some next =>
    exact Relation.TransGen.single
      (by simpa only [move, Option.map_some, Option.mem_def] using equal.symm)

/-- Exact rows and the initial decoder give both blank-tape termination directions. -/
theorem halts_iff [NeZero p] [NeZero q] (literal : Machine p 2) (source : Machine q 2)
    (decode : Fin p → Fin q) (certificate : Rows literal source decode)
    (initial : decode 0 = 0) : Halts literal ↔ Halts source := by
  exact (tr_eval_dom (respects literal source decode certificate)
    (show decodeCfg decode ConjectureMachines.init = ConjectureMachines.init from by
      simp only [decodeCfg, ConjectureMachines.init, initial])).symm
end Binary

section Post
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] {p : Nat} [NeZero p]

/-- A literal Post table can decode to arbitrary symbolic source labels. -/
def PostRows (literal : TM0.Machine Γ (Fin p)) (source : TM0.Machine Γ Λ)
    (decode : Fin p → Λ) : Prop :=
  ∀ state symbol, (literal state symbol).map (fun (next, command) ↦ (decode next, command)) =
    source (decode state) symbol

/-- Decode a Post configuration without changing its tape geometry. -/
def decodePostCfg (decode : Fin p → Λ) (cfg : TM0.Cfg Γ (Fin p)) : TM0.Cfg Γ Λ :=
  ⟨decode cfg.q, cfg.Tape⟩

theorem post_step_decode (literal : TM0.Machine Γ (Fin p)) (source : TM0.Machine Γ Λ)
    (decode : Fin p → Λ) (certificate : PostRows literal source decode)
    (cfg : TM0.Cfg Γ (Fin p)) :
    (TM0.step literal cfg).map (decodePostCfg decode) =
      TM0.step source (decodePostCfg decode cfg) := by
  rcases cfg with ⟨state, tape⟩
  simp only [TM0.step, decodePostCfg]
  rw [← certificate state tape.head]
  cases literal state tape.head with
  | none => rfl
  | some instruction => rcases instruction with ⟨next, command⟩; rfl

theorem post_respects (literal : TM0.Machine Γ (Fin p)) (source : TM0.Machine Γ Λ)
    (decode : Fin p → Λ) (certificate : PostRows literal source decode) :
    Respects (TM0.step literal) (TM0.step source)
      (fun a b ↦ decodePostCfg decode a = b) := by
  apply fun_respects.mpr
  intro cfg
  have equal := post_step_decode literal source decode certificate cfg
  cases move : TM0.step literal cfg with
  | none => simpa only [move, Option.map_none, FRespects] using equal.symm
  | some next =>
    exact Relation.TransGen.single
      (by simpa only [move, Option.map_some, Option.mem_def] using equal.symm)

/-- Neither injectivity nor global label coverage is needed for a local certificate. -/
theorem post_halts_iff (literal : TM0.Machine Γ (Fin p)) (source : TM0.Machine Γ Λ)
    (decode : Fin p → Λ) (certificate : PostRows literal source decode)
    (initial : decode 0 = default) (input : List Γ) :
    (TM0.eval literal input).Dom ↔ (TM0.eval source input).Dom := by
  exact (tr_eval_dom (post_respects literal source decode certificate)
    (show decodePostCfg decode (TM0.init input) = TM0.init input from by
      change TM0.Cfg.mk (decode 0) _ = TM0.Cfg.mk default _
      rw [initial]
      rfl)).symm
end Post

section TapeMachine
variable {Γ A B σ : Type*} [Inhabited Γ]

/-- Exact statement decoding also certifies finite shared-tape and binary control snapshots. -/
def TM1Rows (literal : A → TM1.Stmt Γ A σ) (source : B → TM1.Stmt Γ B σ)
    (decode : A → B) : Prop :=
  ∀ state, TM1Number.mapStmt decode (literal state) = source (decode state)

theorem tm1_step_decode (literal : A → TM1.Stmt Γ A σ) (source : B → TM1.Stmt Γ B σ)
    (decode : A → B) (rows : TM1Rows literal source decode)
    (cfg : TM1.Cfg Γ A σ) :
    (TM1.step literal cfg).map (TM1Number.mapCfg decode) =
      TM1.step source (TM1Number.mapCfg decode cfg) := by
  rcases cfg with ⟨pc, store, tape⟩
  cases pc with
  | none => rfl
  | some pc =>
    simp only [TM1.step, TM1Number.mapCfg, Option.map_some]
    rw [← rows pc, TM1Number.stepAux_map]
    rfl

theorem tm1_respects (literal : A → TM1.Stmt Γ A σ) (source : B → TM1.Stmt Γ B σ)
    (decode : A → B) (rows : TM1Rows literal source decode) :
    Respects (TM1.step literal) (TM1.step source)
      (fun a b ↦ TM1Number.mapCfg decode a = b) := by
  apply fun_respects.mpr
  intro cfg
  have equal := tm1_step_decode literal source decode rows cfg
  cases move : TM1.step literal cfg with
  | none => simpa only [move, Option.map_none, FRespects] using equal.symm
  | some next =>
    exact Relation.TransGen.single
      (by simpa only [move, Option.map_some, Option.mem_def] using equal.symm)

/-- A local statement certificate suffices for both input-tape termination directions. -/
theorem tm1_halts_iff [Inhabited A] [Inhabited B] [Inhabited σ]
    (literal : A → TM1.Stmt Γ A σ) (source : B → TM1.Stmt Γ B σ)
    (decode : A → B) (rows : TM1Rows literal source decode)
    (initial : decode default = default) (input : List Γ) :
    (TM1.eval literal input).Dom ↔ (TM1.eval source input).Dom := by
  exact (tr_eval_dom (tm1_respects literal source decode rows)
    (show TM1Number.mapCfg decode (TM1.init input) = TM1.init input from by
      simp only [TM1Number.mapCfg, TM1.init, Option.map_some, initial])).symm
end TapeMachine
end ConjectureMachines.Compilation.LocalCertificate
