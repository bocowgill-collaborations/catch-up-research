/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.Block

/-!
# Finite TM1 control numbering

An ordered support list replaces function-valued source labels with finite numeric control
before alphabet reduction. Only goto destinations change; the store, tape and primitive
operations remain identical. State zero decodes to the source default label.
-/

@[expose] public section

namespace ConjectureMachines.Compilation.TM1Number

open Turing StateTransition Relation

variable {Γ Λ Λ' σ : Type*}

/-- Rename goto destinations while leaving every primitive operation unchanged. -/
def mapStmt (f : Λ → Λ') : TM1.Stmt Γ Λ σ → TM1.Stmt Γ Λ' σ
  | .move d q => .move d (mapStmt f q)
  | .write a q => .write a (mapStmt f q)
  | .load a q => .load a (mapStmt f q)
  | .branch p q r => .branch p (mapStmt f q) (mapStmt f r)
  | .goto l => .goto fun a v ↦ f (l a v)
  | .halt => .halt

/-- Rename only the configuration's optional control label. -/
def mapCfg [Inhabited Γ] (f : Λ → Λ') (c : TM1.Cfg Γ Λ σ) : TM1.Cfg Γ Λ' σ :=
  ⟨c.l.map f, c.var, c.Tape⟩

/-- Statement evaluation commutes exactly with control renaming. -/
theorem stepAux_map [Inhabited Γ] (f : Λ → Λ') (q : TM1.Stmt Γ Λ σ)
    (v : σ) (T : Tape Γ) :
    TM1.stepAux (mapStmt f q) v T = mapCfg f (TM1.stepAux q v T) := by
  induction q generalizing v T with
  | move d q ih => exact ih _ _
  | write a q ih => exact ih _ _
  | load a q ih => exact ih _ _
  | branch p q r ihq ihr =>
    cases h : p T.head v <;> simp [mapStmt, TM1.stepAux, h, ihq, ihr]
  | goto l => rfl
  | halt => rfl

/-- Renaming goto destinations preserves every proof of tape-head-independent jumps. -/
theorem mapStmt_allHeadFree [Inhabited Γ] (f : Λ → Λ') (stmt : TM1.Stmt Γ Λ σ)
    (h : Block.AllHeadFree stmt) : Block.AllHeadFree (mapStmt f stmt) := by
  induction stmt with
  | move d stmt ih => exact ih h
  | write a stmt ih => exact ih h
  | load a stmt ih => exact ih h
  | branch p stmt r ihq ihr => exact ⟨ihq h.1, ihr h.2⟩
  | goto l => exact fun a v ↦ congrArg f (h a v)
  | halt => trivial

section Numbering

variable [Inhabited Λ] [DecidableEq Λ]

/-- An explicit initial-first control list; duplicate labels retain duplicate numeric rows. -/
def numberProgram (M : Λ → TM1.Stmt Γ Λ σ) (labels : List Λ)
    (q : Fin (labels.length + 1)) : TM1.Stmt Γ (Fin (labels.length + 1)) σ :=
  mapStmt (numberLabel labels) (M (unnumberLabel labels q))

/-- Decode numeric control while preserving the entire store and tape. -/
def decodeCfg [Inhabited Γ] (labels : List Λ)
    (c : TM1.Cfg Γ (Fin (labels.length + 1)) σ) : TM1.Cfg Γ Λ σ :=
  mapCfg (unnumberLabel labels) c

/-- Every numeric row decodes to a member of the initial-first support list. -/
theorem unnumberLabel_mem (labels : List Λ) (q : Fin (labels.length + 1)) :
    unnumberLabel labels q ∈ (default :: labels).toFinset := by
  exact List.mem_toFinset.mpr (List.get_mem _ _)

/-- Numbering followed by decoding fixes every source configuration in the support list. -/
theorem decodeCfg_map [Inhabited Γ] (labels : List Λ) (c : TM1.Cfg Γ Λ σ)
    (hc : c.l ∈ Finset.insertNone (default :: labels).toFinset) :
    decodeCfg labels (mapCfg (numberLabel labels) c) = c := by
  rcases c with ⟨l, v, T⟩
  cases l with
  | none => rfl
  | some l =>
    simp only [decodeCfg, mapCfg, Option.map_some,
      unnumber_number labels (List.mem_toFinset.mp (Finset.some_mem_insertNone.mp hc))]

/-- At supported source control, numbering commutes with one complete source transition. -/
theorem step_number [Inhabited Γ] (M : Λ → TM1.Stmt Γ Λ σ) (labels : List Λ)
    (c : TM1.Cfg Γ Λ σ) (hc : c.l ∈ Finset.insertNone (default :: labels).toFinset) :
    (TM1.step M c).map (mapCfg (numberLabel labels)) =
      TM1.step (numberProgram M labels) (mapCfg (numberLabel labels) c) := by
  rcases c with ⟨l, v, T⟩
  cases l with
  | none => rfl
  | some l =>
    simp only [TM1.step, mapCfg, Option.map_some, numberProgram,
      unnumber_number labels (List.mem_toFinset.mp (Finset.some_mem_insertNone.mp hc)),
      stepAux_map]

/-- Source-to-numbered one-step simulation retains the source finite-support invariant. -/
theorem number_respects [Inhabited Γ] (M : Λ → TM1.Stmt Γ Λ σ) (labels : List Λ)
    (ss : TM1.Supports M (default :: labels).toFinset) :
    Respects (TM1.step M) (TM1.step (numberProgram M labels))
      (fun a b ↦ a.l ∈ Finset.insertNone (default :: labels).toFinset ∧
        mapCfg (numberLabel labels) a = b) := by
  intro c target h
  rcases h with ⟨hc, rfl⟩
  have he := step_number M labels c hc
  cases hs : TM1.step M c with
  | none => simpa only [hs, Option.map_none] using he.symm
  | some next =>
    refine ⟨mapCfg (numberLabel labels) next, ⟨?_, rfl⟩, TransGen.single ?_⟩
    · exact TM1.step_supports M ss (by simpa only [Option.mem_def] using hs) hc
    · simpa only [hs, Option.map_some, Option.mem_def] using he.symm

/-- Decoding a renamed supported statement gives exactly its original store, tape and label. -/
theorem stepAux_decode [Inhabited Γ] (labels : List Λ) (stmt : TM1.Stmt Γ Λ σ)
    (hs : TM1.SupportsStmt (default :: labels).toFinset stmt) (v : σ) (T : Tape Γ) :
    decodeCfg labels (TM1.stepAux (mapStmt (numberLabel labels) stmt) v T) =
      TM1.stepAux stmt v T := by
  induction stmt generalizing v T with
  | move d stmt ih => exact ih hs _ _
  | write a stmt ih => exact ih hs _ _
  | load a stmt ih => exact ih hs _ _
  | branch p stmt r ihq ihr =>
    cases h : p T.head v <;> simp [mapStmt, TM1.stepAux, h, ihq hs.1, ihr hs.2]
  | goto l =>
    simp only [mapStmt, TM1.stepAux, decodeCfg, mapCfg, Option.map_some,
      unnumber_number labels (List.mem_toFinset.mp (hs T.head v))]
  | halt => rfl

/-- One numeric-control transition decodes to exactly one original transition. -/
theorem step_decode [Inhabited Γ] (M : Λ → TM1.Stmt Γ Λ σ) (labels : List Λ)
    (ss : TM1.Supports M (default :: labels).toFinset)
    (c : TM1.Cfg Γ (Fin (labels.length + 1)) σ) :
    (TM1.step (numberProgram M labels) c).map (decodeCfg labels) =
      TM1.step M (decodeCfg labels c) := by
  rcases c with ⟨l, v, T⟩
  cases l with
  | none => rfl
  | some q =>
    exact congrArg some
      (stepAux_decode labels _ (ss.2 _ (unnumberLabel_mem labels q)) v T)

/-- Numeric control refines the original machine by exact one-step decoding. -/
theorem decode_respects [Inhabited Γ] (M : Λ → TM1.Stmt Γ Λ σ) (labels : List Λ)
    (ss : TM1.Supports M (default :: labels).toFinset) :
    Respects (TM1.step (numberProgram M labels)) (TM1.step M)
      (fun a b ↦ decodeCfg labels a = b) := by
  apply fun_respects.mpr
  intro c
  have h := step_decode M labels ss c
  cases hn : TM1.step (numberProgram M labels) c with
  | none =>
    simpa only [hn, Option.map_none, FRespects] using h.symm
  | some next =>
    exact TransGen.single (by simpa only [hn, Option.map_some, Option.mem_def] using h.symm)

/-- Both halting directions hold at every numbered configuration, with unchanged data. -/
theorem numberProgram_dom_cfg [Inhabited Γ] (M : Λ → TM1.Stmt Γ Λ σ) (labels : List Λ)
    (ss : TM1.Supports M (default :: labels).toFinset)
    (c : TM1.Cfg Γ (Fin (labels.length + 1)) σ) :
    (StateTransition.eval (TM1.step (numberProgram M labels)) c).Dom ↔
      (StateTransition.eval (TM1.step M) (decodeCfg labels c)).Dom :=
  (StateTransition.tr_eval_dom (decode_respects M labels ss) rfl).symm

/-- Both halting directions also hold when numbering any supported source configuration. -/
theorem numberProgram_dom_source_cfg [Inhabited Γ] (M : Λ → TM1.Stmt Γ Λ σ)
    (labels : List Λ) (ss : TM1.Supports M (default :: labels).toFinset)
    (c : TM1.Cfg Γ Λ σ) (hc : c.l ∈ Finset.insertNone (default :: labels).toFinset) :
    (StateTransition.eval (TM1.step (numberProgram M labels))
      (mapCfg (numberLabel labels) c)).Dom ↔ (StateTransition.eval (TM1.step M) c).Dom :=
  StateTransition.tr_eval_dom (number_respects M labels ss) ⟨hc, rfl⟩

/-- The source initial label is numbered zero, without changing input or initial store. -/
theorem mapCfg_init [Inhabited Γ] [Inhabited σ] (labels : List Λ) (input : List Γ) :
    mapCfg (numberLabel labels) (TM1.init input : TM1.Cfg Γ Λ σ) = TM1.init input := by
  simp only [mapCfg, TM1.init, Option.map_some, numberLabel_default]
  rfl

omit [DecidableEq Λ] in
/-- Numeric state zero decodes to the source initial label, with the same store and input. -/
theorem decodeCfg_init [Inhabited Γ] [Inhabited σ] (labels : List Λ) (input : List Γ) :
    decodeCfg labels (TM1.init input) = (TM1.init input : TM1.Cfg Γ Λ σ) := rfl

/-- Numbering preserves both halting directions on the same finite input tape. -/
theorem numberProgram_dom [Inhabited Γ] [Inhabited σ] (M : Λ → TM1.Stmt Γ Λ σ)
    (labels : List Λ) (ss : TM1.Supports M (default :: labels).toFinset) (input : List Γ) :
    (TM1.eval (numberProgram M labels) input).Dom ↔ (TM1.eval M input).Dom :=
  (StateTransition.tr_eval_dom (decode_respects M labels ss) (decodeCfg_init labels input)).symm

/-- Every procedure of the numbered program stays inside its finite numeric control type. -/
theorem numberProgram_supports (M : Λ → TM1.Stmt Γ Λ σ) (labels : List Λ) :
    TM1.Supports (numberProgram M labels) Finset.univ := by
  refine ⟨Finset.mem_univ _, fun q _ ↦ ?_⟩
  generalize numberProgram M labels q = stmt
  induction stmt <;> simp_all [TM1.SupportsStmt]

/-- Supported head-free source rows give head-free bodies at every numeric label. -/
theorem numberProgram_allHeadFree [Inhabited Γ] (M : Λ → TM1.Stmt Γ Λ σ)
    (labels : List Λ) (hM : ∀ l ∈ (default :: labels).toFinset, Block.AllHeadFree (M l))
    (q : Fin (labels.length + 1)) : Block.AllHeadFree (numberProgram M labels q) :=
  mapStmt_allHeadFree _ _ (hM _ (unnumberLabel_mem labels q))

/-- Adding an initial-first duplicate leaves a supporting ordered label list's set unchanged. -/
theorem initialFirst_support (M : Λ → TM1.Stmt Γ Λ σ) (labels : List Λ)
    (ss : TM1.Supports M labels.toFinset) : TM1.Supports M (default :: labels).toFinset := by
  simpa only [List.toFinset_cons, Finset.insert_eq_of_mem ss.1] using ss

/-- Convenience form when the ordered list already supports the source machine. -/
theorem numberProgram_dom_of_support [Inhabited Γ] [Inhabited σ]
    (M : Λ → TM1.Stmt Γ Λ σ) (labels : List Λ) (ss : TM1.Supports M labels.toFinset)
    (input : List Γ) :
    (TM1.eval (numberProgram M labels) input).Dom ↔ (TM1.eval M input).Dom :=
  numberProgram_dom M labels (initialFirst_support M labels ss) input

/-- Convenience form for head-free bodies on an already supporting ordered label list. -/
theorem numberProgram_allHeadFree_of_support [Inhabited Γ] (M : Λ → TM1.Stmt Γ Λ σ)
    (labels : List Λ) (ss : TM1.Supports M labels.toFinset)
    (hM : ∀ l ∈ labels.toFinset, Block.AllHeadFree (M l))
    (q : Fin (labels.length + 1)) : Block.AllHeadFree (numberProgram M labels q) := by
  apply numberProgram_allHeadFree M labels
  simpa only [List.toFinset_cons, Finset.insert_eq_of_mem ss.1] using hM

end Numbering

end ConjectureMachines.Compilation.TM1Number
