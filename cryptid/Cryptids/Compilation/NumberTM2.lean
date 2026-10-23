/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.Finite
public import Cryptids.Compilation.Memo

/-! # Finite numeric TM2 control with nominal store-table caching -/

@[expose] public section
namespace ConjectureMachines.Compilation.TM2Number
open Turing StateTransition Relation

variable {K : Type*} {Γ : K → Type*} {Λ Λ' σ : Type*}

/-- Rename only goto destinations; all stack operations and store functions are retained. -/
def mapStmt (rename : Λ → Λ') : TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' σ
  | .push k f next => .push k f (mapStmt rename next)
  | .peek k f next => .peek k f (mapStmt rename next)
  | .pop k f next => .pop k f (mapStmt rename next)
  | .load f next => .load f (mapStmt rename next)
  | .branch p first second => .branch p (mapStmt rename first) (mapStmt rename second)
  | .goto target => .goto (fun store ↦ rename (target store))
  | .halt => .halt

/-- Configuration renaming preserves every stack and the exact store. -/
def mapCfg (rename : Λ → Λ') (config : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ' σ :=
  ⟨config.l.map rename, config.var, config.stk⟩

theorem stepAux_map [DecidableEq K] (rename : Λ → Λ') (stmt : TM2.Stmt Γ Λ σ)
    (store : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (mapStmt rename stmt) store tapes =
      mapCfg rename (TM2.stepAux stmt store tapes) := by
  induction stmt generalizing store tapes with
  | push k f next ih => exact ih _ _
  | peek k f next ih => exact ih _ _
  | pop k f next ih => exact ih _ _
  | load f next ih => exact ih _ _
  | branch p first second left right =>
    cases h : p store <;> simp [mapStmt, TM2.stepAux, h, left, right]
  | goto target => rfl
  | halt => rfl

section Numbering
variable [Inhabited Λ] [DecidableEq Λ]

/-- Explicit initial-first numbering, retaining duplicate support-list rows. -/
def numberProgram (machine : Λ → TM2.Stmt Γ Λ σ) (labels : List Λ)
    (state : Fin (labels.length + 1)) : TM2.Stmt Γ (Fin (labels.length + 1)) σ :=
  mapStmt (numberLabel labels) (machine (unnumberLabel labels state))

def decodeCfg (labels : List Λ) (config : TM2.Cfg Γ (Fin (labels.length + 1)) σ) :
    TM2.Cfg Γ Λ σ := mapCfg (unnumberLabel labels) config

theorem unnumberLabel_mem (labels : List Λ) (state : Fin (labels.length + 1)) :
    unnumberLabel labels state ∈ (default :: labels).toFinset :=
  List.mem_toFinset.mpr (List.get_mem _ _)

/-- Decoding every supported renamed statement is exactly its original transition. -/
theorem stepAux_decode [DecidableEq K] (labels : List Λ) (stmt : TM2.Stmt Γ Λ σ)
    (supported : TM2.SupportsStmt (default :: labels).toFinset stmt)
    (store : σ) (tapes : ∀ k, List (Γ k)) :
    decodeCfg labels (TM2.stepAux (mapStmt (numberLabel labels) stmt) store tapes) =
      TM2.stepAux stmt store tapes := by
  induction stmt generalizing store tapes with
  | push k f next ih => exact ih supported _ _
  | peek k f next ih => exact ih supported _ _
  | pop k f next ih => exact ih supported _ _
  | load f next ih => exact ih supported _ _
  | branch p first second left right =>
    cases h : p store <;>
      simp [mapStmt, TM2.stepAux, h, left supported.1, right supported.2]
  | goto target =>
    simp only [mapStmt, TM2.stepAux, decodeCfg, mapCfg, Option.map_some,
      unnumber_number labels (List.mem_toFinset.mp (supported store))]
  | halt => rfl

/-- Numbering followed by decoding fixes every supported source configuration. -/
theorem decodeCfg_map (labels : List Λ) (config : TM2.Cfg Γ Λ σ)
    (member : config.l ∈ Finset.insertNone (default :: labels).toFinset) :
    decodeCfg labels (mapCfg (numberLabel labels) config) = config := by
  rcases config with ⟨pc, store, tapes⟩
  cases pc with
  | none => rfl
  | some pc =>
    simp only [decodeCfg, mapCfg, Option.map_some,
      unnumber_number labels (List.mem_toFinset.mp (Finset.some_mem_insertNone.mp member))]

theorem step_number [DecidableEq K] (machine : Λ → TM2.Stmt Γ Λ σ) (labels : List Λ)
    (config : TM2.Cfg Γ Λ σ)
    (member : config.l ∈ Finset.insertNone (default :: labels).toFinset) :
    (TM2.step machine config).map (mapCfg (numberLabel labels)) =
      TM2.step (numberProgram machine labels) (mapCfg (numberLabel labels) config) := by
  rcases config with ⟨pc, store, tapes⟩
  cases pc with
  | none => rfl
  | some pc =>
    simp only [TM2.step, mapCfg, Option.map_some, numberProgram,
      unnumber_number labels (List.mem_toFinset.mp (Finset.some_mem_insertNone.mp member)),
      stepAux_map]

/-- Source simulation retains the support invariant through every positive step. -/
theorem number_respects [DecidableEq K] (machine : Λ → TM2.Stmt Γ Λ σ) (labels : List Λ)
    (supported : TM2.Supports machine (default :: labels).toFinset) :
    Respects (TM2.step machine) (TM2.step (numberProgram machine labels))
      (fun first second ↦ first.l ∈ Finset.insertNone (default :: labels).toFinset ∧
        mapCfg (numberLabel labels) first = second) := by
  intro config target related
  rcases related with ⟨member, rfl⟩
  have equal := step_number machine labels config member
  cases stepped : TM2.step machine config with
  | none => simpa only [stepped, Option.map_none] using equal.symm
  | some next =>
    refine ⟨mapCfg (numberLabel labels) next, ⟨?_, rfl⟩, TransGen.single ?_⟩
    · exact TM2.step_supports machine supported
        (by simpa only [Option.mem_def] using stepped) member
    · simpa only [stepped, Option.map_some, Option.mem_def] using equal.symm

omit [DecidableEq Λ] in
/-- Every reachable source configuration retains the finite-support invariant. -/
theorem reaches_supported [DecidableEq K] (machine : Λ → TM2.Stmt Γ Λ σ)
    (support : Finset Λ) (supported : TM2.Supports machine support)
    (first last : TM2.Cfg Γ Λ σ) (initial : first.l ∈ Finset.insertNone support)
    (path : TM2.Reaches machine first last) : last.l ∈ Finset.insertNone support := by
  induction path with
  | refl => exact initial
  | tail _ step ih => exact TM2.step_supports machine supported step ih

/-- Every numeric transition decodes to exactly one source transition. -/
theorem step_decode [DecidableEq K] (machine : Λ → TM2.Stmt Γ Λ σ) (labels : List Λ)
    (supported : TM2.Supports machine (default :: labels).toFinset)
    (config : TM2.Cfg Γ (Fin (labels.length + 1)) σ) :
    (TM2.step (numberProgram machine labels) config).map (decodeCfg labels) =
      TM2.step machine (decodeCfg labels config) := by
  rcases config with ⟨pc, store, tapes⟩
  cases pc with
  | none => rfl
  | some pc =>
    exact congrArg some
      (stepAux_decode labels _ (supported.2 _ (unnumberLabel_mem labels pc)) store tapes)

theorem decode_respects [DecidableEq K] (machine : Λ → TM2.Stmt Γ Λ σ) (labels : List Λ)
    (supported : TM2.Supports machine (default :: labels).toFinset) :
    Respects (TM2.step (numberProgram machine labels)) (TM2.step machine)
      (fun first second ↦ decodeCfg labels first = second) := by
  apply fun_respects.mpr
  intro config
  have equal := step_decode machine labels supported config
  cases stepped : TM2.step (numberProgram machine labels) config with
  | none => simpa only [stepped, Option.map_none, FRespects] using equal.symm
  | some next =>
    exact TransGen.single
      (by simpa only [stepped, Option.map_some, Option.mem_def] using equal.symm)

/-- Both termination directions at every numeric configuration, including duplicate rows. -/
theorem numberProgram_dom_cfg [DecidableEq K] (machine : Λ → TM2.Stmt Γ Λ σ)
    (labels : List Λ) (supported : TM2.Supports machine (default :: labels).toFinset)
    (config : TM2.Cfg Γ (Fin (labels.length + 1)) σ) :
    (StateTransition.eval (TM2.step (numberProgram machine labels)) config).Dom ↔
      (StateTransition.eval (TM2.step machine) (decodeCfg labels config)).Dom :=
  (tr_eval_dom (decode_respects machine labels supported) rfl).symm

theorem numberProgram_dom_source_cfg [DecidableEq K] (machine : Λ → TM2.Stmt Γ Λ σ)
    (labels : List Λ) (supported : TM2.Supports machine (default :: labels).toFinset)
    (config : TM2.Cfg Γ Λ σ)
    (member : config.l ∈ Finset.insertNone (default :: labels).toFinset) :
    (StateTransition.eval (TM2.step (numberProgram machine labels))
      (mapCfg (numberLabel labels) config)).Dom ↔
      (StateTransition.eval (TM2.step machine) config).Dom :=
  tr_eval_dom (number_respects machine labels supported) ⟨member, rfl⟩

/-- The ordinary TM2 initializer becomes numeric state zero with identical data. -/
theorem mapCfg_init [DecidableEq K] [Inhabited σ] (labels : List Λ)
    (inputStack : K) (input : List (Γ inputStack)) :
    mapCfg (numberLabel labels) (TM2.init inputStack input : TM2.Cfg Γ Λ σ) =
      TM2.init inputStack input := by
  simp only [mapCfg, TM2.init, Option.map_some, numberLabel_default]
  rfl

omit [DecidableEq Λ] in
theorem decodeCfg_init [DecidableEq K] [Inhabited σ] (labels : List Λ)
    (inputStack : K) (input : List (Γ inputStack)) :
    decodeCfg labels (TM2.init inputStack input) =
      (TM2.init inputStack input : TM2.Cfg Γ Λ σ) := rfl

/-- Ordinary TM2 evaluation has the same domain on every input and chosen stack. -/
theorem numberProgram_dom [DecidableEq K] [Inhabited σ]
    (machine : Λ → TM2.Stmt Γ Λ σ) (labels : List Λ)
    (supported : TM2.Supports machine (default :: labels).toFinset)
    (inputStack : K) (input : List (Γ inputStack)) :
    (TM2.eval (numberProgram machine labels) inputStack input).Dom ↔
      (TM2.eval machine inputStack input).Dom :=
  (tr_eval_dom (decode_respects machine labels supported)
    (decodeCfg_init labels inputStack input)).symm

theorem numberProgram_supports (machine : Λ → TM2.Stmt Γ Λ σ) (labels : List Λ) :
    TM2.Supports (numberProgram machine labels) Finset.univ := by
  refine ⟨Finset.mem_univ _, fun state _ ↦ ?_⟩
  generalize numberProgram machine labels state = stmt
  induction stmt <;> simp_all [TM2.SupportsStmt]

theorem initialFirst_support (machine : Λ → TM2.Stmt Γ Λ σ) (labels : List Λ)
    (supported : TM2.Supports machine labels.toFinset) :
    TM2.Supports machine (default :: labels).toFinset := by
  simpa only [List.toFinset_cons, Finset.insert_eq_of_mem supported.1] using supported

theorem numberProgram_dom_of_support [DecidableEq K] [Inhabited σ]
    (machine : Λ → TM2.Stmt Γ Λ σ) (labels : List Λ)
    (supported : TM2.Supports machine labels.toFinset)
    (inputStack : K) (input : List (Γ inputStack)) :
    (TM2.eval (numberProgram machine labels) inputStack input).Dom ↔
      (TM2.eval machine inputStack input).Dom :=
  numberProgram_dom machine labels (initialFirst_support machine labels supported) inputStack input

end Numbering

section Cache
variable [Inhabited σ] [DecidableEq σ]

/-- Materialize every goto's complete store table; no tape-head assumption is needed in TM2. -/
def memoStmt (stores : List σ) : TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ σ
  | .push k f next => .push k f (memoStmt stores next)
  | .peek k f next => .peek k f (memoStmt stores next)
  | .pop k f next => .pop k f (memoStmt stores next)
  | .load f next => .load f (memoStmt stores next)
  | .branch p first second => .branch p (memoStmt stores first) (memoStmt stores second)
  | .goto target =>
    let table := cachedStore stores target
    .goto table.get
  | .halt => .halt

theorem memoStmt_eq (stores : List σ) (cover : ∀ store, store ∈ stores)
    (stmt : TM2.Stmt Γ Λ σ) : memoStmt stores stmt = stmt := by
  induction stmt with
  | push k f next ih => exact congrArg (TM2.Stmt.push k f) ih
  | peek k f next ih => exact congrArg (TM2.Stmt.peek k f) ih
  | pop k f next ih => exact congrArg (TM2.Stmt.pop k f) ih
  | load f next ih => exact congrArg (TM2.Stmt.load f) ih
  | branch p first second left right => simp only [memoStmt, left, right]
  | goto target =>
    change TM2.Stmt.goto (memoStore stores target) = TM2.Stmt.goto target
    rw [memoStore_eq stores cover]
  | halt => rfl

/-- Nominal row data is constructed once, with numeric control and captured goto store tables. -/
@[noinline] def cachedProgram {n : Nat} (stores : List σ)
    (machine : Fin n → TM2.Stmt Γ (Fin n) σ) :
    CachedFunction (Fin n) (TM2.Stmt Γ (Fin n) σ) :=
  ⟨Array.ofFn (fun state ↦ memoStmt stores (machine state)), Fin.val, .halt⟩

theorem cachedProgram_eq {n : Nat} (stores : List σ) (cover : ∀ store, store ∈ stores)
    (machine : Fin n → TM2.Stmt Γ (Fin n) σ) :
    (cachedProgram stores machine).get = machine := by
  funext state
  simp [cachedProgram, CachedFunction.get, memoStmt_eq stores cover]

/-- Number and materialize the finite frontend before any tape lowering constructs closures. -/
@[noinline] def cachedNumberProgram [Inhabited Λ] [DecidableEq Λ]
    (stores : List σ) (machine : Λ → TM2.Stmt Γ Λ σ) (labels : List Λ) :
    CachedFunction (Fin (labels.length + 1)) (TM2.Stmt Γ (Fin (labels.length + 1)) σ) :=
  cachedProgram stores (numberProgram machine labels)

theorem cachedNumberProgram_eq [Inhabited Λ] [DecidableEq Λ]
    (stores : List σ) (cover : ∀ store, store ∈ stores)
    (machine : Λ → TM2.Stmt Γ Λ σ) (labels : List Λ) :
    (cachedNumberProgram stores machine labels).get = numberProgram machine labels :=
  cachedProgram_eq stores cover _

theorem cachedNumberProgram_supports [Inhabited Λ] [DecidableEq Λ]
    (stores : List σ) (cover : ∀ store, store ∈ stores)
    (machine : Λ → TM2.Stmt Γ Λ σ) (labels : List Λ) :
    TM2.Supports (cachedNumberProgram stores machine labels).get Finset.univ := by
  rw [cachedNumberProgram_eq stores cover]
  exact numberProgram_supports machine labels

theorem cachedNumberProgram_dom_of_support [DecidableEq K] [Inhabited Λ] [DecidableEq Λ]
    (stores : List σ) (cover : ∀ store, store ∈ stores)
    (machine : Λ → TM2.Stmt Γ Λ σ) (labels : List Λ)
    (supported : TM2.Supports machine labels.toFinset)
    (inputStack : K) (input : List (Γ inputStack)) :
    (TM2.eval (cachedNumberProgram stores machine labels).get inputStack input).Dom ↔
      (TM2.eval machine inputStack input).Dom := by
  rw [cachedNumberProgram_eq stores cover]
  exact numberProgram_dom_of_support machine labels supported inputStack input

end Cache
end ConjectureMachines.Compilation.TM2Number
