/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.Block

/-! Proof-preserving finite lookup tables for head-free numeric programs. -/
@[expose] public section
namespace ConjectureMachines.Compilation
open Turing
variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited σ] [DecidableEq σ]

/-- Nominal data prevents the native compiler from eta-expanding a table-building function. -/
structure CachedFunction (α β : Type*) where
  values : Array β
  position : α → ℕ
  fallback : β

def CachedFunction.get {α β : Type*} (table : CachedFunction α β) (a : α) : β :=
  (table.values[table.position a]?).getD table.fallback

/-- Build data once; the result type is a record, rather than a function. -/
@[noinline] def cachedStore (stores : List σ) (f : σ → Λ) : CachedFunction σ Λ :=
  ⟨(stores.map f).toArray, fun v ↦ stores.idxOf v, f default⟩

def memoStore (stores : List σ) (f : σ → Λ) : σ → Λ := (cachedStore stores f).get

theorem memoStore_eq (stores : List σ) (cover : ∀ v, v ∈ stores) (f : σ → Λ) :
    memoStore stores f = f := by
  funext v
  simp [memoStore, cachedStore, CachedFunction.get, List.getElem?_idxOf (cover v)]

/-- Cache goto tables. Other primitives and all continuations are preserved. -/
def memoStmt (stores : List σ) : TM1.Stmt Γ Λ σ → TM1.Stmt Γ Λ σ
  | .move d q => .move d (memoStmt stores q)
  | .write f q => .write f (memoStmt stores q)
  | .load f q => .load f (memoStmt stores q)
  | .branch p q r => .branch p (memoStmt stores q) (memoStmt stores r)
  | .goto f =>
    let table := cachedStore stores (f default)
    .goto fun _ v ↦ table.get v
  | .halt => .halt

theorem memoStmt_eq (stores : List σ) (cover : ∀ v, v ∈ stores)
    (q : TM1.Stmt Γ Λ σ) (hq : Block.AllHeadFree q) : memoStmt stores q = q := by
  induction q with
  | move d q ih => exact congrArg (TM1.Stmt.move d) (ih hq)
  | write f q ih => exact congrArg (TM1.Stmt.write f) (ih hq)
  | load f q ih => exact congrArg (TM1.Stmt.load f) (ih hq)
  | branch p q r ihq ihr => simp only [memoStmt, ihq hq.1, ihr hq.2]
  | goto f =>
    change TM1.Stmt.goto (fun _ v ↦ memoStore stores (f default) v) = TM1.Stmt.goto f
    rw [memoStore_eq stores cover]
    congr 1
    funext a v
    exact (hq a v).symm
  | halt => rfl

/-- Cache all numeric procedures as nominal data before passing them to a compiler. -/
@[noinline] def cachedProgram {n : ℕ} (stores : List σ)
    (M : Fin n → TM1.Stmt Γ (Fin n) σ) :
    CachedFunction (Fin n) (TM1.Stmt Γ (Fin n) σ) :=
  ⟨Array.ofFn (fun q ↦ memoStmt stores (M q)), Fin.val, .halt⟩

/-- Logical lookup interface; callers materialize `cachedProgram` before building closures. -/
def memoProgram {n : ℕ} (stores : List σ) (M : Fin n → TM1.Stmt Γ (Fin n) σ) :
    Fin n → TM1.Stmt Γ (Fin n) σ := (cachedProgram stores M).get

theorem memoProgram_eq {n : ℕ} (stores : List σ) (cover : ∀ v, v ∈ stores)
    (M : Fin n → TM1.Stmt Γ (Fin n) σ) (hM : ∀ q, Block.AllHeadFree (M q)) :
    memoProgram stores M = M := by
  funext q
  simp [memoProgram, cachedProgram, CachedFunction.get, memoStmt_eq stores cover _ (hM q)]
end ConjectureMachines.Compilation
