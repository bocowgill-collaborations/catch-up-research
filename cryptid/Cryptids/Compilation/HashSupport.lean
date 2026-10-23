/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.Finite
public import Std.Data.HashSet.Lemmas

/-! Constructive hashed support enumeration. Hashes affect performance, never equality. -/
@[expose] public section
namespace ConjectureMachines.Compilation
open Turing

/-- A deterministic structural hash. Sampling function values is sufficient: collisions are
resolved by the full proved decidable equality, never by treating hashes as identities. -/
def sampleStmtHash {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited σ]
    [Hashable Γ] [Hashable Λ] [Hashable σ] : TM1.Stmt Γ Λ σ → UInt64
  | .move d q => mixHash (if d = .left then 0 else 1) (sampleStmtHash q)
  | .write f q => mixHash 2 (mixHash (hash (f default default)) (sampleStmtHash q))
  | .load f q => mixHash 3 (mixHash (hash (f default default)) (sampleStmtHash q))
  | .branch f q r => mixHash 4 (mixHash (hash (f default default))
      (mixHash (sampleStmtHash q) (sampleStmtHash r)))
  | .goto f => mixHash 5 (hash (f default default))
  | .halt => 6

instance stmtHashable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited σ]
    [Hashable Γ] [Hashable Λ] [Hashable σ] : Hashable (TM1.Stmt Γ Λ σ) :=
  ⟨sampleStmtHash⟩

instance blockLabelHashable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited σ]
    [Hashable Γ] [Hashable Λ] [Hashable σ] : Hashable (TM1to1.Λ' Γ Λ σ) where
  hash
    | .normal l => mixHash 0 (hash l)
    | .write a q => mixHash 1 (mixHash (hash a) (hash q))

/-- Deterministic finite enumeration with duplicates removed using extensional equality. -/
def hashUnique {α : Type*} [DecidableEq α] [Hashable α] (xs : List α) : List α :=
  (Std.HashSet.ofList xs).toList

theorem mem_hashUnique {α : Type*} [DecidableEq α] [Hashable α] (xs : List α) (a : α) :
    a ∈ hashUnique xs ↔ a ∈ xs := by
  simp [hashUnique, Std.HashSet.mem_toList]

end ConjectureMachines.Compilation
