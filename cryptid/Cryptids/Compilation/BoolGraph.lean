/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Finite first-order Boolean TM1 syntax graphs

Every observable function is a literal vector with exactly `2 * k` cells. Syntax children
point strictly backwards. Gotos use a separate entry vector and may form control loops.
-/

@[expose] public section
namespace ConjectureMachines.Compilation.BoolGraph
open Turing

/-- A finite table, indexed first by the scanned bit and then by the store. -/
abbrev Table (k : Nat) (α : Type) := Vector α (2 * k)

/-- Read one of the actual finite table cells. -/
def Table.read {k : Nat} {α : Type} (table : Table k α) (bit : Bool) (store : Fin k) : α :=
  table.get (finProdFinEquiv ((if bit then 1 else 0 : Fin 2), store))

/-- First-order syntax. Tables contain data, never callback functions. -/
inductive Node (n k labels : Nat) where
  | move (dir : Dir) (child : Fin n)
  | write (table : Table k Bool) (child : Fin n)
  | load (table : Table k (Fin k)) (child : Fin n)
  | branch (table : Table k Bool) (left right : Fin n)
  | goto (table : Table k (Fin labels))
  | halt

/-- Immediate syntax children; goto destinations are source labels, not syntax children. -/
def Node.children {n k labels : Nat} : Node n k labels → List (Fin n)
  | .move _ child | .write _ child | .load _ child => [child]
  | .branch _ left right => [left, right]
  | .goto _ | .halt => []

/-- A literal node vector, a literal entry vector, and an erased topology certificate. -/
structure Graph (n k labels : Nat) where
  nodes : Vector (Node n k labels) n
  entries : Vector (Fin n) labels
  below : ∀ i child, child ∈ (nodes.get i).children → child.val < i.val

/-- Decode the graph to Mathlib syntax. The store equivalence need not be an enumeration
procedure; the graph itself stores only finite indices and table cells. -/
def decode {n k labels : Nat} {σ : Type} (g : Graph n k labels)
    (store : Fin k ≃ σ) (i : Fin n) : TM1.Stmt Bool (Fin labels) σ :=
  match _h : g.nodes.get i with
  | .move dir child => .move dir (decode g store child)
  | .write table child =>
      .write (fun bit value ↦ table.read bit (store.symm value)) (decode g store child)
  | .load table child =>
      .load (fun bit value ↦ store (table.read bit (store.symm value))) (decode g store child)
  | .branch table left right =>
      .branch (fun bit value ↦ table.read bit (store.symm value))
        (decode g store left) (decode g store right)
  | .goto table => .goto (fun bit value ↦ table.read bit (store.symm value))
  | .halt => .halt
termination_by i.val
decreasing_by all_goals exact g.below i _ (by simp [_h, Node.children])

theorem decode_move {n k labels : Nat} {σ : Type} (g : Graph n k labels)
    (store : Fin k ≃ σ) (i child : Fin n) (dir : Dir)
    (row : g.nodes.get i = .move dir child) :
    decode g store i = .move dir (decode g store child) := by rw [decode, row]

theorem decode_write {n k labels : Nat} {σ : Type} (g : Graph n k labels)
    (store : Fin k ≃ σ) (i child : Fin n) (table : Table k Bool)
    (row : g.nodes.get i = .write table child) :
    decode g store i = .write (fun bit value ↦ table.read bit (store.symm value))
      (decode g store child) := by rw [decode, row]

theorem decode_load {n k labels : Nat} {σ : Type} (g : Graph n k labels)
    (store : Fin k ≃ σ) (i child : Fin n) (table : Table k (Fin k))
    (row : g.nodes.get i = .load table child) :
    decode g store i = .load (fun bit value ↦ store (table.read bit (store.symm value)))
      (decode g store child) := by rw [decode, row]

theorem decode_branch {n k labels : Nat} {σ : Type} (g : Graph n k labels)
    (store : Fin k ≃ σ) (i left right : Fin n) (table : Table k Bool)
    (row : g.nodes.get i = .branch table left right) :
    decode g store i = .branch (fun bit value ↦ table.read bit (store.symm value))
      (decode g store left) (decode g store right) := by rw [decode, row]

theorem decode_goto {n k labels : Nat} {σ : Type} (g : Graph n k labels)
    (store : Fin k ≃ σ) (i : Fin n) (table : Table k (Fin labels))
    (row : g.nodes.get i = .goto table) :
    decode g store i = .goto (fun bit value ↦ table.read bit (store.symm value)) := by
  rw [decode, row]

theorem decode_halt {n k labels : Nat} {σ : Type} (g : Graph n k labels)
    (store : Fin k ≃ σ) (i : Fin n) (row : g.nodes.get i = .halt) :
    decode g store i = .halt := by rw [decode, row]

/-- Source labels select decoded roots. Entry references are allowed to cycle through goto. -/
def machine {n k labels : Nat} {σ : Type} (g : Graph n k labels)
    (store : Fin k ≃ σ) (label : Fin labels) : TM1.Stmt Bool (Fin labels) σ :=
  decode g store (g.entries.get label)

end ConjectureMachines.Compilation.BoolGraph
