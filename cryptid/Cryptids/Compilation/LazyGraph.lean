/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.GraphPost

/-! # Function-backed finite Boolean graphs and direct numeric Post lookup

The vector graph is a mathematical interpretation. Executable lookup uses only the supplied
node and entry functions; it never constructs that vector.
-/

@[expose] public section
namespace ConjectureMachines.Compilation.LazyGraph
open Turing

/-- A finite first-order graph presented by getters, with an erased descent certificate. -/
structure Graph (n k labels : Nat) where
  node : Fin n → BoolGraph.Node n k labels
  entry : Fin labels → Fin n
  below : ∀ i child, child ∈ (node i).children → child.val < i.val

/-- Mathematical vector interpretation; this is absent from executable row lookup. -/
def asGraph {n k labels : Nat} (g : Graph n k labels) : BoolGraph.Graph n k labels where
  nodes := Vector.ofFn g.node
  entries := Vector.ofFn g.entry
  below i child h := g.below i child (by simpa [Vector.get, Fin.cast] using h)

@[simp] theorem asGraph_node {n k labels : Nat} (g : Graph n k labels) (i : Fin n) :
    (asGraph g).nodes.get i = g.node i := by simp [asGraph, Vector.get, Fin.cast]

@[simp] theorem asGraph_entry {n k labels : Nat} (g : Graph n k labels) (i : Fin labels) :
    (asGraph g).entries.get i = g.entry i := by simp [asGraph, Vector.get, Fin.cast]

/-- Direct instruction lookup. Only load and branch follow decreasing syntax children. -/
def trAux {n k labels : Nat} (g : Graph n k labels) (bit : Bool)
    (i : Fin n) (value : Fin k) : GraphPost.Descriptor n k × TM0.Stmt Bool :=
  match _h : g.node i with
  | .move dir child => ((some child, value), .move dir)
  | .write table child => ((some child, value), .write (table.read bit value))
  | .load table child => trAux g bit child (table.read bit value)
  | .branch table left right =>
      if table.read bit value then trAux g bit left value else trAux g bit right value
  | .goto table => ((some (g.entry (table.read bit value)), value), .write bit)
  | .halt => ((none, value), .write bit)
termination_by i.val
decreasing_by all_goals exact g.below i _ (by simp [_h, BoolGraph.Node.children])

theorem trAux_move {n k labels : Nat} (g : Graph n k labels) (bit : Bool)
    (i child : Fin n) (value : Fin k) (dir : Dir) (row : g.node i = .move dir child) :
    trAux g bit i value = ((some child, value), .move dir) := by rw [trAux, row]

theorem trAux_write {n k labels : Nat} (g : Graph n k labels) (bit : Bool)
    (i child : Fin n) (value : Fin k) (table : BoolGraph.Table k Bool)
    (row : g.node i = .write table child) :
    trAux g bit i value = ((some child, value), .write (table.read bit value)) := by
  rw [trAux, row]

theorem trAux_load {n k labels : Nat} (g : Graph n k labels) (bit : Bool)
    (i child : Fin n) (value : Fin k) (table : BoolGraph.Table k (Fin k))
    (row : g.node i = .load table child) :
    trAux g bit i value = trAux g bit child (table.read bit value) := by rw [trAux, row]

theorem trAux_branch {n k labels : Nat} (g : Graph n k labels) (bit : Bool)
    (i left right : Fin n) (value : Fin k) (table : BoolGraph.Table k Bool)
    (row : g.node i = .branch table left right) :
    trAux g bit i value =
      if table.read bit value then trAux g bit left value else trAux g bit right value := by
  rw [trAux, row]

theorem trAux_goto {n k labels : Nat} (g : Graph n k labels) (bit : Bool)
    (i : Fin n) (value : Fin k) (table : BoolGraph.Table k (Fin labels))
    (row : g.node i = .goto table) :
    trAux g bit i value = ((some (g.entry (table.read bit value)), value), .write bit) := by
  rw [trAux, row]

theorem trAux_halt {n k labels : Nat} (g : Graph n k labels) (bit : Bool)
    (i : Fin n) (value : Fin k) (row : g.node i = .halt) :
    trAux g bit i value = ((none, value), .write bit) := by rw [trAux, row]

/-- Direct lookup agrees with the vector backend on every node, bit and store. -/
theorem trAux_eq {n k labels : Nat} (g : Graph n k labels) (bit : Bool)
    (i : Fin n) (value : Fin k) :
    trAux g bit i value = GraphPost.trAux (asGraph g) bit i value := by
  rw [trAux, GraphPost.trAux, asGraph_node]
  cases h : g.node i <;> simp only []
  case load table child => exact trAux_eq g bit child (table.read bit value)
  case branch table left right =>
    cases table.read bit value <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact trAux_eq g bit right value
    · exact trAux_eq g bit left value
  case goto => rw [asGraph_entry]
termination_by i.val
decreasing_by all_goals exact g.below i _ (by simp [h, BoolGraph.Node.children])

/-- State zero uses the direct initial entry; all other states use arithmetic unpacking. -/
def descriptor {n k labels : Nat} [NeZero k] [NeZero labels] (g : Graph n k labels)
    (q : Fin (GraphPost.stateCount n k)) : GraphPost.Descriptor n k :=
  (GraphPost.unpack q).getD (some (g.entry 0), 0)

/-- Numeric Post rows computed without allocating the graph or enumerating its support. -/
def machine {n k labels : Nat} [NeZero k] [NeZero labels] (g : Graph n k labels) :
    TM0.Machine Bool (Fin (GraphPost.stateCount n k)) := fun q bit ↦
  match descriptor g q with
  | (none, _) => none
  | (some pc, value) =>
      let result := trAux g bit pc value
      some (GraphPost.encode result.1, result.2)

theorem descriptor_eq {n k labels : Nat} [NeZero k] [NeZero labels]
    (g : Graph n k labels) (q : Fin (GraphPost.stateCount n k)) :
    descriptor g q = GraphPost.descriptor (asGraph g) q := by
  simp only [descriptor, GraphPost.descriptor, asGraph_entry]

/-- Equality of complete numeric transition functions, including missing transitions. -/
theorem machine_eq {n k labels : Nat} [NeZero k] [NeZero labels] (g : Graph n k labels) :
    machine g = GraphPost.machine (asGraph g) := by
  funext q bit
  simp only [machine, GraphPost.machine, descriptor_eq, trAux_eq]
  rfl

@[simp] theorem descriptor_encode {n k labels : Nat} [NeZero k] [NeZero labels]
    (g : Graph n k labels) (d : GraphPost.Descriptor n k) :
    descriptor g (GraphPost.encode d) = d := by
  simp [descriptor]

@[simp] theorem descriptor_zero {n k labels : Nat} [NeZero k] [NeZero labels]
    (g : Graph n k labels) : descriptor g 0 = (some (g.entry 0), 0) := rfl

@[simp] theorem machine_halted {n k labels : Nat} [NeZero k] [NeZero labels]
    (g : Graph n k labels) (value : Fin k) (bit : Bool) :
    machine g (GraphPost.encode (none, value)) bit = none := by simp [machine]

@[simp] theorem machine_running {n k labels : Nat} [NeZero k] [NeZero labels]
    (g : Graph n k labels) (pc : Fin n) (value : Fin k) (bit : Bool) :
    machine g (GraphPost.encode (some pc, value)) bit =
      some (GraphPost.encode (trAux g bit pc value).1, (trAux g bit pc value).2) := by
  simp [machine]

/-- State zero executes the initial entry with store zero and the actual scanned bit. -/
theorem machine_zero {n k labels : Nat} [NeZero k] [NeZero labels]
    (g : Graph n k labels) (bit : Bool) :
    machine g 0 bit =
      some (GraphPost.encode (trAux g bit (g.entry 0) 0).1,
        (trAux g bit (g.entry 0) 0).2) := rfl

/-- No paid controls are removed: initial, running and halted stores all remain present. -/
theorem stateCount_eq (n k : Nat) : GraphPost.stateCount n k = 1 + (n + 1) * k := rfl

/-- Mathematical decoding only; executable lookup does not call this interpretation. -/
def decodeState {n k labels : Nat} {σ : Type} [NeZero k] [NeZero labels]
    (g : Graph n k labels) (store : Fin k ≃ σ) :
    Fin (GraphPost.stateCount n k) → TM1to0.Λ' (BoolGraph.machine (asGraph g) store) :=
  GraphPost.decodeState (asGraph g) store

/-- Every row has the sealed backend's exact local certificate. -/
theorem rows {n k labels : Nat} {σ : Type} [NeZero k] [NeZero labels] [Inhabited σ]
    (g : Graph n k labels) (store : Fin k ≃ σ) :
    LocalCertificate.PostRows (machine g) (TM1to0.tr (BoolGraph.machine (asGraph g) store))
      (decodeState g store) := by
  rw [machine_eq]
  exact GraphPost.rows (asGraph g) store

/-- The distinguished initial state is the source entry at its actual default store. -/
theorem initial {n k labels : Nat} {σ : Type} [NeZero k] [NeZero labels] [Inhabited σ]
    (g : Graph n k labels) (store : Fin k ≃ σ) (zero : store 0 = default) :
    decodeState g store 0 = default := GraphPost.initial (asGraph g) store zero

/-- Initial configuration decoding preserves the entire arbitrary input tape. -/
theorem init_decode {n k labels : Nat} {σ : Type} [NeZero k] [NeZero labels] [Inhabited σ]
    (g : Graph n k labels) (store : Fin k ≃ σ) (zero : store 0 = default)
    (input : List Bool) :
    LocalCertificate.decodePostCfg (decodeState g store) (TM0.init input) = TM0.init input :=
  GraphPost.init_decode (asGraph g) store zero input

/-- Exact one-step correspondence on all configurations, including halted controls. -/
theorem step_decode {n k labels : Nat} {σ : Type} [NeZero k] [NeZero labels] [Inhabited σ]
    (g : Graph n k labels) (store : Fin k ≃ σ)
    (cfg : TM0.Cfg Bool (Fin (GraphPost.stateCount n k))) :
    (TM0.step (machine g) cfg).map
      (LocalCertificate.decodePostCfg (decodeState g store)) =
      TM0.step (TM1to0.tr (BoolGraph.machine (asGraph g) store))
        (LocalCertificate.decodePostCfg (decodeState g store) cfg) := by
  rw [machine_eq]
  exact GraphPost.step_decode (asGraph g) store cfg

/-- Complete terminal configurations, including final tapes, decode exactly. -/
theorem eval_decode {n k labels : Nat} {σ : Type} [NeZero k] [NeZero labels] [Inhabited σ]
    (g : Graph n k labels) (store : Fin k ≃ σ) (zero : store 0 = default)
    (input : List Bool) :
    StateTransition.eval (TM0.step (TM1to0.tr (BoolGraph.machine (asGraph g) store)))
        (TM0.init input) =
      (StateTransition.eval (TM0.step (machine g)) (TM0.init input)).map
        (LocalCertificate.decodePostCfg (decodeState g store)) := by
  rw [machine_eq]
  exact GraphPost.eval_decode (asGraph g) store zero input

/-- Equality of partial outputs on every input, without a termination assumption. -/
theorem eval_eq {n k labels : Nat} {σ : Type} [NeZero k] [NeZero labels] [Inhabited σ]
    (g : Graph n k labels) (store : Fin k ≃ σ) (zero : store 0 = default)
    (input : List Bool) :
    TM0.eval (machine g) input = TM1.eval (BoolGraph.machine (asGraph g) store) input := by
  rw [machine_eq]
  exact GraphPost.eval_eq (asGraph g) store zero input

/-- Both halting directions hold for exactly the same arbitrary input tape. -/
theorem halts_iff {n k labels : Nat} {σ : Type} [NeZero k] [NeZero labels] [Inhabited σ]
    (g : Graph n k labels) (store : Fin k ≃ σ) (zero : store 0 = default)
    (input : List Bool) :
    (TM0.eval (machine g) input).Dom ↔
      (TM1.eval (BoolGraph.machine (asGraph g) store) input).Dom := by
  rw [machine_eq]
  exact GraphPost.halts_iff (asGraph g) store zero input

end ConjectureMachines.Compilation.LazyGraph
