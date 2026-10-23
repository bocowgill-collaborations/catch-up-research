/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.BoolGraph
public import Cryptids.Compilation.LocalCertificate

/-! # Direct finite numeric Post lowering of Boolean syntax graphs -/

@[expose] public section
namespace ConjectureMachines.Compilation.GraphPost
open Turing BoolGraph

/-- Runtime descriptors contain only a finite syntax PC and a finite store index. -/
abbrev Descriptor (n k : Nat) := Option (Fin n) × Fin k

/-- One Post instruction. Load and branch nodes descend without consuming a Post step. -/
def trAux {n k labels : Nat} (g : Graph n k labels) (bit : Bool)
    (i : Fin n) (value : Fin k) : Descriptor n k × TM0.Stmt Bool :=
  match _h : g.nodes.get i with
  | .move dir child => ((some child, value), .move dir)
  | .write table child => ((some child, value), .write (table.read bit value))
  | .load table child => trAux g bit child (table.read bit value)
  | .branch table left right =>
      if table.read bit value then trAux g bit left value else trAux g bit right value
  | .goto table => ((some (g.entries.get (table.read bit value)), value), .write bit)
  | .halt => ((none, value), .write bit)
termination_by i.val
decreasing_by all_goals exact g.below i _ (by simp [_h, Node.children])

theorem trAux_move {n k labels : Nat} (g : Graph n k labels) (bit : Bool)
    (i child : Fin n) (value : Fin k) (dir : Dir)
    (row : g.nodes.get i = .move dir child) :
    trAux g bit i value = ((some child, value), .move dir) := by rw [trAux, row]

theorem trAux_write {n k labels : Nat} (g : Graph n k labels) (bit : Bool)
    (i child : Fin n) (value : Fin k) (table : Table k Bool)
    (row : g.nodes.get i = .write table child) :
    trAux g bit i value = ((some child, value), .write (table.read bit value)) := by
  rw [trAux, row]

theorem trAux_load {n k labels : Nat} (g : Graph n k labels) (bit : Bool)
    (i child : Fin n) (value : Fin k) (table : Table k (Fin k))
    (row : g.nodes.get i = .load table child) :
    trAux g bit i value = trAux g bit child (table.read bit value) := by rw [trAux, row]

theorem trAux_branch {n k labels : Nat} (g : Graph n k labels) (bit : Bool)
    (i left right : Fin n) (value : Fin k) (table : Table k Bool)
    (row : g.nodes.get i = .branch table left right) :
    trAux g bit i value =
      if table.read bit value then trAux g bit left value else trAux g bit right value := by
  rw [trAux, row]

theorem trAux_goto {n k labels : Nat} (g : Graph n k labels) (bit : Bool)
    (i : Fin n) (value : Fin k) (table : Table k (Fin labels))
    (row : g.nodes.get i = .goto table) :
    trAux g bit i value =
      ((some (g.entries.get (table.read bit value)), value), .write bit) := by rw [trAux, row]

theorem trAux_halt {n k labels : Nat} (g : Graph n k labels) (bit : Bool)
    (i : Fin n) (value : Fin k) (row : g.nodes.get i = .halt) :
    trAux g bit i value = ((none, value), .write bit) := by rw [trAux, row]

/-- Decode a finite graph descriptor into Mathlib's actual statement/store control. -/
def decodeDescriptor {n k labels : Nat} {σ : Type} (g : Graph n k labels)
    (store : Fin k ≃ σ) (d : Descriptor n k) : TM1to0.Λ' (BoolGraph.machine g store) :=
  (d.1.map (BoolGraph.decode g store), store d.2)

/-- Exact local lowering, including branch/load chains, goto loops and halts. -/
theorem trAux_correct {n k labels : Nat} {σ : Type} (g : Graph n k labels)
    (store : Fin k ≃ σ) (bit : Bool) (i : Fin n) (value : Fin k) :
    (decodeDescriptor g store (trAux g bit i value).1, (trAux g bit i value).2) =
      TM1to0.trAux (BoolGraph.machine g store) bit (BoolGraph.decode g store i) (store value) := by
  rw [trAux, BoolGraph.decode]
  cases h : g.nodes.get i <;> simp only [TM1to0.trAux, Equiv.symm_apply_apply]
  case move => rfl
  case write => rfl
  case load table child => exact trAux_correct g store bit child (table.read bit value)
  case branch table left right =>
    cases table.read bit value <;> simp only [Bool.false_eq_true,
      ↓reduceIte, Bool.cond_false, Bool.cond_true]
    · exact trAux_correct g store bit right value
    · exact trAux_correct g store bit left value
  case goto => rfl
  case halt => rfl
termination_by i.val
decreasing_by all_goals exact g.below i _ (by simp [h, Node.children])

/-- One initial state plus every optional node/store pair, including halted controls. -/
def stateCount (n k : Nat) : Nat := 1 + (n + 1) * k

instance {n k : Nat} : NeZero (stateCount n k) := ⟨by simp [stateCount]⟩

/-- Constant-time finite arithmetic packing, with no search over syntax or support. -/
def descriptorEquiv {n k : Nat} : Descriptor n k ≃ Fin ((n + 1) * k) :=
  (Equiv.prodCongr (finSuccEquiv n).symm (Equiv.refl (Fin k))).trans finProdFinEquiv

/-- Numeric successors always use the descriptor part, leaving state zero distinguished. -/
def encode {n k : Nat} (d : Descriptor n k) : Fin (stateCount n k) :=
  finSumFinEquiv (Sum.inr (descriptorEquiv d))

/-- State zero has no descriptor of its own; it is supplied by the graph's initial root. -/
def unpack {n k : Nat} (q : Fin (stateCount n k)) : Option (Descriptor n k) :=
  match finSumFinEquiv.symm q with
  | .inl _ => none
  | .inr d => some (descriptorEquiv.symm d)

@[simp] theorem unpack_encode {n k : Nat} (d : Descriptor n k) :
    unpack (encode d) = some d := by
  simp [unpack, encode]

@[simp] theorem unpack_zero {n k : Nat} : unpack (0 : Fin (stateCount n k)) = none := rfl

/-- No two descriptor states are silently identified. -/
theorem encode_injective {n k : Nat} : Function.Injective (@encode n k) := by
  intro a b equal
  have decoded := congrArg unpack equal
  simpa only [unpack_encode, Option.some.injEq] using decoded

/-- Every emitted successor pays for a nonzero descriptor state. -/
theorem encode_ne_zero {n k : Nat} (d : Descriptor n k) : encode d ≠ 0 := by
  intro equal
  have decoded := congrArg unpack equal
  simp only [unpack_encode, unpack_zero] at decoded
  cases decoded

/-- Interpret state zero as the actual initial source statement and default finite store. -/
def descriptor {n k labels : Nat} [NeZero k] [NeZero labels] (g : Graph n k labels)
    (q : Fin (stateCount n k)) : Descriptor n k :=
  (unpack q).getD (some (g.entries.get 0), 0)

@[simp] theorem descriptor_encode {n k labels : Nat} [NeZero k] [NeZero labels]
    (g : Graph n k labels) (d : Descriptor n k) : descriptor g (encode d) = d := by
  simp [descriptor]

@[simp] theorem descriptor_zero {n k labels : Nat} [NeZero k] [NeZero labels]
    (g : Graph n k labels) : descriptor g 0 = (some (g.entries.get 0), 0) := rfl

/-- Direct numeric Post program. Halted descriptors have a missing transition. -/
def machine {n k labels : Nat} [NeZero k] [NeZero labels] (g : Graph n k labels) :
    TM0.Machine Bool (Fin (stateCount n k)) := fun q bit ↦
  match descriptor g q with
  | (none, _) => none
  | (some pc, value) =>
      let result := trAux g bit pc value
      some (encode result.1, result.2)

/-- Materialize all numeric rows once as a literal array-backed vector of bit rows. -/
def program {n k labels : Nat} [NeZero k] [NeZero labels] (g : Graph n k labels) :
    Vector (Vector (Option (Fin (stateCount n k) × TM0.Stmt Bool)) 2) (stateCount n k) :=
  Vector.ofFn (fun q ↦ Vector.ofFn (fun bit ↦ machine g q (bit == 1)))

/-- Execute a precomputed first-order row vector. -/
def programMachine {n k : Nat}
    (table : Vector (Vector (Option (Fin (stateCount n k) × TM0.Stmt Bool)) 2)
      (stateCount n k)) : TM0.Machine Bool (Fin (stateCount n k)) :=
  fun q bit ↦ (table.get q).get (if bit then 1 else 0)

/-- Materialization preserves every transition, including all missing transitions. -/
theorem program_correct {n k labels : Nat} [NeZero k] [NeZero labels] (g : Graph n k labels) :
    programMachine (program g) = machine g := by
  funext q bit
  cases bit <;> simp [programMachine, program, Vector.get, Fin.cast]

/-- The materialized vector has exactly the advertised number of numeric controls. -/
theorem program_size {n k labels : Nat} [NeZero k] [NeZero labels] (g : Graph n k labels) :
    (program g).toArray.size = stateCount n k := (program g).size_toArray

/-- Decode numeric control to the exact Mathlib translated control; the tape is untouched. -/
def decodeState {n k labels : Nat} {σ : Type} [NeZero k] [NeZero labels]
    (g : Graph n k labels) (store : Fin k ≃ σ) (q : Fin (stateCount n k)) :
    TM1to0.Λ' (BoolGraph.machine g store) :=
  decodeDescriptor g store (descriptor g q)

/-- Every row, including missing transitions, is certified against actual `TM1to0.tr`. -/
theorem rows {n k labels : Nat} {σ : Type} [NeZero k] [NeZero labels] [Inhabited σ]
    (g : Graph n k labels) (store : Fin k ≃ σ) :
    LocalCertificate.PostRows (machine g) (TM1to0.tr (BoolGraph.machine g store))
      (decodeState g store) := by
  intro q bit
  unfold machine decodeState
  cases h : descriptor g q with
  | mk pc value =>
    cases pc with
    | none => rfl
    | some pc =>
      simp only [Option.map_some, descriptor_encode]
      exact congrArg some (trAux_correct g store bit pc value)

/-- State zero decodes to `(some (M default), default)`, never to a halted control. -/
theorem initial {n k labels : Nat} {σ : Type} [NeZero k] [NeZero labels] [Inhabited σ]
    (g : Graph n k labels) (store : Fin k ≃ σ) (zero : store 0 = default) :
    decodeState g store 0 = default := by
  change (some (BoolGraph.machine g store 0), store 0) =
    (some (BoolGraph.machine g store default), default)
  rw [zero]
  rfl

/-- The advertised count includes initial control, all node/store pairs and all halted stores. -/
theorem stateCount_eq (n k : Nat) : stateCount n k = 1 + k * (n + 1) := by
  simp [stateCount, Nat.mul_comm]

@[simp] theorem machine_halted {n k labels : Nat} [NeZero k] [NeZero labels]
    (g : Graph n k labels) (value : Fin k) (bit : Bool) :
    machine g (encode (none, value)) bit = none := by
  simp [machine]

@[simp] theorem machine_running {n k labels : Nat} [NeZero k] [NeZero labels]
    (g : Graph n k labels) (pc : Fin n) (value : Fin k) (bit : Bool) :
    machine g (encode (some pc, value)) bit =
      some (encode (trAux g bit pc value).1, (trAux g bit pc value).2) := by
  simp [machine]

/-- Initial Post instruction starts at the source entry, not a missing transition. -/
theorem machine_zero {n k labels : Nat} [NeZero k] [NeZero labels]
    (g : Graph n k labels) (bit : Bool) :
    machine g 0 bit =
      some (encode (trAux g bit (g.entries.get 0) 0).1,
        (trAux g bit (g.entries.get 0) 0).2) := rfl

/-- Exact ordinary initialization, including the whole original input tape. -/
theorem init_decode {n k labels : Nat} {σ : Type} [NeZero k] [NeZero labels] [Inhabited σ]
    (g : Graph n k labels) (store : Fin k ≃ σ) (zero : store 0 = default)
    (input : List Bool) :
    LocalCertificate.decodePostCfg (decodeState g store) (TM0.init input) =
      TM0.init input := by
  change TM0.Cfg.mk (decodeState g store 0) _ = TM0.Cfg.mk default _
  rw [initial g store zero]
  rfl

/-- Exact one-step decoding retains the complete tape, including missing transitions. -/
theorem step_decode {n k labels : Nat} {σ : Type} [NeZero k] [NeZero labels] [Inhabited σ]
    (g : Graph n k labels) (store : Fin k ≃ σ)
    (cfg : TM0.Cfg Bool (Fin (stateCount n k))) :
    (TM0.step (machine g) cfg).map
      (LocalCertificate.decodePostCfg (decodeState g store)) =
      TM0.step (TM1to0.tr (BoolGraph.machine g store))
        (LocalCertificate.decodePostCfg (decodeState g store) cfg) :=
  LocalCertificate.post_step_decode _ _ _ (rows g store) cfg

/-- Full terminal configurations decode exactly; this also preserves the complete final tape. -/
theorem eval_decode {n k labels : Nat} {σ : Type} [NeZero k] [NeZero labels] [Inhabited σ]
    (g : Graph n k labels) (store : Fin k ≃ σ) (zero : store 0 = default)
    (input : List Bool) :
    StateTransition.eval (TM0.step (TM1to0.tr (BoolGraph.machine g store))) (TM0.init input) =
      (StateTransition.eval (TM0.step (machine g)) (TM0.init input)).map
        (LocalCertificate.decodePostCfg (decodeState g store)) := by
  simpa only [init_decode g store zero input, Part.map_eq_map] using
    StateTransition.tr_eval' (TM0.step (machine g))
      (TM0.step (TM1to0.tr (BoolGraph.machine g store)))
      (LocalCertificate.decodePostCfg (decodeState g store))
      (LocalCertificate.post_respects _ _ _ (rows g store)) (TM0.init input)

/-- Exact partial output equality, stronger than termination equivalence. -/
theorem eval_eq {n k labels : Nat} {σ : Type} [NeZero k] [NeZero labels] [Inhabited σ]
    (g : Graph n k labels) (store : Fin k ≃ σ) (zero : store 0 = default)
    (input : List Bool) :
    TM0.eval (machine g) input = TM1.eval (BoolGraph.machine g store) input := by
  rw [← TM1to0.tr_eval]
  unfold TM0.eval
  rw [eval_decode g store zero input, Part.map_map]
  rfl

/-- Both termination directions on precisely the same arbitrary input tape. -/
theorem halts_iff {n k labels : Nat} {σ : Type} [NeZero k] [NeZero labels] [Inhabited σ]
    (g : Graph n k labels) (store : Fin k ≃ σ) (zero : store 0 = default)
    (input : List Bool) :
    (TM0.eval (machine g) input).Dom ↔ (TM1.eval (BoolGraph.machine g store) input).Dom := by
  rw [LocalCertificate.post_halts_iff (machine g) (TM1to0.tr (BoolGraph.machine g store))
    (decodeState g store) (rows g store) (initial g store zero) input,
    TM1to0.tr_eval]

/-- The first-order materialized Post rows have the same exact partial tape output. -/
theorem program_eval_eq {n k labels : Nat} {σ : Type}
    [NeZero k] [NeZero labels] [Inhabited σ] (g : Graph n k labels)
    (store : Fin k ≃ σ) (zero : store 0 = default) (input : List Bool) :
    TM0.eval (programMachine (program g)) input =
      TM1.eval (BoolGraph.machine g store) input := by
  rw [program_correct]
  exact eval_eq g store zero input

/-- Both input-domain directions for the materialized numeric rows. -/
theorem program_halts_iff {n k labels : Nat} {σ : Type}
    [NeZero k] [NeZero labels] [Inhabited σ] (g : Graph n k labels)
    (store : Fin k ≃ σ) (zero : store 0 = default) (input : List Bool) :
    (TM0.eval (programMachine (program g)) input).Dom ↔
      (TM1.eval (BoolGraph.machine g store) input).Dom := by
  rw [program_correct]
  exact halts_iff g store zero input

end ConjectureMachines.Compilation.GraphPost
