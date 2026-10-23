/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.LazyGraph
public import Cryptids.Compilation.BinaryTemplates
public import Mathlib.Algebra.BigOperators.Fin

/-! # Arithmetic getters for exact binary block syntax graphs

Computational getters and finite source data are separate from topology and source
refinement proofs. The `Vector.ofFn` graph is a formal view, not a native export plan.
-/

@[expose] public section
namespace ConjectureMachines.Compilation.TemplateGraph
open Turing BoolGraph

set_option backward.isDefEq.respectTransparency false

/-- Rename syntax children without changing finite observable tables or goto labels. -/
def mapNode {a b k labels : Nat} (f : Fin a → Fin b) : Node a k labels → Node b k labels
  | .move dir child => .move dir (f child)
  | .write table child => .write table (f child)
  | .load table child => .load table (f child)
  | .branch table left right => .branch table (f left) (f right)
  | .goto table => .goto table
  | .halt => .halt

@[simp] theorem children_mapNode {a b k labels : Nat} (f : Fin a → Fin b)
    (node : Node a k labels) : (mapNode f node).children = node.children.map f := by
  cases node <;> rfl

/-- A computational getter, with no semantic certificate or materialized node vector. -/
structure Raw (k labels : Nat) where
  count : Nat
  node : Fin count → Node count k labels

/-- Erased topology certificate, kept separate from computational data. -/
def Raw.Valid {k labels : Nat} (raw : Raw k labels) : Prop :=
  ∀ i child, child ∈ (raw.node i).children → child.val < i.val

/-- Append an entire finite node family in one arithmetic layer. Every new child refers
only to the previous layer. Neither old nor new getter is traversed during construction. -/
abbrev Raw.extend {k labels : Nat} (raw : Raw k labels) (extra : Nat)
    (node : Fin extra → Node raw.count k labels) : Raw k labels where
  count := raw.count + extra
  node := Fin.addCases (fun i ↦ mapNode (Fin.castAdd extra) (raw.node i))
    (fun i ↦ mapNode (Fin.castAdd extra) (node i))

@[simp] theorem Raw.extend_old {k labels : Nat} (raw : Raw k labels) (extra : Nat)
    (node : Fin extra → Node raw.count k labels) (i : Fin raw.count) :
    (raw.extend extra node).node (i.castAdd extra) =
      mapNode (Fin.castAdd extra) (raw.node i) := by
  simp [Raw.extend]

@[simp] theorem Raw.extend_new {k labels : Nat} (raw : Raw k labels) (extra : Nat)
    (node : Fin extra → Node raw.count k labels) (i : Fin extra) :
    (raw.extend extra node).node (Fin.natAdd raw.count i) =
      mapNode (Fin.castAdd extra) (node i) := by
  simp [Raw.extend]

/-- Every appended node refers backwards, even when a finite family is empty. -/
theorem Raw.extend_valid {k labels : Nat} (raw : Raw k labels) (valid : raw.Valid)
    (extra : Nat) (node : Fin extra → Node raw.count k labels) :
    (raw.extend extra node).Valid := by
  intro i child member
  induction i using Fin.addCases with
  | left i =>
    rw [Raw.extend_old] at member
    rw [children_mapNode, List.mem_map] at member
    obtain ⟨old, member, rfl⟩ := member
    exact valid i old member
  | right i =>
    rw [Raw.extend_new] at member
    rw [children_mapNode, List.mem_map] at member
    obtain ⟨old, _, rfl⟩ := member
    exact old.isLt.trans_le (Nat.le_add_right _ _)

/-- Decode directly through getters. No vector allocation occurs in this operation. -/
def Raw.decode {k labels : Nat} {σ : Type} (raw : Raw k labels) (valid : raw.Valid)
    (store : Fin k ≃ σ) (i : Fin raw.count) : TM1.Stmt Bool (Fin labels) σ :=
  match _h : raw.node i with
  | .move dir child => .move dir (raw.decode valid store child)
  | .write table child =>
      .write (fun bit value ↦ table.read bit (store.symm value)) (raw.decode valid store child)
  | .load table child =>
      .load (fun bit value ↦ store (table.read bit (store.symm value)))
        (raw.decode valid store child)
  | .branch table left right =>
      .branch (fun bit value ↦ table.read bit (store.symm value))
        (raw.decode valid store left) (raw.decode valid store right)
  | .goto table => .goto (fun bit value ↦ table.read bit (store.symm value))
  | .halt => .halt
termination_by i.val
decreasing_by all_goals exact valid i _ (by simp [_h, Node.children])

/-- Interpret one first-order node with supplied already-decoded children. -/
def buildNode {n k labels : Nat} {σ : Type} (store : Fin k ≃ σ)
    (child : Fin n → TM1.Stmt Bool (Fin labels) σ) : Node n k labels →
      TM1.Stmt Bool (Fin labels) σ
  | .move dir next => .move dir (child next)
  | .write table next => .write (fun bit value ↦ table.read bit (store.symm value)) (child next)
  | .load table next =>
      .load (fun bit value ↦ store (table.read bit (store.symm value))) (child next)
  | .branch table left right =>
      .branch (fun bit value ↦ table.read bit (store.symm value)) (child left) (child right)
  | .goto table => .goto (fun bit value ↦ table.read bit (store.symm value))
  | .halt => .halt

@[simp] theorem buildNode_map {a b k labels : Nat} {σ : Type} (store : Fin k ≃ σ)
    (f : Fin a → Fin b) (child : Fin b → TM1.Stmt Bool (Fin labels) σ)
    (node : Node a k labels) :
    buildNode store child (mapNode f node) = buildNode store (child ∘ f) node := by
  cases node <;> rfl

theorem buildNode_congr {n k labels : Nat} {σ : Type} (store : Fin k ≃ σ)
    (left right : Fin n → TM1.Stmt Bool (Fin labels) σ) (node : Node n k labels)
    (equal : ∀ i, i ∈ node.children → left i = right i) :
    buildNode store left node = buildNode store right node := by
  cases node <;> simp only [buildNode, Node.children, List.mem_cons] at *
  all_goals first | rfl | congr 1 <;> apply equal <;> simp

/-- One guarded unfolding equation is enough to certify an arithmetic getter row. -/
theorem Raw.decode_eq {k labels : Nat} {σ : Type} (raw : Raw k labels) (valid : raw.Valid)
    (store : Fin k ≃ σ) (i : Fin raw.count) :
    raw.decode valid store i = buildNode store (raw.decode valid store) (raw.node i) := by
  rw [Raw.decode]
  cases raw.node i <;> rfl

/-- Extension preserves every earlier node's exact expanded syntax. -/
theorem Raw.decode_extend_old {k labels : Nat} {σ : Type} (raw : Raw k labels)
    (valid : raw.Valid) (extra : Nat) (node : Fin extra → Node raw.count k labels)
    (store : Fin k ≃ σ) (i : Fin raw.count) :
    (raw.extend extra node).decode (raw.extend_valid valid extra node) store (i.castAdd extra) =
      raw.decode valid store i := by
  rw [Raw.decode_eq, Raw.extend_old, buildNode_map, Raw.decode_eq]
  apply buildNode_congr
  intro child member
  exact raw.decode_extend_old valid extra node store child
termination_by i.val
decreasing_by exact valid i _ member

/-- New rows decode by their constructor and the previous layer's decoded children. -/
theorem Raw.decode_extend_new {k labels : Nat} {σ : Type} (raw : Raw k labels)
    (valid : raw.Valid) (extra : Nat) (node : Fin extra → Node raw.count k labels)
    (store : Fin k ≃ σ) (i : Fin extra) :
    (raw.extend extra node).decode (raw.extend_valid valid extra node) store
      (Fin.natAdd raw.count i) = buildNode store (raw.decode valid store) (node i) := by
  rw [Raw.decode_eq, Raw.extend_new, buildNode_map]
  exact buildNode_congr store _ _ _ (fun child _ ↦
    raw.decode_extend_old valid extra node store child)

@[simp] theorem vector_get_ofFn {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by simp [Vector.get, Fin.cast]

/-- Materialize just one observable finite table, never the entire graph. -/
def tableOf {k : Nat} {α : Type} (f : Bool → Fin k → α) : Table k α :=
  Vector.ofFn fun pos ↦ let pair := finProdFinEquiv.symm pos
    f (pair.1 == 1) pair.2

@[simp] theorem tableOf_read {k : Nat} {α : Type} (f : Bool → Fin k → α)
    (bit : Bool) (store : Fin k) : (tableOf f).read bit store = f bit store := by
  unfold tableOf Table.read
  rw [vector_get_ofFn, Equiv.symm_apply_apply]
  cases bit <;> rfl

/-- Root slots are finite arithmetic families. Temporary unused slots are overwritten
before final entries are selected. -/
inductive Ref (n w r u m : Nat) where
  | tail (pc : Fin n) (right : Bool)
  | writerTail (site : Fin w)
  | readLeaf (reader : Fin r) (glyph : Fin m)
  | reader (reader : Fin r)
  | writer (site : Fin w) (glyph : Fin m)
  | mover (mover : Fin u)

/-- Getter state and root maps, with no topology or source semantic proof fields. -/
structure Bundle (n w r u m k : Nat) where
  raw : Raw k (n + w * m)
  root : Ref n w r u m → Fin raw.count

/-- Append a family and replace only the explicitly selected root slots. -/
abbrev Bundle.add {n w r u m k : Nat} (state : Bundle n w r u m k) (extra : Nat)
    (node : Fin extra → Node state.raw.count k (n + w * m))
    (pick : Ref n w r u m → Option (Fin extra)) : Bundle n w r u m k where
  raw := state.raw.extend extra node
  root ref := match pick ref with
    | none => (state.root ref).castAdd extra
    | some i => Fin.natAdd state.raw.count i

@[simp] theorem Bundle.decode_add_old {n w r u m k : Nat} {σ : Type}
    (state : Bundle n w r u m k) (valid : state.raw.Valid) (extra : Nat)
    (node : Fin extra → Node state.raw.count k (n + w * m))
    (pick : Ref n w r u m → Option (Fin extra)) (store : Fin k ≃ σ)
    (ref : Ref n w r u m) (keep : pick ref = none) :
    (state.add extra node pick).raw.decode (state.raw.extend_valid valid extra node) store
      ((state.add extra node pick).root ref) = state.raw.decode valid store (state.root ref) := by
  simp only [Bundle.add, keep]
  exact state.raw.decode_extend_old valid extra node store (state.root ref)

@[simp] theorem Bundle.decode_add_new {n w r u m k : Nat} {σ : Type}
    (state : Bundle n w r u m k) (valid : state.raw.Valid) (extra : Nat)
    (node : Fin extra → Node state.raw.count k (n + w * m))
    (pick : Ref n w r u m → Option (Fin extra)) (store : Fin k ≃ σ)
    (ref : Ref n w r u m) (i : Fin extra) (chosen : pick ref = some i) :
    (state.add extra node pick).raw.decode (state.raw.extend_valid valid extra node) store
      ((state.add extra node pick).root ref) =
      buildNode store (state.raw.decode valid store) (node i) := by
  simp only [Bundle.add, chosen]
  exact state.raw.decode_extend_new valid extra node store i

/-- The raw source partition contains only numeric indices. -/
inductive Class (r u : Nat) where
  | plain
  | read (reader : Fin r)
  | move (mover : Fin u)

/-- Computational data only. Source refinement and partition proofs are separate arguments.
The supplied functions are raw finite primitive fields, not semantic-operation oracles. -/
structure Data (Γ σ : Type) (n w m k r u width : Nat) where
  rows : Fin n → TM1.Stmt Γ (Fin n) σ
  encode : Γ → List.Vector Bool width
  decode : List.Vector Bool width → Γ
  siteFor : Fin n → Option (Fin w)
  next : Fin w → Γ → σ → Fin n
  alphabet : Fin m ≃ Γ
  stores : Fin k ≃ σ
  readPC : Fin r → Fin n
  movePC : Fin u → Fin n
  classify : Fin n → Class r u

/-- Select the exact head-free continuation used by BinaryTemplates.normalRow. -/
def jump {Γ σ : Type} {n : Nat} (row : TM1.Stmt Γ (Fin n) σ)
    (right : Bool) : Option (Γ → σ → Fin n) :=
  match row with
  | .move _ (.goto next) | .load _ (.goto next) => some next
  | .branch _ (.goto left) (.goto next) => some (if right then next else left)
  | .goto next => some next
  | _ => none

/-- A tail is always a childless goto or halt node. -/
def tailNode {Γ σ : Type} [Inhabited Γ] {n w m k r u width count : Nat}
    (data : Data Γ σ n w m k r u width) (pc : Fin n) (right : Bool) :
    Node count k (n + w * m) :=
  match jump (data.rows pc) right with
  | none => .halt
  | some next => .goto (tableOf fun _ value ↦
      BinaryTemplates.normal w m (next default (data.stores value)))

@[simp] theorem tailNode_children {Γ σ : Type} [Inhabited Γ]
    {n w m k r u width count : Nat} (data : Data Γ σ n w m k r u width)
    (pc : Fin n) (right : Bool) : (tailNode (count := count) data pc right).children = [] := by
  unfold tailNode
  split <;> rfl

/-- Childless normal continuations and writer continuations occupy the first range. -/
def base {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) : Bundle n w r u m k where
  raw := ⟨n * 2 + w, Fin.addCases
    (fun p ↦ let pair : Fin n × Fin 2 := finProdFinEquiv.symm p
      tailNode data pair.1 (pair.2 == 1))
    (fun site ↦ .goto (tableOf fun _ value ↦
      BinaryTemplates.normal w m (data.next site default (data.stores value))))⟩
  root ref := match ref with
    | .tail pc right => (finProdFinEquiv (pc, (if right then 1 else 0 : Fin 2))).castAdd w
    | .writerTail site => Fin.natAdd (n * 2) site
    | _ => (finProdFinEquiv (0, (0 : Fin 2))).castAdd w

/-- The base range is acyclic independently of every source-semantic certificate. -/
theorem base_valid {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) : (base data).raw.Valid := by
  intro i child member
  induction i using Fin.addCases with
  | left i =>
    simp only [base, Fin.addCases_left] at member
    change child ∈ (tailNode data (finProdFinEquiv.symm i).1
      ((finProdFinEquiv.symm i : Fin n × Fin 2).2 == 1)).children at member
    simp only [tailNode_children, List.not_mem_nil] at member
  | right i => simp [base, Node.children] at member

/-- The exact normal continuation after the head-independent jump specialization. -/
def tailStmt {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat}
    (data : Data Γ σ n w m k r u width) (pc : Fin n) (right : Bool) :
    TM1.Stmt Bool (Fin (n + w * m)) σ :=
  match jump (data.rows pc) right with
  | none => .halt
  | some next => .goto fun _ value ↦ BinaryTemplates.normal w m (next default value)

@[simp] theorem build_tailNode {Γ σ : Type} [Inhabited Γ]
    {n w m k r u width count : Nat} (data : Data Γ σ n w m k r u width)
    (child : Fin count → TM1.Stmt Bool (Fin (n + w * m)) σ) (pc : Fin n) (right : Bool) :
    buildNode data.stores child (tailNode data pc right) = tailStmt data pc right := by
  unfold tailNode tailStmt
  split <;> simp [buildNode, tableOf_read]

theorem base_tail {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) (pc : Fin n) (right : Bool) :
    (base data).raw.decode (base_valid data) data.stores ((base data).root (.tail pc right)) =
      tailStmt data pc right := by
  rw [Raw.decode_eq]
  simp only [base, Fin.addCases_left, Equiv.symm_apply_apply]
  cases right <;> exact build_tailNode data _ pc _

theorem base_writerTail {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) (site : Fin w) :
    (base data).raw.decode (base_valid data) data.stores ((base data).root (.writerTail site)) =
      .goto (fun _ value ↦ BinaryTemplates.normal w m (data.next site default value)) := by
  rw [Raw.decode_eq]
  simp [base, buildNode]

/-- Exact read-leaf payload, before the reader's restoring left moves. -/
def payloadStmt {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat}
    (data : Data Γ σ n w m k r u width) (pc : Fin n) (glyph : Γ) :
    TM1.Stmt Bool (Fin (n + w * m)) σ :=
  match data.rows pc with
  | .write f _ => match data.siteFor pc with
    | none => .halt
    | some site => .goto fun _ value ↦
        BinaryTemplates.writer n site (data.alphabet.symm (f glyph value))
  | .load f (.goto _) =>
      .load (fun _ value ↦ f glyph value) (tailStmt data pc false)
  | .branch p (.goto _) (.goto _) =>
      .branch (fun _ value ↦ p glyph value) (tailStmt data pc false) (tailStmt data pc true)
  | _ => .halt

/-- A read payload observes one decoded glyph and all finite stores. -/
def payloadNode {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat}
    (data : Data Γ σ n w m k r u width) (state : Bundle n w r u m k)
    (i : Fin (r * m)) : Node state.raw.count k (n + w * m) :=
  let pair : Fin r × Fin m := finProdFinEquiv.symm i
  let pc := data.readPC pair.1
  let glyph := data.alphabet pair.2
  match data.rows pc with
  | .write f _ => match data.siteFor pc with
    | none => .halt
    | some site => .goto (tableOf fun _ value ↦
        BinaryTemplates.writer n site (data.alphabet.symm (f glyph (data.stores value))))
  | .load f (.goto _) =>
      .load (tableOf fun _ value ↦ data.stores.symm (f glyph (data.stores value)))
        (state.root (.tail pc false))
  | .branch p (.goto _) (.goto _) =>
      .branch (tableOf fun _ value ↦ p glyph (data.stores value))
        (state.root (.tail pc false)) (state.root (.tail pc true))
  | _ => .halt

def payloadPick {n w r u m : Nat} : Ref n w r u m → Option (Fin (r * m))
  | .readLeaf reader glyph => some (finProdFinEquiv (reader, glyph))
  | _ => none

/-- Allocate one payload per read row and actual glyph, shared by every invalid bit code
that the real decoder maps to that glyph. -/
def payloads {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat}
    (data : Data Γ σ n w m k r u width) (state : Bundle n w r u m k) : Bundle n w r u m k :=
  state.add (r * m) (payloadNode data state) payloadPick

theorem payloads_valid {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat}
    (data : Data Γ σ n w m k r u width) (state : Bundle n w r u m k)
    (valid : state.raw.Valid) : (payloads data state).raw.Valid :=
  state.raw.extend_valid valid _ _

/-- A whole parallel movement layer uses previous roots as its children. -/
def moveStep {n w r u m k : Nat} (extra : Nat) (refOf : Fin extra → Ref n w r u m)
    (pick : Ref n w r u m → Option (Fin extra)) (dir : Fin extra → Dir)
    (state : Bundle n w r u m k) : Bundle n w r u m k :=
  state.add extra (fun i ↦ .move (dir i) (state.root (refOf i))) pick

/-- Repeated movement layers allocate one node per selected family member and step. -/
def moveLayers {n w r u m k : Nat} (extra : Nat) (refOf : Fin extra → Ref n w r u m)
    (pick : Ref n w r u m → Option (Fin extra)) (dir : Fin extra → Dir) :
    Nat → Bundle n w r u m k → Bundle n w r u m k
  | 0, state => state
  | steps + 1, state => moveStep extra refOf pick dir
      (moveLayers extra refOf pick dir steps state)

theorem moveLayers_valid {n w r u m k : Nat} (extra : Nat)
    (refOf : Fin extra → Ref n w r u m) (pick : Ref n w r u m → Option (Fin extra))
    (dir : Fin extra → Dir) (steps : Nat) (state : Bundle n w r u m k)
    (valid : state.raw.Valid) : (moveLayers extra refOf pick dir steps state).raw.Valid := by
  induction steps with
  | zero => exact valid
  | succ steps ih => exact Raw.extend_valid _ ih _ _

theorem moveLayers_count {n w r u m k : Nat} (extra : Nat)
    (refOf : Fin extra → Ref n w r u m) (pick : Ref n w r u m → Option (Fin extra))
    (dir : Fin extra → Dir) (steps : Nat) (state : Bundle n w r u m k) :
    (moveLayers extra refOf pick dir steps state).raw.count = state.raw.count + steps * extra := by
  induction steps with
  | zero => simp [moveLayers]
  | succ steps ih => simpa [moveLayers, moveStep, Bundle.add, Raw.extend, Nat.succ_mul,
      Nat.add_assoc] using congrArg (fun x ↦ x + extra) ih

theorem moveLayers_at {n w r u m k : Nat} {σ : Type} (extra : Nat)
    (refOf : Fin extra → Ref n w r u m) (pick : Ref n w r u m → Option (Fin extra))
    (dir : Fin extra → Dir) (steps : Nat) (state : Bundle n w r u m k)
    (valid : state.raw.Valid) (store : Fin k ≃ σ) (i : Fin extra)
    (chosen : pick (refOf i) = some i) :
    (moveLayers extra refOf pick dir steps state).raw.decode
      (moveLayers_valid extra refOf pick dir steps state valid) store
      ((moveLayers extra refOf pick dir steps state).root (refOf i)) =
      BinaryTemplates.move steps (dir i) (state.raw.decode valid store (state.root (refOf i))) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    simp only [moveLayers, moveStep]
    rw [Bundle.decode_add_new _ (moveLayers_valid extra refOf pick dir steps state valid)
      _ _ _ _ _ i chosen]
    simp only [buildNode]
    rw [ih]
    simp [BinaryTemplates.move, Function.iterate_succ_apply']

theorem moveLayers_keep {n w r u m k : Nat} {σ : Type} (extra : Nat)
    (refOf : Fin extra → Ref n w r u m) (pick : Ref n w r u m → Option (Fin extra))
    (dir : Fin extra → Dir) (steps : Nat) (state : Bundle n w r u m k)
    (valid : state.raw.Valid) (store : Fin k ≃ σ) (ref : Ref n w r u m)
    (keep : pick ref = none) :
    (moveLayers extra refOf pick dir steps state).raw.decode
      (moveLayers_valid extra refOf pick dir steps state valid) store
      ((moveLayers extra refOf pick dir steps state).root ref) =
      state.raw.decode valid store (state.root ref) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    simp only [moveLayers, moveStep]
    rw [Bundle.decode_add_old _ (moveLayers_valid extra refOf pick dir steps state valid)
      _ _ _ _ _ keep]
    exact ih

/-- Constructive Boolean-vector indexing, using only finite arithmetic in the getters. -/
def bitsEquiv (width : Nat) : List.Vector Bool width ≃ Fin (2 ^ width) :=
  (Equiv.vectorEquivFin Bool width).trans
    ((Equiv.piCongrRight (fun _ ↦ finTwoEquiv.symm)).trans finFunctionFinEquiv)

def familyEquiv (owners width : Nat) :
    (Fin owners × List.Vector Bool width) ≃ Fin (owners * 2 ^ width) :=
  (Equiv.prodCongr (Equiv.refl _) (bitsEquiv width)).trans finProdFinEquiv

/-- Intermediate read/write layers retain a finite root getter for their current frontier. -/
structure Frontier (n w r u m k owners width : Nat) where
  state : Bundle n w r u m k
  root : Fin owners → List.Vector Bool width → Fin state.raw.count

def writerMoveNode {n w r u m k d : Nat} (prev : Frontier n w r u m k w d)
    (i : Fin (w * 2 ^ (d + 1))) : Node prev.state.raw.count k (n + w * m) :=
  let pair := (familyEquiv w (d + 1)).symm i
  .move .right (prev.root pair.1 pair.2.tail)

abbrev writerMoves {n w r u m k d : Nat} (prev : Frontier n w r u m k w d) :
    Bundle n w r u m k :=
  prev.state.add (w * 2 ^ (d + 1)) (writerMoveNode prev) (fun _ ↦ none)

def writerWriteNode {n w r u m k d : Nat} (prev : Frontier n w r u m k w d)
    (i : Fin (w * 2 ^ (d + 1))) : Node (writerMoves prev).raw.count k (n + w * m) :=
  let pair := (familyEquiv w (d + 1)).symm i
  .write (tableOf fun _ _ ↦ pair.2.head) (Fin.natAdd prev.state.raw.count i)

/-- Share every shorter writer suffix once per site. A new width adds two nodes for
all bit vectors at that width, independently of how many glyphs encode to them. -/
abbrev writerStep {n w r u m k d : Nat} (prev : Frontier n w r u m k w d) :
    Frontier n w r u m k w (d + 1) where
  state := (writerMoves prev).add (w * 2 ^ (d + 1)) (writerWriteNode prev) (fun _ ↦ none)
  root site bits := Fin.natAdd (writerMoves prev).raw.count ((familyEquiv w (d + 1)) (site, bits))

theorem writerStep_valid {n w r u m k d : Nat} (prev : Frontier n w r u m k w d)
    (valid : prev.state.raw.Valid) : (writerStep prev).state.raw.Valid :=
  Raw.extend_valid _ (Raw.extend_valid _ valid _ _) _ _

theorem writerStep_keep {n w r u m k d : Nat} {σ : Type}
    (prev : Frontier n w r u m k w d) (valid : prev.state.raw.Valid) (store : Fin k ≃ σ)
    (ref : Ref n w r u m) :
    (writerStep prev).state.raw.decode (writerStep_valid prev valid) store
      ((writerStep prev).state.root ref) =
      prev.state.raw.decode valid store (prev.state.root ref) := by
  exact (Bundle.decode_add_old (writerMoves prev) (Raw.extend_valid _ valid _ _) _
    (writerWriteNode prev) (fun _ ↦ none) store ref rfl).trans
      (Bundle.decode_add_old prev.state valid _ (writerMoveNode prev) (fun _ ↦ none) store ref rfl)

theorem writerStep_root {n w r u m k d : Nat} {σ : Type}
    (prev : Frontier n w r u m k w d) (valid : prev.state.raw.Valid) (store : Fin k ≃ σ)
    (site : Fin w) (bits : List.Vector Bool (d + 1)) :
    (writerStep prev).state.raw.decode (writerStep_valid prev valid) store
      ((writerStep prev).root site bits) =
      .write (fun _ _ ↦ bits.head)
        (.move .right (prev.state.raw.decode valid store (prev.root site bits.tail))) := by
  change ((writerMoves prev).raw.extend _ _).decode
    (Raw.extend_valid _ (Raw.extend_valid _ valid _ _) _ _) store
    (Fin.natAdd (writerMoves prev).raw.count ((familyEquiv w (d + 1)) (site, bits))) = _
  rw [Raw.decode_extend_new _ (Raw.extend_valid _ valid _ _) _ _ store
    ((familyEquiv w (d + 1)) (site, bits))]
  simp only [writerWriteNode, Equiv.symm_apply_apply, buildNode, tableOf_read]
  congr 1
  rw [Raw.decode_extend_new _ valid _ _ store ((familyEquiv w (d + 1)) (site, bits))]
  simp [writerMoveNode, buildNode]

/-- All suffix levels are getter layers; construction visits only `width` levels. -/
def writers {n w r u m k : Nat} : (width : Nat) → Bundle n w r u m k →
    Frontier n w r u m k w width
  | 0, state => ⟨state, fun site _ ↦ state.root (.writerTail site)⟩
  | width + 1, state => writerStep (writers width state)

theorem writers_valid {n w r u m k : Nat} (width : Nat) (state : Bundle n w r u m k)
    (valid : state.raw.Valid) : (writers width state).state.raw.Valid := by
  induction width with
  | zero => exact valid
  | succ width ih => exact writerStep_valid _ ih

theorem writers_keep {n w r u m k : Nat} {σ : Type} (width : Nat)
    (state : Bundle n w r u m k) (valid : state.raw.Valid) (store : Fin k ≃ σ)
    (ref : Ref n w r u m) :
    (writers width state).state.raw.decode (writers_valid width state valid) store
      ((writers width state).state.root ref) = state.raw.decode valid store (state.root ref) := by
  induction width with
  | zero => rfl
  | succ width ih => exact (writerStep_keep _ (writers_valid width state valid) store ref).trans ih

theorem writers_root {n w r u m k : Nat} {σ : Type} (width : Nat)
    (state : Bundle n w r u m k) (valid : state.raw.Valid) (store : Fin k ≃ σ)
    (site : Fin w) (bits : List.Vector Bool width) :
    (writers width state).state.raw.decode (writers_valid width state valid) store
      ((writers width state).root site bits) =
      BinaryTemplates.write bits.toList
        (state.raw.decode valid store (state.root (.writerTail site))) := by
  induction width with
  | zero => simp [writers, bits.eq_nil, BinaryTemplates.write]
  | succ width ih =>
    simp only [writers]
    rw [writerStep_root _ (writers_valid width state valid), ih bits.tail]
    rw [← bits.cons_head_tail]
    rfl

/-- Prefix extension uses exactly the order in which the read macro visits tape bits. -/
def concatBits {p : Nat} (pre : List.Vector Bool p) (bit : Bool) : List.Vector Bool (p + 1) :=
  ⟨pre.toList ++ [bit], by simp⟩

def joinBits {p d width : Nat} (pre : List.Vector Bool p) (suffix : List.Vector Bool d)
    (bound : p + d = width) : List.Vector Bool width :=
  ⟨pre.toList ++ suffix.toList, by simpa using bound⟩

theorem joinBits_cons {p d width : Nat} (pre : List.Vector Bool p) (bit : Bool)
    (suffix : List.Vector Bool d) (bound : p + (d + 1) = width) :
    joinBits (concatBits pre bit) suffix (by omega) =
      joinBits pre (bit ::ᵥ suffix) bound := by
  apply Subtype.ext
  simp [joinBits, concatBits, List.append_assoc]

def readerMoveNode {n w r u m k p : Nat} (prev : Frontier n w r u m k r (p + 1))
    (i : Fin ((r * 2 ^ p) * 2)) : Node prev.state.raw.count k (n + w * m) :=
  let pair : Fin (r * 2 ^ p) × Fin 2 := finProdFinEquiv.symm i
  let leaf := (familyEquiv r p).symm pair.1
  .move .right (prev.root leaf.1 (concatBits leaf.2 (pair.2 == 1)))

abbrev readerMoves {n w r u m k p : Nat} (prev : Frontier n w r u m k r (p + 1)) :
    Bundle n w r u m k :=
  prev.state.add ((r * 2 ^ p) * 2) (readerMoveNode prev) (fun _ ↦ none)

def readerBranchNode {n w r u m k p : Nat} (prev : Frontier n w r u m k r (p + 1))
    (i : Fin (r * 2 ^ p)) : Node (readerMoves prev).raw.count k (n + w * m) :=
  .branch (tableOf fun bit _ ↦ bit)
    (Fin.natAdd prev.state.raw.count (finProdFinEquiv (i, (1 : Fin 2))))
    (Fin.natAdd prev.state.raw.count (finProdFinEquiv (i, (0 : Fin 2))))

/-- Add one complete read-tree level. Both Boolean outcomes retain their exact pre. -/
abbrev readerStep {n w r u m k p : Nat} (prev : Frontier n w r u m k r (p + 1)) :
    Frontier n w r u m k r p where
  state := (readerMoves prev).add (r * 2 ^ p) (readerBranchNode prev) (fun _ ↦ none)
  root reader pre := Fin.natAdd (readerMoves prev).raw.count
    ((familyEquiv r p) (reader, pre))

theorem readerStep_valid {n w r u m k p : Nat} (prev : Frontier n w r u m k r (p + 1))
    (valid : prev.state.raw.Valid) : (readerStep prev).state.raw.Valid :=
  Raw.extend_valid _ (Raw.extend_valid _ valid _ _) _ _

theorem readerStep_keep {n w r u m k p : Nat} {σ : Type}
    (prev : Frontier n w r u m k r (p + 1)) (valid : prev.state.raw.Valid) (store : Fin k ≃ σ)
    (ref : Ref n w r u m) :
    (readerStep prev).state.raw.decode (readerStep_valid prev valid) store
      ((readerStep prev).state.root ref) =
      prev.state.raw.decode valid store (prev.state.root ref) := by
  exact (Bundle.decode_add_old (readerMoves prev) (Raw.extend_valid _ valid _ _) _
    (readerBranchNode prev) (fun _ ↦ none) store ref rfl).trans
      (Bundle.decode_add_old prev.state valid _ (readerMoveNode prev) (fun _ ↦ none) store ref rfl)

theorem readerStep_root {n w r u m k p : Nat} {σ : Type}
    (prev : Frontier n w r u m k r (p + 1)) (valid : prev.state.raw.Valid) (store : Fin k ≃ σ)
    (reader : Fin r) (pre : List.Vector Bool p) :
    (readerStep prev).state.raw.decode (readerStep_valid prev valid) store
      ((readerStep prev).root reader pre) =
      .branch (fun bit _ ↦ bit)
        (.move .right (prev.state.raw.decode valid store
          (prev.root reader (concatBits pre true))))
        (.move .right (prev.state.raw.decode valid store
          (prev.root reader (concatBits pre false)))) := by
  change ((readerMoves prev).raw.extend _ _).decode
    (Raw.extend_valid _ (Raw.extend_valid _ valid _ _) _ _) store
    (Fin.natAdd (readerMoves prev).raw.count ((familyEquiv r p) (reader, pre))) = _
  rw [Raw.decode_extend_new _ (Raw.extend_valid _ valid _ _) _ _ store
    ((familyEquiv r p) (reader, pre))]
  simp only [readerBranchNode, buildNode, tableOf_read]
  congr 1 <;> rw [Raw.decode_extend_new _ valid] <;>
    simp [readerMoveNode, buildNode]

/-- Reader construction uses only one getter layer per bit, not a traversal of bit strings. -/
def readers {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat}
    (data : Data Γ σ n w m k r u width) : (remaining pre : Nat) →
    pre + remaining = width → Bundle n w r u m k → Frontier n w r u m k r pre
  | 0, pre, bound, state => ⟨state, fun reader bits ↦
      state.root (.readLeaf reader (data.alphabet.symm (data.decode
        (joinBits bits List.Vector.nil bound))))⟩
  | remaining + 1, pre, bound, state =>
      readerStep (readers data remaining (pre + 1) (by omega) state)

theorem readers_valid {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat}
    (data : Data Γ σ n w m k r u width) (remaining pre : Nat)
    (bound : pre + remaining = width) (state : Bundle n w r u m k)
    (valid : state.raw.Valid) : (readers data remaining pre bound state).state.raw.Valid := by
  induction remaining generalizing pre with
  | zero => exact valid
  | succ remaining ih => exact readerStep_valid _ (ih _ _)

theorem readers_keep {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat}
    (data : Data Γ σ n w m k r u width) (remaining pre : Nat)
    (bound : pre + remaining = width) (state : Bundle n w r u m k)
    (valid : state.raw.Valid) (ref : Ref n w r u m) :
    (readers data remaining pre bound state).state.raw.decode
      (readers_valid data remaining pre bound state valid) data.stores
      ((readers data remaining pre bound state).state.root ref) =
      state.raw.decode valid data.stores (state.root ref) := by
  induction remaining generalizing pre with
  | zero => rfl
  | succ remaining ih =>
    exact (readerStep_keep _ (readers_valid data remaining (pre + 1) _ state valid)
      data.stores ref).trans (ih _ _)

theorem readers_root {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat}
    (data : Data Γ σ n w m k r u width) (remaining pre : Nat)
    (bound : pre + remaining = width) (state : Bundle n w r u m k)
    (valid : state.raw.Valid) (reader : Fin r) (bits : List.Vector Bool pre) :
    (readers data remaining pre bound state).state.raw.decode
      (readers_valid data remaining pre bound state valid) data.stores
      ((readers data remaining pre bound state).root reader bits) =
      BinaryTemplates.readAux remaining (fun suffix ↦ state.raw.decode valid data.stores
        (state.root (.readLeaf reader (data.alphabet.symm (data.decode
          (joinBits bits suffix bound)))))) := by
  induction remaining generalizing pre with
  | zero => simp [readers, BinaryTemplates.readAux]
  | succ remaining ih =>
    simp only [readers]
    rw [readerStep_root _ (readers_valid data remaining (pre + 1) _ state valid)]
    rw [ih _ _ (concatBits bits true), ih _ _ (concatBits bits false)]
    simp only [BinaryTemplates.readAux]
    apply congrArg₂ (TM1.Stmt.branch (fun bit _ ↦ bit))
    all_goals apply congrArg (TM1.Stmt.move .right)
    all_goals apply congrArg (BinaryTemplates.readAux remaining)
    all_goals funext suffix
    · rw [joinBits_cons bits true suffix bound]
    · rw [joinBits_cons bits false suffix bound]

theorem payloads_leaf {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat}
    (data : Data Γ σ n w m k r u width) (state : Bundle n w r u m k)
    (valid : state.raw.Valid)
    (tails : ∀ pc side, state.raw.decode valid data.stores (state.root (.tail pc side)) =
      tailStmt data pc side) (reader : Fin r) (glyph : Fin m) :
    (payloads data state).raw.decode (payloads_valid data state valid) data.stores
      ((payloads data state).root (.readLeaf reader glyph)) =
      payloadStmt data (data.readPC reader) (data.alphabet glyph) := by
  simp only [payloads]
  rw [Bundle.decode_add_new _ valid _ _ _ _ _ (finProdFinEquiv (reader, glyph)) rfl]
  simp only [payloadNode, Equiv.symm_apply_apply]
  cases row : data.rows (data.readPC reader) with
  | move dir tail => simp [payloadStmt, row, buildNode]
  | write f tail =>
    cases site : data.siteFor (data.readPC reader) <;>
      simp [payloadStmt, row, site, buildNode]
  | load f tail => cases tail <;> simp [payloadStmt, row, buildNode, tails]
  | branch p left right =>
    cases left <;> cases right <;> simp [payloadStmt, row, buildNode, tails]
  | goto next => simp [payloadStmt, row, buildNode]
  | halt => simp [payloadStmt, row, buildNode]

/-- Root family for shared restorations and normal movement chains. -/
def chainRef {n w r u m : Nat} (i : Fin (r * m + w + u)) : Ref n w r u m :=
  Fin.addCases (Fin.addCases
    (fun p ↦ let pair : Fin r × Fin m := finProdFinEquiv.symm p
      .readLeaf pair.1 pair.2) Ref.writerTail) Ref.mover i

def chainPick {n w r u m : Nat} : Ref n w r u m → Option (Fin (r * m + w + u))
  | .readLeaf reader glyph => some ((finProdFinEquiv (reader, glyph)).castAdd w |>.castAdd u)
  | .writerTail site => some ((Fin.natAdd (r * m) site).castAdd u)
  | .mover mover => some (Fin.natAdd (r * m + w) mover)
  | _ => none

@[simp] theorem chainPick_ref {n w r u m : Nat} (i : Fin (r * m + w + u)) :
    chainPick (chainRef (n := n) i) = some i := by
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i =>
      simpa only [chainRef, Fin.addCases_left, chainPick] using
        congrArg (fun j : Fin (r * m) ↦ some ((j.castAdd w).castAdd u))
          (finProdFinEquiv.apply_symm_apply i)
    | right i => simp [chainRef, chainPick]
  | right i => simp [chainRef, chainPick]

def chainDir {Γ σ : Type} {n w m k r u width : Nat}
    (data : Data Γ σ n w m k r u width) (i : Fin (r * m + w + u)) : Dir :=
  match chainRef (n := n) i with
  | .mover mover => match data.rows (data.movePC mover) with
    | .move dir _ => dir
    | _ => .left
  | _ => .left

/-- Install normal mover continuations without adding nodes. -/
def initialMoves {Γ σ : Type} {n w m k r u width : Nat}
    (data : Data Γ σ n w m k r u width) (state : Bundle n w r u m k) : Bundle n w r u m k where
  raw := state.raw
  root ref := match ref with
    | .mover i => state.root (.tail (data.movePC i) false)
    | _ => state.root ref

def prepared {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) : Bundle n w r u m k :=
  moveLayers (r * m + w + u) chainRef chainPick (chainDir data) width
    (initialMoves data (payloads data (base data)))

theorem prepared_valid {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) : (prepared data).raw.Valid :=
  moveLayers_valid _ _ _ _ _ _ (payloads_valid data _ (base_valid data))

abbrev readFrontier {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) : Frontier n w r u m k r 0 :=
  readers data width 0 (by omega) (prepared data)

abbrev readState {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) : Bundle n w r u m k :=
  let front := readFrontier data
  ⟨front.state.raw, fun ref ↦ match ref with
    | .reader i => front.root i List.Vector.nil
    | _ => front.state.root ref⟩

theorem readState_valid {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) : (readState data).raw.Valid :=
  readers_valid _ _ _ _ _ (prepared_valid data)

/-- Complete nominal getter bundle. Only O(width) layers are allocated; every final node
is selected by arithmetic descent through these layers. No source certificate is an input. -/
def build {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) : Bundle n w r u m k :=
  let front := writers width (readState data)
  ⟨front.state.raw, fun ref ↦ match ref with
    | .writer site glyph => front.root site (data.encode (data.alphabet glyph))
    | _ => front.state.root ref⟩

theorem build_valid {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) : (build data).raw.Valid :=
  writers_valid _ _ (readState_valid data)

/-- Exact complete read-tree allocation, by remaining bits and already-read bits. -/
def readerCost (readers : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | remaining + 1, pre => readerCost readers remaining (pre + 1) + 3 * (readers * 2 ^ pre)

/-- Exact universal suffix sharing: one move and one write for each nonempty suffix. -/
def writerCost (sites : Nat) : Nat → Nat
  | 0 => 0
  | width + 1 => writerCost sites width + 2 * (sites * 2 ^ (width + 1))

theorem writers_count {n w r u m k : Nat} (width : Nat) (state : Bundle n w r u m k) :
    (writers width state).state.raw.count = state.raw.count + writerCost w width := by
  induction width with
  | zero => rfl
  | succ width ih =>
    simp only [writers, writerStep, writerMoves, Bundle.add, Raw.extend, writerCost]
    rw [ih]
    omega

theorem readers_count {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat}
    (data : Data Γ σ n w m k r u width) (remaining pre : Nat)
    (bound : pre + remaining = width) (state : Bundle n w r u m k) :
    (readers data remaining pre bound state).state.raw.count =
      state.raw.count + readerCost r remaining pre := by
  induction remaining generalizing pre with
  | zero => rfl
  | succ remaining ih =>
    simp only [readers, readerStep, readerMoves, Bundle.add, Raw.extend, readerCost]
    rw [ih]
    omega

/-- Every allocated node is paid, including unused normal continuation slots. -/
def nodeCount (n w m readers movers width : Nat) : Nat :=
  n * 2 + w + readers * m + width * (readers * m + w + movers) +
    readerCost readers width 0 + writerCost w width

theorem build_count {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) :
    (build data).raw.count = nodeCount n w m r u width := by
  simp only [build, writers_count, readState, readFrontier, readers_count, prepared,
    moveLayers_count, initialMoves, payloads, Bundle.add, Raw.extend, base, nodeCount]

/-- The unpadded actual family inventory's exact generic allocation. -/
theorem chess_inventory_count : nodeCount 4042 270 1250 1734 1188 11 = 38893646 := by decide

theorem payloads_tail {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) (pc : Fin n) (side : Bool) :
    (payloads data (base data)).raw.decode (payloads_valid data _ (base_valid data)) data.stores
      ((payloads data (base data)).root (.tail pc side)) = tailStmt data pc side := by
  exact (Bundle.decode_add_old _ (base_valid data) _ _ _ data.stores (.tail pc side) rfl).trans
    (base_tail data pc side)

theorem prepared_leaf {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) (reader : Fin r) (glyph : Fin m) :
    (prepared data).raw.decode (prepared_valid data) data.stores
      ((prepared data).root (.readLeaf reader glyph)) =
      BinaryTemplates.move width .left
        (payloadStmt data (data.readPC reader) (data.alphabet glyph)) := by
  let i : Fin (r * m + w + u) := ((finProdFinEquiv (reader, glyph)).castAdd w).castAdd u
  have ref : chainRef (n := n) i = .readLeaf reader glyph := by
    simpa only [i, chainRef, Fin.addCases_left] using
      congrArg (fun pair : Fin r × Fin m ↦ Ref.readLeaf (n := n) (w := w) (u := u)
        pair.1 pair.2) (finProdFinEquiv.symm_apply_apply (reader, glyph))
  have direction : chainDir data i = .left := by simp [chainDir, ref]
  have equal := moveLayers_at _ chainRef chainPick (chainDir data) width
    (initialMoves data (payloads data (base data)))
    (payloads_valid data _ (base_valid data)) data.stores i (chainPick_ref i)
  rw [ref, direction] at equal
  exact equal.trans (congrArg (BinaryTemplates.move width .left)
    (payloads_leaf data (base data) (base_valid data) (base_tail data) reader glyph))

theorem prepared_writerTail {Γ σ : Type} [Inhabited Γ]
    {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) (site : Fin w) :
    (prepared data).raw.decode (prepared_valid data) data.stores
      ((prepared data).root (.writerTail site)) =
      BinaryTemplates.move width .left
        (.goto fun _ value ↦ BinaryTemplates.normal w m (data.next site default value)) := by
  let i : Fin (r * m + w + u) := (Fin.natAdd (r * m) site).castAdd u
  have ref : chainRef (n := n) i = .writerTail site := by simp [i, chainRef]
  have direction : chainDir data i = .left := by simp [chainDir, ref]
  have equal := moveLayers_at _ chainRef chainPick (chainDir data) width
    (initialMoves data (payloads data (base data)))
    (payloads_valid data _ (base_valid data)) data.stores i (chainPick_ref i)
  rw [ref, direction] at equal
  apply equal.trans
  apply congrArg (BinaryTemplates.move width .left)
  exact (Bundle.decode_add_old (base data) (base_valid data) (r * m)
    (payloadNode data (base data)) payloadPick data.stores (.writerTail site) rfl).trans
    (base_writerTail data site)

def moverDir {Γ σ : Type} {n w m k r u width : Nat}
    (data : Data Γ σ n w m k r u width) (mover : Fin u) : Dir :=
  match data.rows (data.movePC mover) with
  | .move dir _ => dir
  | _ => .left

theorem prepared_mover {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) (mover : Fin u) :
    (prepared data).raw.decode (prepared_valid data) data.stores
      ((prepared data).root (.mover mover)) =
      BinaryTemplates.move width (moverDir data mover)
        (tailStmt data (data.movePC mover) false) := by
  let i : Fin (r * m + w + u) := Fin.natAdd (r * m + w) mover
  have ref : chainRef (n := n) i = .mover mover := by simp [i, chainRef]
  have direction : chainDir data i = moverDir data mover := by simp [chainDir, ref, moverDir]
  have equal := moveLayers_at _ chainRef chainPick (chainDir data) width
    (initialMoves data (payloads data (base data)))
    (payloads_valid data _ (base_valid data)) data.stores i (chainPick_ref i)
  rw [ref, direction] at equal
  exact equal.trans (congrArg (BinaryTemplates.move width (moverDir data mover))
    (payloads_tail data (data.movePC mover) false))

theorem prepared_tail {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) (pc : Fin n) (side : Bool) :
    (prepared data).raw.decode (prepared_valid data) data.stores
      ((prepared data).root (.tail pc side)) = tailStmt data pc side := by
  exact (moveLayers_keep _ chainRef chainPick (chainDir data) width
    (initialMoves data (payloads data (base data)))
    (payloads_valid data _ (base_valid data)) data.stores (.tail pc side) rfl).trans
      (payloads_tail data pc side)

theorem readState_reader {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) (reader : Fin r) :
    (readState data).raw.decode (readState_valid data) data.stores
      ((readState data).root (.reader reader)) =
      BinaryTemplates.read data.decode (payloadStmt data (data.readPC reader)) := by
  change (readFrontier data).state.raw.decode _ data.stores
    ((readFrontier data).root reader List.Vector.nil) = _
  rw [readers_root data width 0 _ (prepared data) (prepared_valid data)]
  unfold BinaryTemplates.read
  apply congrArg (BinaryTemplates.readAux width)
  funext suffix
  rw [prepared_leaf]
  simp [joinBits]

theorem readState_writerTail {Γ σ : Type} [Inhabited Γ]
    {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) (site : Fin w) :
    (readState data).raw.decode (readState_valid data) data.stores
      ((readState data).root (.writerTail site)) =
      BinaryTemplates.move width .left
        (.goto fun _ value ↦ BinaryTemplates.normal w m (data.next site default value)) :=
  (readers_keep data width 0 _ (prepared data) (prepared_valid data) (.writerTail site)).trans
    (prepared_writerTail data site)

theorem readState_mover {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) (mover : Fin u) :
    (readState data).raw.decode (readState_valid data) data.stores
      ((readState data).root (.mover mover)) =
      BinaryTemplates.move width (moverDir data mover)
        (tailStmt data (data.movePC mover) false) :=
  (readers_keep data width 0 _ (prepared data) (prepared_valid data) (.mover mover)).trans
    (prepared_mover data mover)

theorem readState_tail {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) (pc : Fin n) (side : Bool) :
    (readState data).raw.decode (readState_valid data) data.stores
      ((readState data).root (.tail pc side)) = tailStmt data pc side :=
  (readers_keep data width 0 _ (prepared data) (prepared_valid data) (.tail pc side)).trans
    (prepared_tail data pc side)

theorem build_reader {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) (reader : Fin r) :
    (build data).raw.decode (build_valid data) data.stores ((build data).root (.reader reader)) =
      BinaryTemplates.read data.decode (payloadStmt data (data.readPC reader)) :=
  (writers_keep width (readState data) (readState_valid data) data.stores (.reader reader)).trans
    (readState_reader data reader)

theorem build_mover {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) (mover : Fin u) :
    (build data).raw.decode (build_valid data) data.stores ((build data).root (.mover mover)) =
      BinaryTemplates.move width (moverDir data mover)
        (tailStmt data (data.movePC mover) false) :=
  (writers_keep width (readState data) (readState_valid data) data.stores (.mover mover)).trans
    (readState_mover data mover)

theorem build_tail {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) (pc : Fin n) (side : Bool) :
    (build data).raw.decode (build_valid data) data.stores ((build data).root (.tail pc side)) =
      tailStmt data pc side :=
  (writers_keep width (readState data) (readState_valid data) data.stores (.tail pc side)).trans
    (readState_tail data pc side)

theorem build_writer {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) (site : Fin w) (glyph : Fin m) :
    (build data).raw.decode (build_valid data) data.stores
      ((build data).root (.writer site glyph)) =
      BinaryTemplates.write (data.encode (data.alphabet glyph)).toList
        (BinaryTemplates.move width .left
          (.goto fun _ value ↦ BinaryTemplates.normal w m (data.next site default value))) := by
  change (writers width (readState data)).state.raw.decode _ data.stores
    ((writers width (readState data)).root site (data.encode (data.alphabet glyph))) = _
  rw [writers_root _ _ (readState_valid data), readState_writerTail]

/-- Shape-only classification predicates never compare primitive function fields. -/
def PlainRow {Γ σ : Type} {n : Nat} : TM1.Stmt Γ (Fin n) σ → Prop
  | .goto _ | .halt => True
  | _ => False

def ReadRow {Γ σ : Type} {n : Nat} : TM1.Stmt Γ (Fin n) σ → Prop
  | .write _ _ | .load _ _ | .branch _ _ _ => True
  | _ => False

def MoveRow {Γ σ : Type} {n : Nat} : TM1.Stmt Γ (Fin n) σ → Prop
  | .move _ _ => True
  | _ => False

/-- Source semantic obligations are erased and never supplied to `build` or its getters. -/
structure Valid {Γ σ : Type} [Inhabited Γ] {n w m k r u : Nat} (C : BlockCode Γ)
    (data : Data Γ σ n w m k r u C.width)
    (sites : BinaryTemplates.WriteSites data.rows w) : Prop where
  encode_eq : data.encode = C.encode
  decode_eq : data.decode = C.decode
  siteFor_eq : data.siteFor = sites.siteFor
  next_eq : data.next = sites.next
  primitive : ∀ pc, TM1Normalize.OnePrimitive (data.rows pc)
  classified : ∀ pc, match data.classify pc with
    | .plain => PlainRow (data.rows pc)
    | .read i => data.readPC i = pc ∧ ReadRow (data.rows pc)
    | .move i => data.movePC i = pc ∧ MoveRow (data.rows pc)

/-- One classified read row has exactly the original reader macro, including all invalid codes. -/
theorem normal_read {Γ σ : Type} [Inhabited Γ] {n w m k r u : Nat} (C : BlockCode Γ)
    (data : Data Γ σ n w m k r u C.width) (sites : BinaryTemplates.WriteSites data.rows w)
    (valid : Valid C data sites) (pc : Fin n) (read : ReadRow (data.rows pc)) :
    BinaryTemplates.normalRow C data.rows sites data.alphabet pc =
      BinaryTemplates.read data.decode (payloadStmt data pc) := by
  have primitive := valid.primitive pc
  cases row : data.rows pc with
  | move dir tail => simp [ReadRow, row] at read
  | goto next => simp [ReadRow, row] at read
  | halt => simp [ReadRow, row] at read
  | write f tail =>
    obtain ⟨i, found⟩ := sites.covers pc f tail row
    have found' : data.siteFor pc = some i := by rw [valid.siteFor_eq]; exact found
    simp only [BinaryTemplates.normalRow, row, found, valid.decode_eq]
    apply congrArg (BinaryTemplates.read C.decode)
    funext glyph
    simp [payloadStmt, row, found']
  | load f tail =>
    rw [row] at primitive
    cases tail <;> simp only [TM1Normalize.OnePrimitive] at primitive
    simp only [BinaryTemplates.normalRow, row, valid.decode_eq]
    apply congrArg (BinaryTemplates.read C.decode)
    funext glyph
    simp [payloadStmt, row, tailStmt, jump]
  | branch p left right =>
    rw [row] at primitive
    cases left <;> cases right <;> simp only [TM1Normalize.OnePrimitive] at primitive
    simp only [BinaryTemplates.normalRow, row, valid.decode_eq]
    apply congrArg (BinaryTemplates.read C.decode)
    funext glyph
    simp [payloadStmt, row, tailStmt, jump]

/-- Entry selection on an already constructed nominal bundle never rebuilds its getters. -/
def entryOf {Γ σ : Type} {n w m k r u width : Nat}
    (data : Data Γ σ n w m k r u width) (state : Bundle n w r u m k)
    (label : Fin (n + w * m)) : Fin state.raw.count :=
  match (BinaryTemplates.labelEquiv n w m).symm label with
  | .inl pc => match data.classify pc with
    | .plain => state.root (.tail pc false)
    | .read reader => state.root (.reader reader)
    | .move mover => state.root (.mover mover)
  | .inr (site, glyph) => state.root (.writer site glyph)

/-- Pointwise entry specification. Native export retains the bundle through `lazyGraph`. -/
def entry {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) (label : Fin (n + w * m)) : Fin (build data).raw.count :=
  entryOf data (build data) label

/-- Native export consumes this getter graph directly, without `asGraph`. -/
def lazyGraph {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) :
    LazyGraph.Graph (build data).raw.count k (n + w * m) :=
  let state := build data
  ⟨state.raw.node, entryOf data state, build_valid data⟩

/-- Formal vector interpretation only. Executable row lookup never calls this definition. -/
def graph {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) : BoolGraph.Graph (build data).raw.count k (n + w * m) :=
  LazyGraph.asGraph (lazyGraph data)

/-- Getter decoding equals the mathematical vector graph without evaluating that vector. -/
theorem decode_graph {Γ σ : Type} [Inhabited Γ] {n w m k r u width : Nat} [NeZero n]
    (data : Data Γ σ n w m k r u width) (i : Fin (build data).raw.count) :
    (build data).raw.decode (build_valid data) data.stores i =
      BoolGraph.decode (graph data) data.stores i := by
  rw [Raw.decode, BoolGraph.decode,
    show (graph data).nodes.get i = (build data).raw.node i from LazyGraph.asGraph_node _ i]
  cases row : (build data).raw.node i <;> simp only []
  case move dir child => exact congrArg (TM1.Stmt.move dir) (decode_graph data child)
  case write table child =>
    exact congrArg (TM1.Stmt.write _) (decode_graph data child)
  case load table child => exact congrArg (TM1.Stmt.load _) (decode_graph data child)
  case branch table left right =>
    exact congrArg₂ (TM1.Stmt.branch _) (decode_graph data left) (decode_graph data right)
termination_by i.val
decreasing_by all_goals exact build_valid data i _ (by simp [row, Node.children])

/-- All normal labels and every writer glyph decode to exactly BinaryTemplates.machine. -/
theorem machine_eq {Γ σ : Type} [Inhabited Γ] {n w m k r u : Nat} [NeZero n]
    (C : BlockCode Γ) (data : Data Γ σ n w m k r u C.width)
    (sites : BinaryTemplates.WriteSites data.rows w) (valid : Valid C data sites) :
    BoolGraph.machine (graph data) data.stores =
      BinaryTemplates.machine C data.rows sites data.alphabet := by
  funext label
  unfold BoolGraph.machine
  rw [show (graph data).entries.get label = entry data label from LazyGraph.asGraph_entry _ _]
  rw [← decode_graph]
  obtain ⟨label, rfl⟩ := (BinaryTemplates.labelEquiv n w m).surjective label
  cases label with
  | inl pc =>
    simp only [entry, entryOf, Equiv.symm_apply_apply]
    change _ = BinaryTemplates.machine C data.rows sites data.alphabet
      (BinaryTemplates.normal w m pc)
    rw [BinaryTemplates.machine_normal]
    have classified := valid.classified pc
    cases kind : data.classify pc with
    | plain =>
      simp only [kind] at classified ⊢
      rw [build_tail]
      cases row : data.rows pc <;> simp only [row, PlainRow] at classified
      all_goals simp [tailStmt, jump, row, BinaryTemplates.normalRow]
    | read reader =>
      simp only [kind] at classified ⊢
      rw [build_reader, classified.1]
      exact (normal_read C data sites valid pc classified.2).symm
    | move mover =>
      simp only [kind] at classified ⊢
      have owner := classified.1
      have shape := classified.2
      rw [build_mover, owner]
      have primitive := valid.primitive pc
      cases row : data.rows pc <;> simp only [row, MoveRow] at shape
      case move dir tail =>
        rw [row] at primitive
        cases tail <;> simp only [TM1Normalize.OnePrimitive] at primitive
        simp [moverDir, owner, row, tailStmt, jump, BinaryTemplates.normalRow]
  | inr pair =>
    rcases pair with ⟨site, glyph⟩
    simp only [entry, entryOf, Equiv.symm_apply_apply]
    change _ = BinaryTemplates.machine C data.rows sites data.alphabet
      (BinaryTemplates.writer n site glyph)
    rw [BinaryTemplates.machine_writer]
    rw [build_writer, valid.encode_eq, valid.next_eq]

/-- Exact partial output equality from direct lazy Post lookup, on every input. -/
theorem eval_eq {Γ σ : Type} [Inhabited Γ] [Inhabited σ]
    {n w m k r u : Nat} [NeZero n] [NeZero k]
    (C : BlockCode Γ) (data : Data Γ σ n w m k r u C.width)
    (sites : BinaryTemplates.WriteSites data.rows w) (valid : Valid C data sites)
    (zero : data.stores 0 = default) (input : List Bool) :
    TM0.eval (LazyGraph.machine (lazyGraph data)) input =
      TM1.eval (BinaryTemplates.machine C data.rows sites data.alphabet) input := by
  rw [LazyGraph.eval_eq _ data.stores zero input]
  rw [show BoolGraph.machine (LazyGraph.asGraph (lazyGraph data)) data.stores =
    BinaryTemplates.machine C data.rows sites data.alphabet from machine_eq C data sites valid]

/-- Both termination directions include genuine goto loops and ordinary initial tapes. -/
theorem halts_iff {Γ σ : Type} [Inhabited Γ] [Inhabited σ]
    {n w m k r u : Nat} [NeZero n] [NeZero k]
    (C : BlockCode Γ) (data : Data Γ σ n w m k r u C.width)
    (sites : BinaryTemplates.WriteSites data.rows w) (valid : Valid C data sites)
    (zero : data.stores 0 = default) (input : List Bool) :
    (TM0.eval (LazyGraph.machine (lazyGraph data)) input).Dom ↔
      (TM1.eval (BinaryTemplates.machine C data.rows sites data.alphabet) input).Dom := by
  rw [eval_eq C data sites valid zero input]

/-- Exact paid Post control count for the stated actual family inventory. -/
theorem chess_inventory_post_count :
    GraphPost.stateCount (nodeCount 4042 270 1250 1734 1188 11) 5 = 194468236 := by decide

end ConjectureMachines.Compilation.TemplateGraph
