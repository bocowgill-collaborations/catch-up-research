/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Computability.TuringMachine.Config
public import Std.Data.HashMap.Lemmas

/-!
# Verified bottom-up shared Code tables

The cache hashes only a constructor and its natural-number child IDs. Decoding is proved
structurally exact; sharing does not assume semantic equivalence or hash collision freedom.
-/

@[expose] public section
namespace ConjectureMachines.Compilation.CodeDAG
open Turing.ToPartrec

set_option backward.isDefEq.respectTransparency false

/-- Normalized hash keys, with no recursive Code payload. -/
inductive Node where
  | zero
  | succ
  | tail
  | cons : Nat → Nat → Node
  | comp : Nat → Nat → Node
  | branch : Nat → Nat → Node
  | fix : Nat → Node
  deriving DecidableEq, BEq, Hashable, Repr

deriving instance ReflBEq for Node
deriving instance LawfulBEq for Node

/-- Every referenced row precedes its parent. -/
def Node.Below (node : Node) (bound : Nat) : Prop :=
  match node with
  | .zero | .succ | .tail => True
  | .cons left right | .comp left right | .branch left right => left < bound ∧ right < bound
  | .fix child => child < bound

theorem Node.Below.mono (node : Node) {first second : Nat}
    (below : node.Below first) (bound : first ≤ second) : node.Below second := by
  cases node <;> simp_all [Node.Below] <;> omega

/-- Interpret one row using its already decoded children. -/
def Node.build (node : Node) (lookup : Nat → Code) : Code :=
  match node with
  | .zero => .zero'
  | .succ => .succ
  | .tail => .tail
  | .cons left right => .cons (lookup left) (lookup right)
  | .comp left right => .comp (lookup left) (lookup right)
  | .branch left right => .case (lookup left) (lookup right)
  | .fix child => .fix (lookup child)

theorem Node.build_congr (node : Node) (bound : Nat) (below : node.Below bound)
    (first second : Nat → Code) (equal : ∀ i < bound, first i = second i) :
    node.build first = node.build second := by
  cases node <;> simp_all [Node.Below, Node.build]

/-- Decoder accumulator; the default affects only malformed forward/out-of-range references. -/
def decodeRows (rows : Array Node) : Array Code :=
  rows.foldl (fun decoded node ↦ decoded.push (node.build (fun i ↦ decoded[i]?.getD .zero'))) #[]

def decode (rows : Array Node) (id : Nat) : Code := (decodeRows rows)[id]?.getD .zero'

theorem decodeRows_size (rows : Array Node) : (decodeRows rows).size = rows.size := by
  unfold decodeRows
  exact Array.foldl_induction (fun n (decoded : Array Code) ↦ decoded.size = n) rfl
    (fun _ decoded size ↦ by simp [size])

theorem decodeRows_push (rows : Array Node) (node : Node) :
    decodeRows (rows.push node) =
      (decodeRows rows).push (node.build (decode rows)) := by
  rw [decodeRows, Array.foldl_push]
  rfl

theorem decode_push_old (rows : Array Node) (node : Node) (id : Nat) (old : id < rows.size) :
    decode (rows.push node) id = decode rows id := by
  simp only [decode, decodeRows_push, Array.getElem?_push, decodeRows_size,
    Nat.ne_of_lt old, ↓reduceIte]

theorem decode_push_new (rows : Array Node) (node : Node) :
    decode (rows.push node) rows.size = node.build (decode rows) := by
  simp only [decode, decodeRows_push, Array.getElem?_push, decodeRows_size,
    ↓reduceIte, Option.getD_some]

/-- Every row of an arbitrary topological table satisfies its exact constructor equation. -/
theorem decode_row (rows : Array Node)
    (topology : ∀ (i : Nat) (node : Node), rows[i]? = some node → node.Below i)
    (i : Nat) (node : Node) (row : rows[i]? = some node) :
    decode rows i = node.build (decode rows) := by
  cases rows with
  | mk nodes =>
    induction nodes using List.reverseRecOn generalizing i node with
    | nil => simp at row
    | append_singleton nodes last ih =>
      let previous : Array Node := ⟨nodes⟩
      have push : (⟨nodes ++ [last]⟩ : Array Node) = previous.push last := by
        apply Array.ext'
        simp [previous]
      rw [push] at topology row ⊢
      by_cases final : i = previous.size
      · subst i
        have equal : last = node := by simpa [Array.getElem?_push] using row
        subst node
        rw [decode_push_new]
        exact last.build_congr _ (topology _ _ (by simp)) _ _
          (fun j bound ↦ (decode_push_old previous last j bound).symm)
      · have old : previous[i]? = some node := by
          simpa only [Array.getElem?_push, final, ↓reduceIte] using row
        have bound := (Array.getElem?_eq_some_iff.mp old).1
        have before : ∀ (j : Nat) (key : Node), previous[j]? = some key → key.Below j := by
          intro j key found
          have index := (Array.getElem?_eq_some_iff.mp found).1
          exact topology j key (by simpa only [Array.getElem?_push, Nat.ne_of_lt index,
            ↓reduceIte] using found)
        rw [decode_push_old previous last i bound, ih i node before old]
        exact node.build_congr _ ((before i node old).mono node (Nat.le_of_lt bound))
          _ _ (fun j bound ↦ (decode_push_old previous last j bound).symm)

/-- The executed builder stores only rows and the finite hash cache. -/
structure State where
  rows : Array Node := #[]
  cache : Std.HashMap Node Nat := {}

/-- Erased invariant: topology, bidirectional cache/row correspondence, and exact row meaning. -/
structure Valid (state : State) : Prop where
  below : ∀ (i : Nat) (node : Node), state.rows[i]? = some node → node.Below i
  cache_row : ∀ (node : Node) (i : Nat), state.cache[node]? = some i → state.rows[i]? = some node
  row_cache : ∀ (i : Nat) (node : Node), state.rows[i]? = some node → state.cache[node]? = some i
  meaning : ∀ (i : Nat) (node : Node), state.rows[i]? = some node →
    decode state.rows i = node.build (decode state.rows)

/-- Existing indices and their decoded values are preserved by a builder extension. -/
structure Extends (before after : State) : Prop where
  size : before.rows.size ≤ after.rows.size
  rows : ∀ i < before.rows.size, after.rows[i]? = before.rows[i]?
  decoded : ∀ i < before.rows.size, decode after.rows i = decode before.rows i

theorem Extends.refl (state : State) : Extends state state := ⟨le_rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem Extends.trans {first second third : State}
    (left : Extends first second) (right : Extends second third) : Extends first third := by
  exact ⟨left.size.trans right.size,
    fun i bound ↦ (right.rows i (bound.trans_le left.size)).trans (left.rows i bound),
    fun i bound ↦ (right.decoded i (bound.trans_le left.size)).trans (left.decoded i bound)⟩

theorem valid_empty : Valid ({} : State) := by
  constructor <;> simp

/-- Reuse an equal normalized row or append exactly one new row. -/
def intern (node : Node) (state : State) : Nat × State :=
  match state.cache[node]? with
  | some i => (i, state)
  | none => (state.rows.size,
      { rows := state.rows.push node, cache := state.cache.insert node state.rows.size })

theorem valid_push (node : Node) (state : State) (valid : Valid state)
    (below : node.Below state.rows.size) (fresh : state.cache[node]? = none) :
    Valid { rows := state.rows.push node, cache := state.cache.insert node state.rows.size } := by
  have absent (i : Nat) : state.rows[i]? ≠ some node := by
    intro row
    have cached := valid.row_cache i node row
    rw [fresh] at cached
    contradiction
  constructor
  · intro i key row
    by_cases last : i = state.rows.size
    · subst i
      have equal : node = key := by simpa only [Array.getElem?_push, ↓reduceIte,
        Option.some.injEq] using row
      simpa only [← equal] using below
    · exact valid.below i key (by simpa only [Array.getElem?_push, last, ↓reduceIte] using row)
  · intro key i lookup
    by_cases equal : node = key
    · subst key
      have index : state.rows.size = i := by simpa using lookup
      subst i
      simp
    · have old : state.cache[key]? = some i := by
        simpa only [Std.HashMap.getElem?_insert, beq_iff_eq, equal, ↓reduceIte] using lookup
      have row := valid.cache_row key i old
      have bound := (Array.getElem?_eq_some_iff.mp row).1
      simpa only [Array.getElem?_push, Nat.ne_of_lt bound, ↓reduceIte] using row
  · intro i key row
    by_cases last : i = state.rows.size
    · subst i
      have equal : node = key := by simpa only [Array.getElem?_push, ↓reduceIte,
        Option.some.injEq] using row
      subst key
      simp
    · have old : state.rows[i]? = some key := by
        simpa only [Array.getElem?_push, last, ↓reduceIte] using row
      have different : node ≠ key := by
        intro equal
        exact absent i (equal.symm ▸ old)
      simpa only [Std.HashMap.getElem?_insert, beq_iff_eq, different, ↓reduceIte] using
        valid.row_cache i key old
  · intro i key row
    by_cases last : i = state.rows.size
    · subst i
      have equal : node = key := by simpa only [Array.getElem?_push, ↓reduceIte,
        Option.some.injEq] using row
      subst key
      rw [decode_push_new]
      exact node.build_congr _ below _ _ (fun i bound ↦ (decode_push_old _ _ i bound).symm)
    · have old : state.rows[i]? = some key := by
        simpa only [Array.getElem?_push, last, ↓reduceIte] using row
      have bound := (Array.getElem?_eq_some_iff.mp old).1
      rw [decode_push_old _ _ i bound, valid.meaning i key old]
      exact key.build_congr _ ((valid.below i key old).mono key (Nat.le_of_lt bound))
        _ _ (fun i bound ↦ (decode_push_old _ _ i bound).symm)

theorem extends_push (node : Node) (state : State) :
    Extends state
      { rows := state.rows.push node, cache := state.cache.insert node state.rows.size } := by
  exact ⟨by simp, fun i bound ↦ by simp only [Array.getElem?_push, Nat.ne_of_lt bound,
    ↓reduceIte], fun i bound ↦ decode_push_old _ _ i bound⟩

/-- Full interning invariant, including sharing and preservation of previous references. -/
theorem intern_spec (node : Node) (state : State) (valid : Valid state)
    (below : node.Below state.rows.size) :
    let result := intern node state
    Valid result.2 ∧ Extends state result.2 ∧ result.1 < result.2.rows.size ∧
      result.2.rows[result.1]? = some node ∧
      decode result.2.rows result.1 = node.build (decode state.rows) := by
  cases found : state.cache[node]? with
  | some i =>
    have row := valid.cache_row node i found
    simp only [intern, found]
    exact ⟨valid, .refl state, (Array.getElem?_eq_some_iff.mp row).1, row,
      valid.meaning i node row⟩
  | none =>
    simp only [intern, found]
    exact ⟨valid_push node state valid below found, extends_push node state, by simp,
      by simp, decode_push_new state.rows node⟩

theorem intern_cached (node : Node) (state : State) (id : Nat)
    (cached : state.cache[node]? = some id) : intern node state = (id, state) := by
  simp only [intern, cached]

/-- The number of constructor occurrences in the original expanded syntax tree. -/
def occurrences : Code → Nat
  | .zero' | .succ | .tail => 1
  | .cons first second | .comp first second | .case first second =>
    occurrences first + occurrences second + 1
  | .fix child => occurrences child + 1

/-- Executable bottom-up lowering: recursively intern children, then their normalized parent. -/
def lower : Code → State → Nat × State
  | .zero', state => intern .zero state
  | .succ, state => intern .succ state
  | .tail, state => intern .tail state
  | .cons first second, state =>
    let left := lower first state
    let right := lower second left.2
    intern (.cons left.1 right.1) right.2
  | .comp first second, state =>
    let left := lower first state
    let right := lower second left.2
    intern (.comp left.1 right.1) right.2
  | .case first second, state =>
    let left := lower first state
    let right := lower second left.2
    intern (.branch left.1 right.1) right.2
  | .fix child, state =>
    let result := lower child state
    intern (.fix result.1) result.2

theorem intern_size (node : Node) (state : State) :
    (intern node state).2.rows.size ≤ state.rows.size + 1 := by
  unfold intern
  split <;> simp

/-- Proof-only result predicate; the builder stores no semantic Code copies or proof fields. -/
structure Built (code : Code) (before : State) (result : Nat × State) : Prop where
  valid : Valid result.2
  extension : Extends before result.2
  root_lt : result.1 < result.2.rows.size
  correct : decode result.2.rows result.1 = code
  size : result.2.rows.size ≤ before.rows.size + occurrences code

/-- All constructor cases preserve the cache, topology, references, and exact decoding. -/
theorem lower_spec (code : Code) (state : State) (valid : Valid state) :
    Built code state (lower code state) := by
  induction code generalizing state with
  | zero' =>
    rcases intern_spec .zero state valid trivial with ⟨valid, extension, bound, _, correct⟩
    exact ⟨valid, extension, bound, correct, intern_size _ _⟩
  | succ =>
    rcases intern_spec .succ state valid trivial with ⟨valid, extension, bound, _, correct⟩
    exact ⟨valid, extension, bound, correct, intern_size _ _⟩
  | tail =>
    rcases intern_spec .tail state valid trivial with ⟨valid, extension, bound, _, correct⟩
    exact ⟨valid, extension, bound, correct, intern_size _ _⟩
  | cons first second leftIH rightIH =>
    have left := leftIH state valid
    have right := rightIH (lower first state).2 left.valid
    rcases intern_spec (.cons (lower first state).1 (lower second (lower first state).2).1)
      (lower second (lower first state).2).2 right.valid
      ⟨left.root_lt.trans_le right.extension.size, right.root_lt⟩ with
      ⟨parentValid, extension, bound, _, correct⟩
    refine ⟨parentValid, left.extension.trans (right.extension.trans extension), bound, ?_, ?_⟩
    · simpa only [lower, Node.build, right.extension.decoded _ left.root_lt, left.correct,
        right.correct] using correct
    · have size := intern_size (.cons (lower first state).1
        (lower second (lower first state).2).1) (lower second (lower first state).2).2
      have leftSize := left.size
      have rightSize := right.size
      simp only [lower]
      change _ ≤ state.rows.size + (occurrences first + occurrences second + 1)
      omega
  | comp first second leftIH rightIH =>
    have left := leftIH state valid
    have right := rightIH (lower first state).2 left.valid
    rcases intern_spec (.comp (lower first state).1 (lower second (lower first state).2).1)
      (lower second (lower first state).2).2 right.valid
      ⟨left.root_lt.trans_le right.extension.size, right.root_lt⟩ with
      ⟨parentValid, extension, bound, _, correct⟩
    refine ⟨parentValid, left.extension.trans (right.extension.trans extension), bound, ?_, ?_⟩
    · simpa only [lower, Node.build, right.extension.decoded _ left.root_lt, left.correct,
        right.correct] using correct
    · have size := intern_size (.comp (lower first state).1
        (lower second (lower first state).2).1) (lower second (lower first state).2).2
      have leftSize := left.size
      have rightSize := right.size
      simp only [lower]
      change _ ≤ state.rows.size + (occurrences first + occurrences second + 1)
      omega
  | «case» first second leftIH rightIH =>
    have left := leftIH state valid
    have right := rightIH (lower first state).2 left.valid
    rcases intern_spec (.branch (lower first state).1 (lower second (lower first state).2).1)
      (lower second (lower first state).2).2 right.valid
      ⟨left.root_lt.trans_le right.extension.size, right.root_lt⟩ with
      ⟨parentValid, extension, bound, _, correct⟩
    refine ⟨parentValid, left.extension.trans (right.extension.trans extension), bound, ?_, ?_⟩
    · simpa only [lower, Node.build, right.extension.decoded _ left.root_lt, left.correct,
        right.correct] using correct
    · have size := intern_size (.branch (lower first state).1
        (lower second (lower first state).2).1) (lower second (lower first state).2).2
      have leftSize := left.size
      have rightSize := right.size
      simp only [lower]
      change _ ≤ state.rows.size + (occurrences first + occurrences second + 1)
      omega
  | fix child ih =>
    have childResult := ih state valid
    rcases intern_spec (.fix (lower child state).1) (lower child state).2 childResult.valid
      childResult.root_lt with ⟨parentValid, extension, bound, _, correct⟩
    refine ⟨parentValid, childResult.extension.trans extension, bound, ?_, ?_⟩
    · simpa only [lower, Node.build, childResult.correct] using correct
    · have size := intern_size (.fix (lower child state).1) (lower child state).2
      have childSize := childResult.size
      simp only [lower]
      change _ ≤ state.rows.size + (occurrences child + 1)
      omega

/-- The shared artifact excludes the construction cache. -/
structure DAG where
  rows : Array Node
  root : Nat
  deriving Repr

def DAG.Valid (dag : DAG) : Prop := dag.root < dag.rows.size ∧
  ∀ (i : Nat) (node : Node), dag.rows[i]? = some node → node.Below i

/-- Row semantics for any valid table, including accepted serialized tables. -/
theorem DAG.decode_row (dag : DAG) (valid : dag.Valid) (i : Nat) (node : Node)
    (row : dag.rows[i]? = some node) :
    CodeDAG.decode dag.rows i = node.build (CodeDAG.decode dag.rows) :=
  CodeDAG.decode_row dag.rows valid.2 i node row

/-- Compile arbitrary Code; only normalized small keys are hashed. -/
def compile (code : Code) : DAG :=
  let result := lower code {}
  ⟨result.2.rows, result.1⟩

def DAG.decode (dag : DAG) : Code := CodeDAG.decode dag.rows dag.root

/-- Exact syntax reconstruction, stronger than semantic equivalence. -/
theorem compile_correct (code : Code) : (compile code).decode = code :=
  (lower_spec code {} valid_empty).correct

theorem compile_valid (code : Code) : (compile code).Valid :=
  ⟨(lower_spec code {} valid_empty).root_lt, (lower_spec code {} valid_empty).valid.below⟩

theorem compile_size (code : Code) : (compile code).rows.size ≤ occurrences code := by
  simpa [compile] using (lower_spec code {} valid_empty).size

/-- The decoded DAG has exactly the source partial-function semantics, on every input. -/
theorem compile_eval (code : Code) (input : List Nat) :
    (compile code).decode.eval input = code.eval input := by rw [compile_correct]

/-- A normalized row occurs at most once, so repeated cache hits really share an ID. -/
theorem Valid.unique_row (state : State) (valid : Valid state) (i j : Nat) (node : Node)
    (first : state.rows[i]? = some node) (second : state.rows[j]? = some node) : i = j := by
  exact Option.some.inj ((valid.row_cache i node first).symm.trans (valid.row_cache j node second))

theorem compile_unique_row (code : Code) (i j : Nat) (node : Node)
    (first : (compile code).rows[i]? = some node)
    (second : (compile code).rows[j]? = some node) : i = j :=
  Valid.unique_row (lower code {}).2 (lower_spec code {} valid_empty).valid i j node first second

/-- Canonical triples: zero', successor, tail, cons, composition, case, and fix. -/
def Node.words : Node → List Nat
  | .zero => [0, 0, 0]
  | .succ => [1, 0, 0]
  | .tail => [2, 0, 0]
  | .cons left right => [3, left, right]
  | .comp left right => [4, left, right]
  | .branch left right => [5, left, right]
  | .fix child => [6, child, 0]

/-- Reject unknown tags and noncanonical unused operands. -/
def Node.ofTriple : Nat → Nat → Nat → Option Node
  | 0, 0, 0 => some .zero
  | 1, 0, 0 => some .succ
  | 2, 0, 0 => some .tail
  | 3, left, right => some (.cons left right)
  | 4, left, right => some (.comp left right)
  | 5, left, right => some (.branch left right)
  | 6, child, 0 => some (.fix child)
  | _, _, _ => none

theorem Node.words_length (node : Node) : node.words.length = 3 := by cases node <;> rfl

theorem Node.ofTriple_canonical (tag left right : Nat) (node : Node)
    (parsed : Node.ofTriple tag left right = some node) : node.words = [tag, left, right] := by
  unfold Node.ofTriple at parsed
  split at parsed <;> cases parsed <;> rfl

/-- Parse an exact count of rows, returning the unconsumed suffix. -/
def parseRows : Nat → List Nat → Option (List Node × List Nat)
  | 0, words => some ([], words)
  | count + 1, tag :: left :: right :: rest => do
    let node ← Node.ofTriple tag left right
    let result ← parseRows count rest
    return (node :: result.1, result.2)
  | _ + 1, _ => none

theorem parseRows_words (rows : List Node) (suffix : List Nat) :
    parseRows rows.length (rows.flatMap Node.words ++ suffix) = some (rows, suffix) := by
  induction rows with
  | nil => rfl
  | cons node rows ih => cases node <;> simp [Node.words, parseRows, Node.ofTriple, ih]

theorem parseRows_canonical (count : Nat) (words : List Nat) (rows : List Node)
    (suffix : List Nat) (parsed : parseRows count words = some (rows, suffix)) :
    rows.length = count ∧ words = rows.flatMap Node.words ++ suffix := by
  induction count generalizing words rows with
  | zero =>
    simp only [parseRows, Option.some.injEq, Prod.mk.injEq] at parsed
    rcases parsed with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  | succ count ih =>
    cases words with
    | nil => simp [parseRows] at parsed
    | cons tag words =>
      cases words with
      | nil => simp [parseRows] at parsed
      | cons left words =>
        cases words with
        | nil => simp [parseRows] at parsed
        | cons right rest =>
          simp only [parseRows, Bind.bind, Option.bind_eq_some_iff, Option.pure_def,
            Option.some.injEq, Prod.mk.injEq] at parsed
          rcases parsed with ⟨node, row, ⟨tail, remaining⟩, parsedTail, rfl, rfl⟩
          obtain ⟨length, encoded⟩ := ih rest tail parsedTail
          simp [Node.ofTriple_canonical tag left right node row, length, encoded]

instance (node : Node) (bound : Nat) : Decidable (node.Below bound) := by
  cases node <;> unfold Node.Below <;> infer_instance

/-- Executable linear table validation; all quantified indices have explicit finite bounds. -/
def check (dag : DAG) : Bool := decide
  (dag.root < dag.rows.size ∧ ∀ i : Fin dag.rows.size, dag.rows[i.val].Below i.val)

theorem check_iff (dag : DAG) : check dag = true ↔ dag.Valid := by
  simp only [check, decide_eq_true_eq, DAG.Valid]
  constructor
  · rintro ⟨root, rows⟩
    refine ⟨root, fun i node row ↦ ?_⟩
    obtain ⟨bound, equal⟩ := Array.getElem?_eq_some_iff.mp row
    exact equal ▸ rows ⟨i, bound⟩
  · rintro ⟨root, rows⟩
    exact ⟨root, fun i ↦ rows i.val _ (Array.getElem?_eq_getElem i.isLt)⟩

/-- Canonical wire data: row count, root ID, then exactly one triple per shared row. -/
def serialize (dag : DAG) : List Nat :=
  dag.rows.size :: dag.root :: dag.rows.toList.flatMap Node.words

def deserialize (words : List Nat) : Option DAG := do
  let count :: root :: rest := words | none
  let (rows, suffix) ← parseRows count rest
  if suffix = [] then
    let dag : DAG := ⟨rows.toArray, root⟩
    if check dag then some dag else none
  else none

theorem serialize_length (dag : DAG) : (serialize dag).length = 2 + 3 * dag.rows.size := by
  have length (rows : List Node) : (rows.flatMap Node.words).length = 3 * rows.length := by
    induction rows with
    | nil => rfl
    | cons node rows ih => simp [Node.words_length, ih, Nat.mul_add, Nat.add_comm]
  simp only [serialize, List.length_cons, length, Array.length_toList]
  omega

/-- Every valid table has an exact executable serialization round trip. -/
theorem deserialize_serialize (dag : DAG) (valid : dag.Valid) :
    deserialize (serialize dag) = some dag := by
  have parse := parseRows_words dag.rows.toList []
  simp only [Array.length_toList, List.append_nil] at parse
  have accepted := (check_iff dag).mpr valid
  simp [deserialize, serialize, parse, accepted]

theorem deserialize_valid (words : List Nat) (dag : DAG)
    (parsed : deserialize words = some dag) : dag.Valid := by
  cases words with
  | nil => simp [deserialize] at parsed
  | cons count words =>
    cases words with
    | nil => simp [deserialize] at parsed
    | cons root rest =>
      cases parsedRows : parseRows count rest with
      | none => simp [deserialize, parsedRows] at parsed
      | some pair =>
        rcases pair with ⟨rows, suffix⟩
        simp only [deserialize, parsedRows, Bind.bind, Option.bind_some] at parsed
        split_ifs at parsed with empty checked
        · cases Option.some.inj parsed
          exact (check_iff _).mp checked

/-- Accepted bytes are already canonical, including row count, padding, and final boundary. -/
theorem serialize_deserialize (words : List Nat) (dag : DAG)
    (parsed : deserialize words = some dag) : serialize dag = words := by
  cases words with
  | nil => simp [deserialize] at parsed
  | cons count words =>
    cases words with
    | nil => simp [deserialize] at parsed
    | cons root rest =>
      cases parsedRows : parseRows count rest with
      | none => simp [deserialize, parsedRows] at parsed
      | some pair =>
        rcases pair with ⟨rows, suffix⟩
        simp only [deserialize, parsedRows, Bind.bind, Option.bind_some] at parsed
        split_ifs at parsed with empty checked
        cases Option.some.inj parsed
        obtain ⟨length, encoded⟩ := parseRows_canonical count rest rows suffix parsedRows
        simpa [serialize, length, empty] using
          congrArg (fun payload ↦ count :: root :: payload) encoded.symm

theorem serialize_injective {first second : DAG} (firstValid : first.Valid)
    (secondValid : second.Valid) (equal : serialize first = serialize second) : first = second := by
  exact Option.some.inj ((deserialize_serialize first firstValid).symm.trans
    ((congrArg deserialize equal).trans (deserialize_serialize second secondValid)))

/-- Serialized compiled artifacts reconstruct the same exact source program. -/
theorem deserialize_compile (code : Code) :
    deserialize (serialize (compile code)) = some (compile code) :=
  deserialize_serialize (compile code) (compile_valid code)

theorem serialize_compile_length_le (code : Code) :
    (serialize (compile code)).length ≤ 2 + 3 * occurrences code := by
  rw [serialize_length]
  have bound := compile_size code
  omega

end ConjectureMachines.Compilation.CodeDAG
