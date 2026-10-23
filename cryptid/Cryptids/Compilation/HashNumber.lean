/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.Finite
public import Std.Data.HashMap.Lemmas

/-! Hash numbering of supported TM0 machines, with nominal packing for compiled caching. -/
@[expose] public section

namespace ConjectureMachines.Compilation
open Turing

section Index
variable {Λ : Type*} [Inhabited Λ] [DecidableEq Λ] [Hashable Λ]

/-- A linear traversal pairs each source state with its literal finite position. -/
def hashNumberEntries (labels : List Λ) : List (Λ × Fin (labels.length + 1)) :=
  (default :: labels).mapFinIdx fun i q h ↦ (q, ⟨i, h⟩)

/-- Later duplicate entries may replace earlier entries; the initial state is forced to zero. -/
def hashNumberIndex (labels : List Λ) : Std.HashMap Λ (Fin (labels.length + 1)) :=
  (Std.HashMap.ofList (hashNumberEntries labels)).insert default 0

/-- Logical hash lookup; use `hashNumberPack` to retain the computed index in compiled code. -/
def hashNumberLabel (labels : List Λ) : Λ → Fin (labels.length + 1) :=
  let index := hashNumberIndex labels
  fun q ↦ (index[q]?).getD 0

omit [DecidableEq Λ] [Hashable Λ] in
theorem hashNumberEntries_sound (labels : List Λ) {e : Λ × Fin (labels.length + 1)}
    (he : e ∈ hashNumberEntries labels) : unnumberLabel labels e.2 = e.1 := by
  obtain ⟨i, hi, h⟩ := List.mem_mapFinIdx.mp he
  cases h
  rfl

omit [DecidableEq Λ] [Hashable Λ] in
theorem hashNumberEntries_cover (labels : List Λ) {q : Λ} (hq : q ∈ default :: labels) :
    q ∈ (hashNumberEntries labels).map Prod.fst := by
  obtain ⟨i, hi, h⟩ := List.mem_iff_getElem.mp hq
  exact List.mem_map.mpr ⟨((default :: labels)[i], ⟨i, hi⟩),
    List.mem_mapFinIdx.mpr ⟨i, hi, rfl⟩, h⟩

omit [Inhabited Λ] in
private theorem insertMany_decode {β : Type*} (decode : β → Λ)
    (entries : List (Λ × β)) (index : Std.HashMap Λ β)
    (valid : ∀ e ∈ entries, decode e.2 = e.1)
    (initial : ∀ q i, index[q]? = some i → decode i = q) :
    ∀ q i, (index.insertMany entries)[q]? = some i → decode i = q := by
  induction entries generalizing index with
  | nil => simpa using initial
  | cons e entries IH =>
    rw [Std.HashMap.insertMany_cons]
    refine IH _ (fun e he ↦ valid e (List.mem_cons_of_mem _ he)) ?_
    intro q i h
    by_cases he : e.1 = q
    · have hv : e.2 = i := by simpa [Std.HashMap.getElem?_insert, he] using h
      exact (congrArg decode hv.symm).trans ((valid e (List.mem_cons_self)).trans he)
    · exact initial q i (by simpa [Std.HashMap.getElem?_insert, he] using h)

theorem hashNumberIndex_sound (labels : List Λ) {q : Λ} {i : Fin (labels.length + 1)}
    (hi : (hashNumberIndex labels)[q]? = some i) : unnumberLabel labels i = q := by
  have base : ∀ q i, (Std.HashMap.ofList (hashNumberEntries labels))[q]? = some i →
      unnumberLabel labels i = q := by
    rw [Std.HashMap.ofList_eq_insertMany_empty]
    exact insertMany_decode _ _ _ (fun e he ↦ hashNumberEntries_sound labels he)
      (by intro q i h; simp at h)
  by_cases hq : default = q
  · have hi0 : 0 = i := by simpa [hashNumberIndex, Std.HashMap.getElem?_insert, hq] using hi
    rw [← hi0]
    exact hq
  · exact base q i (by simpa [hashNumberIndex, Std.HashMap.getElem?_insert, hq] using hi)

theorem hashNumberIndex_cover (labels : List Λ) {q : Λ} (hq : q ∈ default :: labels) :
    ∃ i, (hashNumberIndex labels)[q]? = some i := by
  have hm : q ∈ hashNumberIndex labels := by
    apply Std.HashMap.mem_insert.mpr
    right
    exact Std.HashMap.mem_ofList.mpr (by simpa using hashNumberEntries_cover labels hq)
  exact Option.isSome_iff_exists.mp (Std.HashMap.isSome_getElem?_iff_mem.mpr hm)

theorem unnumber_hashNumber (labels : List Λ) {q : Λ} (hq : q ∈ default :: labels) :
    unnumberLabel labels (hashNumberLabel labels q) = q := by
  obtain ⟨i, hi⟩ := hashNumberIndex_cover labels hq
  simpa only [hashNumberLabel, hi, Option.getD_some] using hashNumberIndex_sound labels hi

theorem hashNumberLabel_default (labels : List Λ) : hashNumberLabel labels default = 0 := by
  simp [hashNumberLabel, hashNumberIndex]
end Index

section Decode
variable {Λ : Type*} [Inhabited Λ]

/-- Logical array decoding with exactly the original list decoder's values. -/
def hashUnnumberLabel (labels : List Λ) : Fin (labels.length + 1) → Λ :=
  let table := (default :: labels).toArray
  fun q ↦ table[q.val]'(by simpa only [table, List.size_toArray, List.length_cons] using q.isLt)

theorem hashUnnumberLabel_eq (labels : List Λ) :
    hashUnnumberLabel labels = unnumberLabel labels := by
  funext q
  simp [hashUnnumberLabel, unnumberLabel, List.get_eq_getElem]
end Decode

section Machine
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ] [Hashable Λ]

/-- Logical finite TM0 renumbering with forward hash lookup and inverse array lookup. -/
def hashNumberMachine (M : TM0.Machine Γ Λ) (labels : List Λ) :
    TM0.Machine Γ (Fin (labels.length + 1)) :=
  let forward := hashNumberLabel labels
  let backward := hashUnnumberLabel labels
  M.map ⟨id, rfl⟩ ⟨id, rfl⟩ forward backward

/-- Hash numbering preserves both halting directions whenever the list covers a support. -/
theorem hashNumberMachine_dom (M : TM0.Machine Γ Λ) (labels : List Λ)
    (S : Set Λ) (ss : TM0.Supports M S) (cover : ∀ q ∈ S, q ∈ default :: labels)
    (input : List Γ) :
    (TM0.eval (hashNumberMachine M labels) input).Dom ↔ (TM0.eval M input).Dom := by
  let g : PointedMap Λ (Fin (labels.length + 1)) :=
    ⟨hashNumberLabel labels, hashNumberLabel_default labels⟩
  have h := TM0.Machine.map_respects M ⟨id, rfl⟩ ⟨id, rfl⟩ g
    (hashUnnumberLabel labels) ss (fun _ ↦ rfl) (by
      intro q hq
      rw [hashUnnumberLabel_eq]
      exact unnumber_hashNumber labels (cover q hq))
  apply StateTransition.tr_eval_dom h
  refine ⟨ss.1, ?_⟩
  simpa using TM0.map_init (⟨id, rfl⟩ : PointedMap Γ Γ) g input
end Machine

/-- A nominal machine package retains its constructed transition closure in compiled code. -/
structure CachedPost (Γ : Type*) (n : ℕ) [Inhabited (Fin n)] where
  machine : TM0.Machine Γ (Fin n)
  stateCount : ℕ

section Packed
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ] [Hashable Λ]

/-- Construct the actual lookup data before allocating the packaged transition closure. -/
@[noinline] def hashNumberPack (M : TM0.Machine Γ Λ) (labels : List Λ) :
    CachedPost Γ (labels.length + 1) :=
  let index := hashNumberIndex labels
  let table := (default :: labels).toArray
  { machine := M.map ⟨id, rfl⟩ ⟨id, rfl⟩
      (fun q ↦ (index[q]?).getD 0)
      (fun q ↦ table[q.val]'(by
        simpa only [table, List.size_toArray, List.length_cons] using q.isLt))
    stateCount := labels.length + 1 }

/-- Nominal packing changes compiled caching, while its transition function is exactly the same. -/
theorem hashNumberPack_machine (M : TM0.Machine Γ Λ) (labels : List Λ) :
    (hashNumberPack M labels).machine = hashNumberMachine M labels := rfl

/-- The packed machine retains both halting directions on every supported covered input. -/
theorem hashNumberPack_dom (M : TM0.Machine Γ Λ) (labels : List Λ)
    (S : Set Λ) (ss : TM0.Supports M S) (cover : ∀ q ∈ S, q ∈ default :: labels)
    (input : List Γ) :
    (TM0.eval (hashNumberPack M labels).machine input).Dom ↔ (TM0.eval M input).Dom := by
  rw [hashNumberPack_machine]
  exact hashNumberMachine_dom M labels S ss cover input
end Packed

end ConjectureMachines.Compilation
