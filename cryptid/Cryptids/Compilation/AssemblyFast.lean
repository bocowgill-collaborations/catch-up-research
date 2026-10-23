/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.Assembly
public import Cryptids.Compilation.NumberTM1
public import Cryptids.Compilation.HashSupport
public import Cryptids.Compilation.HashNumber
public import Cryptids.Compilation.Memo

/-! Finite numeric shared control and hashed support, with the same source semantics. -/
@[expose] public section
namespace ConjectureMachines.Compilation
open Turing
set_option maxSynthPendingDepth 128

section
variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)]
variable [Fintype σ] [DecidableEq σ] [DecidableEq Λ] [Inhabited Λ] [Inhabited σ]
variable [Hashable σ] [Hashable (TM2to1.Γ' K Γ)]
variable (M : Λ → TM2.Stmt Γ Λ σ) (C : BlockCode (TM2to1.Γ' K Γ))
variable (labels : List Λ)

def fastTM1 : Fin ((sharedTapeLabels M labels).length + 1) →
    TM1.Stmt (TM2to1.Γ' K Γ) (Fin ((sharedTapeLabels M labels).length + 1)) σ :=
  TM1Number.numberProgram (TM1Normalize.tr (TM2to1.tr M)) (sharedTapeLabels M labels)

omit [Inhabited σ] [Hashable σ] [Hashable (TM2to1.Γ' K Γ)] in
theorem fastTM1_supports : TM1.Supports (fastTM1 M labels) Finset.univ :=
  TM1Number.numberProgram_supports _ _

omit [Inhabited σ] [Hashable σ] [Hashable (TM2to1.Γ' K Γ)] in
theorem normalized_supports (ss : TM2.Supports M labels.toFinset) :
    TM1.Supports (TM1Normalize.tr (TM2to1.tr M))
      (default :: sharedTapeLabels M labels).toFinset := by
  have hs : (stackSupportList M labels).toFinset = TM2to1.trSupp M labels.toFinset := by
    ext q
    simp only [List.mem_toFinset, mem_stackSupportList]
  have h1 : TM1.Supports (TM2to1.tr M) (stackSupportList M labels).toFinset := by
    rw [hs]
    exact TM2to1.tr_supports M ss
  have h2 := TM1Normalize.tr_supports (TM2to1.tr M) (stackSupportList M labels) h1
  change TM1.Supports _ (sharedTapeLabels M labels).toFinset at h2
  simpa only [List.toFinset_cons, Finset.insert_eq_of_mem h2.1] using h2

omit [Inhabited σ] [Hashable σ] [Hashable (TM2to1.Γ' K Γ)] in
theorem fastTM1_allFree (q : Fin ((sharedTapeLabels M labels).length + 1)) :
    Block.AllHeadFree (fastTM1 M labels q) := by
  apply TM1Number.numberProgram_allHeadFree
  intro r hr
  rcases List.mem_cons.mp (List.mem_toFinset.mp hr) with hr | hr
  · subst r
    exact FreeNormalize.normalize_preserves_allFree _ _ (FreeNormalize.stack_allFree M default)
  · exact FreeNormalize.normalize_stackSupportList_allFree M _ r hr

def fastBinary (stores : List σ) :=
  Block.compilerFree C (memoProgram stores (fastTM1 M labels))
def fastPost (stores : List σ) := TM1to0.tr (fastBinary M C labels stores)
instance fastPostDecidableEq (stores : List σ) :
    DecidableEq (TM1to0.Λ' (fastBinary M C labels stores)) :=
  letI : DecidableEq (Fin ((sharedTapeLabels M labels).length + 1)) := fun a b ↦
    if h : a.val = b.val then isTrue (Fin.ext h)
    else isFalse (fun e ↦ h (congrArg Fin.val e))
  postLabelDecidableEq _
instance fastPostHashable (stores : List σ) :
    Hashable (TM1to0.Λ' (fastBinary M C labels stores)) :=
  letI : Hashable (Fin ((sharedTapeLabels M labels).length + 1)) := ⟨fun q ↦ hash q.val⟩
  inferInstanceAs (Hashable (Option (TM1.Stmt Bool
    (TM1to1.Λ' (TM2to1.Γ' K Γ) (Fin ((sharedTapeLabels M labels).length + 1)) σ) σ) × σ))

def fastBinaryLabels (symbols : List (TM2to1.Γ' K Γ)) (stores : List σ) :=
  binarySupportList (memoProgram stores (fastTM1 M labels))
    (List.finRange ((sharedTapeLabels M labels).length + 1)) symbols

def fastLabels (symbols : List (TM2to1.Γ' K Γ)) (stores : List σ) :
    List (TM1to0.Λ' (fastBinary M C labels stores)) :=
  let source := cachedProgram stores (fastTM1 M labels)
  let binary := Block.compilerFree C source.get
  let binaryLabels := binarySupportList source.get
    (List.finRange ((sharedTapeLabels M labels).length + 1)) symbols
  hashUnique (postSupportList binary binaryLabels stores)

theorem fast_supported (symbols : List (TM2to1.Γ' K Γ)) (cover : ∀ a, a ∈ symbols)
    (stores : List σ) (storeCover : ∀ v, v ∈ stores) :
    TM0.Supports (fastPost M C labels stores)
      ↑(fastLabels M C labels symbols stores).toFinset := by
  have hm := memoProgram_eq stores storeCover (fastTM1 M labels) (fastTM1_allFree M labels)
  have hb : (fastBinaryLabels M labels symbols stores).toFinset =
      binarySupport (memoProgram stores (fastTM1 M labels)) Finset.univ := by
    ext q
    simp only [fastBinaryLabels, List.mem_toFinset, mem_binarySupportList _ _ _ cover,
      List.toFinset_finRange, binarySupport_eq]
  have h3 : TM1.Supports (fastBinary M C labels stores)
      (fastBinaryLabels M labels symbols stores).toFinset := by
    rw [hb]
    apply Block.free_supports
    rw [hm]
    exact fastTM1_supports M labels
  have hp : (fastLabels M C labels symbols stores).toFinset =
      TM1to0.trStmts (fastBinary M C labels stores)
        (fastBinaryLabels M labels symbols stores).toFinset := by
    change (hashUnique (postSupportList (fastBinary M C labels stores)
      (fastBinaryLabels M labels symbols stores) stores)).toFinset = _
    ext q
    simp only [List.mem_toFinset, mem_hashUnique, mem_postSupportList _ _ _ storeCover]
  rw [hp]
  exact TM1to0.tr_supports _ h3

/-- Practical constructive source-to-Post compiler; all memory is still unbounded tape. -/
def fastStack (symbols : List (TM2to1.Γ' K Γ)) (stores : List σ) (k : K) : NumberedPost :=
  let source := cachedProgram stores (fastTM1 M labels)
  let binary := Block.compilerFree C source.get
  let qs := fastLabels M C labels symbols stores
  letI : Hashable (TM1to0.Λ' binary) := fastPostHashable M C labels stores
  letI : DecidableEq (TM1to0.Λ' binary) := fastPostDecidableEq M C labels stores
  let packed := hashNumberPack (TM1to0.tr binary) qs
  { extraStates := qs.length
    machine := packed.machine
    input := blockInput C (TM2to1.trInit k []) }

theorem fastStack_halts (ss : TM2.Supports M labels.toFinset)
    (symbols : List (TM2to1.Γ' K Γ)) (cover : ∀ a, a ∈ symbols)
    (stores : List σ) (storeCover : ∀ v, v ∈ stores) (k : K) :
    (fastStack M C labels symbols stores k).Halts ↔ (TM2.eval M k []).Dom := by
  have hn := hashNumberMachine_dom (fastPost M C labels stores)
    (fastLabels M C labels symbols stores)
    (↑(fastLabels M C labels symbols stores).toFinset)
    (fast_supported M C labels symbols cover stores storeCover)
    (by intro q hq; exact List.mem_cons_of_mem _ (List.mem_toFinset.mp hq))
    (blockInput C (TM2to1.trInit k []))
  have hm := memoProgram_eq stores storeCover (fastTM1 M labels) (fastTM1_allFree M labels)
  have hp : (TM0.eval (fastPost M C labels stores) (blockInput C (TM2to1.trInit k []))).Dom ↔
      (TM2.eval M k []).Dom := by
    rw [fastPost, TM1to0.tr_eval, fastBinary, hm]
    exact (Block.free_dom C _ (fastTM1_supports M labels)
      (fun q _ ↦ fastTM1_allFree M labels q) _).trans
      ((TM1Number.numberProgram_dom _ _ (normalized_supports M labels ss) _).trans
        ((TM1Normalize.tr_eval_dom _ _).trans (TM2to1.tr_eval_dom M k [])))
  change (TM0.eval (hashNumberPack (fastPost M C labels stores)
    (fastLabels M C labels symbols stores)).machine _).Dom ↔ _
  rw [hashNumberPack_machine]
  exact hn.trans hp
end
end ConjectureMachines.Compilation
