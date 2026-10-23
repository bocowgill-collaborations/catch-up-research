/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.Stack

/-! Binary block compilation with shared continuations for tape-independent jumps. -/
@[expose] public section

namespace ConjectureMachines.Compilation.Block
open Turing StateTransition Relation TM1

variable {Γ Λ σ : Type*} [Inhabited Γ] [Fintype Γ] [Fintype σ] [DecidableEq Λ]

/-- The destination can depend on the store, but not on the scanned tape symbol. -/
def HeadFree (l : Γ → σ → Λ) : Prop := ∀ a v, l a v = l default v

instance (l : Γ → σ → Λ) : Decidable (HeadFree l) :=
  inferInstanceAs (Decidable (∀ a v, l a v = l default v))

/-- Mathlib's block translation, bypassing the read for a verified head-free jump. -/
def fastNormal (C : BlockCode Γ) : Stmt Γ Λ σ → Stmt Bool (TM1to1.Λ' Γ Λ σ) σ
  | .move d q => TM1to1.move C.width d (fastNormal C q)
  | .write f q => TM1to1.read C.decode fun a ↦ .goto fun _ v ↦ .write (f a v) q
  | .load f q =>
    TM1to1.read C.decode fun a ↦ .load (fun _ v ↦ f a v) (fastNormal C q)
  | .branch p q r =>
    TM1to1.read C.decode fun a ↦ .branch (fun _ v ↦ p a v) (fastNormal C q) (fastNormal C r)
  | .goto l =>
    if HeadFree l then .goto fun _ v ↦ .normal (l default v)
    else TM1to1.read C.decode fun a ↦ .goto fun _ v ↦ .normal (l a v)
  | .halt => .halt

/-- The optimized compiler uses exactly Mathlib's normal and auxiliary-write labels. -/
def compiler (C : BlockCode Γ) (M : Λ → Stmt Γ Λ σ) :
    TM1to1.Λ' Γ Λ σ → Stmt Bool (TM1to1.Λ' Γ Λ σ) σ
  | .normal l => fastNormal C (M l)
  | .write a q =>
    TM1to1.write (C.encode a).toList (TM1to1.move C.width Dir.left (fastNormal C q))

/-- Each source step is simulated by one or more target steps, including at halt. -/
theorem fast_respects (C : BlockCode Γ) (M : Λ → Stmt Γ Λ σ) :
    Respects (step M) (step (compiler C M))
      fun c₁ c₂ ↦ TM1to1.trCfg C.encode C.blank c₁ = c₂ :=
  fun_respects.2 fun ⟨l₁, v, T⟩ ↦ by
    obtain ⟨L, R, rfl⟩ := T.exists_mk'
    rcases l₁ with - | l₁
    · exact rfl
    suffices ∀ q R,
        Reaches (step (compiler C M))
          (stepAux (fastNormal C q) v (TM1to1.trTape' C.blank L R))
          (TM1to1.trCfg C.encode C.blank (stepAux q v (Tape.mk' L R))) by
      refine TransGen.head' rfl ?_
      rw [TM1to1.trTape_mk']
      exact this _ R
    clear R l₁
    intro q R
    induction q generalizing v L R with
    | move d q IH =>
      cases d <;>
        simp only [fastNormal, TM1to1.stepAux_move, stepAux, Tape.move_left_mk',
          TM1to1.trTape'_move_left C.blank, TM1to1.trTape'_move_right C.blank] <;>
        apply IH
    | write f q IH =>
      simp only [fastNormal, TM1to1.stepAux_read C.decode C.blank C.roundtrip, stepAux]
      refine ReflTransGen.head rfl ?_
      obtain ⟨a, R, rfl⟩ := R.exists_cons
      rw [compiler, Tape.mk'_head, TM1to1.stepAux_write, ListBlank.head_cons,
        TM1to1.stepAux_move, TM1to1.trTape'_move_left C.blank]
      simpa using! IH ..
    | load a q IH =>
      simp only [fastNormal, TM1to1.stepAux_read C.decode C.blank C.roundtrip]
      apply IH
    | branch p q r IHq IHr =>
      simp only [fastNormal, TM1to1.stepAux_read C.decode C.blank C.roundtrip,
        stepAux, Tape.mk'_head]
      grind
    | goto l =>
      by_cases h : HeadFree l
      · simp only [fastNormal, ite_eq_left h, stepAux, TM1to1.trCfg,
          TM1to1.trTape_mk', Tape.mk'_head, h R.head v]
        exact ReflTransGen.refl
      · simp only [fastNormal, ite_eq_right h,
          TM1to1.stepAux_read C.decode C.blank C.roundtrip, stepAux, TM1to1.trCfg,
          TM1to1.trTape_mk']
        exact ReflTransGen.refl
    | halt =>
      simp only [fastNormal, stepAux, TM1to1.trCfg, TM1to1.trTape_mk']
      apply ReflTransGen.refl

section Initial
variable [Inhabited Λ] [Inhabited σ]

/-- Both halting directions hold on the actual finite encoded input. -/
theorem fast_dom (C : BlockCode Γ) (M : Λ → Stmt Γ Λ σ) (input : List Γ) :
    (TM1.eval (compiler C M) (blockInput C input)).Dom ↔ (TM1.eval M input).Dom :=
  StateTransition.tr_eval_dom (fast_respects C M) (blockCfg_init C input)
end Initial

section Support
variable [Inhabited Λ]

/-- The optimization preserves Mathlib's original finite set of generated labels. -/
theorem fast_supports_mathlib (C : BlockCode Γ) (M : Λ → Stmt Γ Λ σ)
    {S : Finset Λ} (ss : Supports M S) :
    Supports (compiler C M) (TM1to1.trSupp M S) := by
  classical
  let : DecidableEq (TM1to1.Λ' Γ Λ σ) := Classical.decEq _
  refine ⟨Finset.mem_biUnion.2 ⟨_, ss.1, Finset.mem_insert_self _ _⟩, ?_⟩
  intro q h
  suffices ∀ q, SupportsStmt S q →
      (∀ q' ∈ TM1to1.writes q, q' ∈ TM1to1.trSupp M S) →
      SupportsStmt (TM1to1.trSupp M S) (fastNormal C q) ∧
      ∀ q' ∈ TM1to1.writes q, SupportsStmt (TM1to1.trSupp M S) (compiler C M q') by
    rcases Finset.mem_biUnion.1 h with ⟨l, hl, h⟩
    have hh := this _ (ss.2 _ hl)
      fun q' hq ↦ Finset.mem_biUnion.2 ⟨_, hl, Finset.mem_insert_of_mem hq⟩
    rcases Finset.mem_insert.1 h with (rfl | h)
    exacts [hh.1, hh.2 _ h]
  intro q hs hw
  induction q with
  | move d q IH =>
    unfold TM1to1.writes at hw ⊢
    replace IH := IH hs hw
    refine ⟨?_, IH.2⟩
    cases d <;> simp only [fastNormal, TM1to1.supportsStmt_move, IH]
  | write f q IH =>
    unfold TM1to1.writes at hw ⊢
    simp only [Finset.mem_image, Finset.mem_union, Finset.mem_univ, true_and] at hw ⊢
    replace IH := IH hs fun q hq ↦ hw q (Or.inr hq)
    refine ⟨TM1to1.supportsStmt_read _ fun a _ s ↦ hw _ (Or.inl ⟨_, rfl⟩), ?_⟩
    intro q' hq
    rcases hq with (⟨a, q₂, rfl⟩ | hq)
    · simp only [compiler, TM1to1.supportsStmt_write, TM1to1.supportsStmt_move, IH.1]
    · exact IH.2 _ hq
  | load a q IH =>
    unfold TM1to1.writes at hw ⊢
    replace IH := IH hs hw
    exact ⟨TM1to1.supportsStmt_read _ fun _ ↦ IH.1, IH.2⟩
  | branch p q r IHq IHr =>
    unfold TM1to1.writes at hw ⊢
    simp only [Finset.mem_union] at hw ⊢
    replace IHq := IHq hs.1 fun q hq ↦ hw q (Or.inl hq)
    replace IHr := IHr hs.2 fun q hq ↦ hw q (Or.inr hq)
    exact ⟨TM1to1.supportsStmt_read _ fun _ ↦ ⟨IHq.1, IHr.1⟩,
      fun q ↦ Or.rec (IHq.2 _) (IHr.2 _)⟩
  | goto l =>
    simp only [TM1to1.writes, Finset.notMem_empty]
    refine ⟨?_, fun _ ↦ False.elim⟩
    by_cases h : HeadFree l
    · simp only [fastNormal, ite_eq_left h, SupportsStmt]
      exact fun _ v ↦ Finset.mem_biUnion.2 ⟨_, hs default v, Finset.mem_insert_self _ _⟩
    · simp only [fastNormal, ite_eq_right h]
      exact TM1to1.supportsStmt_read _ fun a _ v ↦
        Finset.mem_biUnion.2 ⟨_, hs a v, Finset.mem_insert_self _ _⟩
  | halt =>
    simp only [TM1to1.writes, Finset.notMem_empty]
    refine ⟨?_, fun _ ↦ False.elim⟩
    simp only [SupportsStmt, fastNormal]

variable [DecidableEq Γ] [DecidableEq σ]

/-- The executable collector from `Finite` supports the optimized binary compiler. -/
theorem fast_supports (C : BlockCode Γ) (M : Λ → Stmt Γ Λ σ)
    {S : Finset Λ} (ss : Supports M S) :
    Supports (compiler C M) (binarySupport M S) := by
  rw [binarySupport_eq]
  exact fast_supports_mathlib C M ss
end Support

/-- Ordered reusable support; labels have the same shapes as Mathlib's block compiler. -/
def orderedLabels (M : Λ → Stmt Γ Λ σ) (labels : List Λ) (symbols : List Γ) :
    List (TM1to1.Λ' Γ Λ σ) := binarySupportList M labels symbols

omit [Inhabited Γ] [Fintype σ] in
/-- An alphabet-covering traversal yields exactly the original generated-label support. -/
theorem orderedLabels_mem (M : Λ → Stmt Γ Λ σ) (labels : List Λ)
    (symbols : List Γ) (cover : ∀ a, a ∈ symbols) (q : TM1to1.Λ' Γ Λ σ) :
    q ∈ orderedLabels M labels symbols ↔ q ∈ TM1to1.trSupp M labels.toFinset :=
  mem_binarySupportList M labels symbols cover q

/-- Every jump in the statement, including all continuations, ignores the tape head. -/
def AllHeadFree : Stmt Γ Λ σ → Prop
  | .move _ q | .write _ q | .load _ q => AllHeadFree q
  | .branch _ q r => AllHeadFree q ∧ AllHeadFree r
  | .goto l => HeadFree l
  | .halt => True

/-- Block translation with every jump shared directly, without a runtime equality decision. -/
def fastNormalFree (C : BlockCode Γ) : Stmt Γ Λ σ → Stmt Bool (TM1to1.Λ' Γ Λ σ) σ
  | .move d q => TM1to1.move C.width d (fastNormalFree C q)
  | .write f q => TM1to1.read C.decode fun a ↦ .goto fun _ v ↦ .write (f a v) q
  | .load f q =>
    TM1to1.read C.decode fun a ↦ .load (fun _ v ↦ f a v) (fastNormalFree C q)
  | .branch p q r =>
    TM1to1.read C.decode fun a ↦
      .branch (fun _ v ↦ p a v) (fastNormalFree C q) (fastNormalFree C r)
  | .goto l => .goto fun _ v ↦ .normal (l default v)
  | .halt => .halt

/-- Equality-free executable compiler; safety of all source jumps is a separate proof premise. -/
def compilerFree (C : BlockCode Γ) (M : Λ → Stmt Γ Λ σ) :
    TM1to1.Λ' Γ Λ σ → Stmt Bool (TM1to1.Λ' Γ Λ σ) σ
  | .normal l => fastNormalFree C (M l)
  | .write a q =>
    TM1to1.write (C.encode a).toList (TM1to1.move C.width Dir.left (fastNormalFree C q))

omit [Fintype Γ] [Fintype σ] [DecidableEq Λ] in
/-- Head-free jumps on a supported source invariant make the equality-free compiler exact. -/
theorem free_respects [Inhabited Λ] (C : BlockCode Γ) (M : Λ → Stmt Γ Λ σ)
    {S : Finset Λ} (ss : Supports M S) (hM : ∀ l ∈ S, AllHeadFree (M l)) :
    Respects (step M) (step (compilerFree C M))
      fun c₁ c₂ ↦ c₁.l ∈ Finset.insertNone S ∧ TM1to1.trCfg C.encode C.blank c₁ = c₂ := by
    intro c₁ c₂ h
    obtain ⟨hc, rfl⟩ := h
    rcases c₁ with ⟨l₁, v, T⟩
    obtain ⟨L, R, rfl⟩ := T.exists_mk'
    rcases l₁ with - | l₁
    · exact rfl
    refine ⟨TM1to1.trCfg C.encode C.blank (stepAux (M l₁) v (Tape.mk' L R)),
      ⟨step_supports M ss rfl hc, rfl⟩, ?_⟩
    suffices ∀ q R, AllHeadFree q →
        Reaches (step (compilerFree C M))
          (stepAux (fastNormalFree C q) v (TM1to1.trTape' C.blank L R))
          (TM1to1.trCfg C.encode C.blank (stepAux q v (Tape.mk' L R))) by
      refine TransGen.head' rfl ?_
      rw [TM1to1.trTape_mk']
      exact this _ R (hM l₁ (Finset.some_mem_insertNone.mp hc))
    clear hc R l₁
    intro q R
    induction q generalizing v L R with
    | move d q IH =>
      intro hq
      cases d <;>
        simp only [fastNormalFree, TM1to1.stepAux_move, stepAux, Tape.move_left_mk',
          TM1to1.trTape'_move_left C.blank, TM1to1.trTape'_move_right C.blank] <;>
        exact IH _ _ _ hq
    | write f q IH =>
      intro hq
      simp only [fastNormalFree, TM1to1.stepAux_read C.decode C.blank C.roundtrip, stepAux]
      refine ReflTransGen.head rfl ?_
      obtain ⟨a, R, rfl⟩ := R.exists_cons
      rw [compilerFree, Tape.mk'_head, TM1to1.stepAux_write, ListBlank.head_cons,
        TM1to1.stepAux_move, TM1to1.trTape'_move_left C.blank]
      simpa using! IH _ _ _ hq
    | load a q IH =>
      intro hq
      simp only [fastNormalFree, TM1to1.stepAux_read C.decode C.blank C.roundtrip]
      exact IH _ _ _ hq
    | branch p q r IHq IHr =>
      rintro ⟨hq, hr⟩
      simp only [fastNormalFree, TM1to1.stepAux_read C.decode C.blank C.roundtrip,
        stepAux, Tape.mk'_head]
      grind
    | goto l =>
      intro hq
      simp only [fastNormalFree, stepAux, TM1to1.trCfg, TM1to1.trTape_mk',
        Tape.mk'_head, hq R.head v]
      exact ReflTransGen.refl
    | halt =>
      intro _
      simp only [fastNormalFree, stepAux, TM1to1.trCfg, TM1to1.trTape_mk']
      exact ReflTransGen.refl

omit [Fintype Γ] [Fintype σ] [DecidableEq Λ] in
/-- Both halting directions for the equality-free compiler on a proved source support. -/
theorem free_dom [Inhabited Λ] [Inhabited σ] (C : BlockCode Γ)
    (M : Λ → Stmt Γ Λ σ) {S : Finset Λ} (ss : Supports M S)
    (hM : ∀ l ∈ S, AllHeadFree (M l)) (input : List Γ) :
    (TM1.eval (compilerFree C M) (blockInput C input)).Dom ↔ (TM1.eval M input).Dom :=
  StateTransition.tr_eval_dom (free_respects C M ss hM)
    ⟨Finset.some_mem_insertNone.mpr ss.1, blockCfg_init C input⟩

omit [Fintype σ] [DecidableEq Λ] in
/-- Direct jumps remain supported even without a head-freedom assumption. -/
theorem free_supports_mathlib [Inhabited Λ] (C : BlockCode Γ) (M : Λ → Stmt Γ Λ σ)
    {S : Finset Λ} (ss : Supports M S) :
    Supports (compilerFree C M) (TM1to1.trSupp M S) := by
  classical
  refine ⟨Finset.mem_biUnion.2 ⟨_, ss.1, Finset.mem_insert_self _ _⟩, ?_⟩
  intro q h
  suffices ∀ q, SupportsStmt S q →
      (∀ q' ∈ TM1to1.writes q, q' ∈ TM1to1.trSupp M S) →
      SupportsStmt (TM1to1.trSupp M S) (fastNormalFree C q) ∧
      ∀ q' ∈ TM1to1.writes q, SupportsStmt (TM1to1.trSupp M S) (compilerFree C M q') by
    rcases Finset.mem_biUnion.1 h with ⟨l, hl, h⟩
    have hh := this _ (ss.2 _ hl)
      fun q' hq ↦ Finset.mem_biUnion.2 ⟨_, hl, Finset.mem_insert_of_mem hq⟩
    rcases Finset.mem_insert.1 h with (rfl | h)
    exacts [hh.1, hh.2 _ h]
  intro q hs hw
  induction q with
  | move d q IH =>
    unfold TM1to1.writes at hw ⊢
    replace IH := IH hs hw
    refine ⟨?_, IH.2⟩
    cases d <;> simp only [fastNormalFree, TM1to1.supportsStmt_move, IH]
  | write f q IH =>
    unfold TM1to1.writes at hw ⊢
    simp only [Finset.mem_image, Finset.mem_union, Finset.mem_univ, true_and] at hw ⊢
    replace IH := IH hs fun q hq ↦ hw q (Or.inr hq)
    refine ⟨TM1to1.supportsStmt_read _ fun a _ s ↦ hw _ (Or.inl ⟨_, rfl⟩), ?_⟩
    intro q' hq
    rcases hq with (⟨a, q₂, rfl⟩ | hq)
    · simp only [compilerFree, TM1to1.supportsStmt_write, TM1to1.supportsStmt_move, IH.1]
    · exact IH.2 _ hq
  | load a q IH =>
    unfold TM1to1.writes at hw ⊢
    replace IH := IH hs hw
    exact ⟨TM1to1.supportsStmt_read _ fun _ ↦ IH.1, IH.2⟩
  | branch p q r IHq IHr =>
    unfold TM1to1.writes at hw ⊢
    simp only [Finset.mem_union] at hw ⊢
    replace IHq := IHq hs.1 fun q hq ↦ hw q (Or.inl hq)
    replace IHr := IHr hs.2 fun q hq ↦ hw q (Or.inr hq)
    exact ⟨TM1to1.supportsStmt_read _ fun _ ↦ ⟨IHq.1, IHr.1⟩,
      fun q ↦ Or.rec (IHq.2 _) (IHr.2 _)⟩
  | goto l =>
    simp only [TM1to1.writes, Finset.notMem_empty]
    refine ⟨?_, fun _ ↦ False.elim⟩
    exact fun _ v ↦ Finset.mem_biUnion.2 ⟨_, hs default v, Finset.mem_insert_self _ _⟩
  | halt =>
    simp only [TM1to1.writes, Finset.notMem_empty]
    refine ⟨?_, fun _ ↦ False.elim⟩
    simp only [SupportsStmt, fastNormalFree]

/-- The unchanged executable label collector also supports the equality-free compiler. -/
theorem free_supports [Inhabited Λ] [DecidableEq Γ] [DecidableEq σ]
    (C : BlockCode Γ) (M : Λ → Stmt Γ Λ σ) {S : Finset Λ} (ss : Supports M S) :
    Supports (compilerFree C M) (binarySupport M S) := by
  rw [binarySupport_eq]
  exact free_supports_mathlib C M ss

end ConjectureMachines.Compilation.Block
