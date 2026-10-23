/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Computability.TuringMachine.StackTuringMachine
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Log

/-! Executable support extraction and restriction for Mathlib's Turing machines. -/
@[expose] public section

namespace ConjectureMachines.Compilation
open Turing

section Equality
variable {Γ Λ σ : Type*} [Fintype Γ] [Fintype σ]
variable [DecidableEq Γ] [DecidableEq Λ] [DecidableEq σ]

/-- Structural equality; finite function fields are compared by enumeration. -/
def tm1StmtDecEq (a b : TM1.Stmt Γ Λ σ) : Decidable (a = b) :=
  withPtrEqDecEq a b fun _ ↦
    match a, b with
    | .move d q, .move d' q' => by
      letI := tm1StmtDecEq q q'
      exact decidable_of_iff (d = d' ∧ q = q') (by simp)
    | .move d q, .write f' q' => isFalse (by intro h; cases h)
    | .move d q, .load f' q' => isFalse (by intro h; cases h)
    | .move d q, .branch p' q' r' => isFalse (by intro h; cases h)
    | .move d q, .goto f' => isFalse (by intro h; cases h)
    | .move d q, .halt => isFalse (by intro h; cases h)
    | .write f q, .move d' q' => isFalse (by intro h; cases h)
    | .write f q, .write f' q' => by
      letI := tm1StmtDecEq q q'
      exact decidable_of_iff (f = f' ∧ q = q') (by simp)
    | .write f q, .load f' q' => isFalse (by intro h; cases h)
    | .write f q, .branch p' q' r' => isFalse (by intro h; cases h)
    | .write f q, .goto f' => isFalse (by intro h; cases h)
    | .write f q, .halt => isFalse (by intro h; cases h)
    | .load f q, .move d' q' => isFalse (by intro h; cases h)
    | .load f q, .write f' q' => isFalse (by intro h; cases h)
    | .load f q, .load f' q' => by
      letI := tm1StmtDecEq q q'
      exact decidable_of_iff (f = f' ∧ q = q') (by simp)
    | .load f q, .branch p' q' r' => isFalse (by intro h; cases h)
    | .load f q, .goto f' => isFalse (by intro h; cases h)
    | .load f q, .halt => isFalse (by intro h; cases h)
    | .branch p q r, .move d' q' => isFalse (by intro h; cases h)
    | .branch p q r, .write f' q' => isFalse (by intro h; cases h)
    | .branch p q r, .load f' q' => isFalse (by intro h; cases h)
    | .branch p q r, .branch p' q' r' => by
      letI := tm1StmtDecEq q q'
      letI := tm1StmtDecEq r r'
      exact decidable_of_iff (p = p' ∧ q = q' ∧ r = r') (by simp)
    | .branch p q r, .goto f' => isFalse (by intro h; cases h)
    | .branch p q r, .halt => isFalse (by intro h; cases h)
    | .goto f, .move d' q' => isFalse (by intro h; cases h)
    | .goto f, .write f' q' => isFalse (by intro h; cases h)
    | .goto f, .load f' q' => isFalse (by intro h; cases h)
    | .goto f, .branch p' q' r' => isFalse (by intro h; cases h)
    | .goto f, .goto f' => by
      exact decidable_of_iff (f = f') (by simp)
    | .goto f, .halt => isFalse (by intro h; cases h)
    | .halt, .move d' q' => isFalse (by intro h; cases h)
    | .halt, .write f' q' => isFalse (by intro h; cases h)
    | .halt, .load f' q' => isFalse (by intro h; cases h)
    | .halt, .branch p' q' r' => isFalse (by intro h; cases h)
    | .halt, .goto f' => isFalse (by intro h; cases h)
    | .halt, .halt => by
      exact isTrue rfl
termination_by structural a

instance tm1StmtDecidableEq : DecidableEq (TM1.Stmt Γ Λ σ) := tm1StmtDecEq
end Equality

section StackEquality
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ] [DecidableEq Λ]
variable [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)]

/-- Decidable equality on the unbounded source syntax, including dependent stack alphabets. -/
def tm2StmtDecEq (a b : TM2.Stmt Γ Λ σ) : Decidable (a = b) :=
  withPtrEqDecEq a b fun _ ↦
    match a, b with
    | .push k f q, .push k' f' q' => by
      by_cases hk : k = k'
      · subst k'
        letI := tm2StmtDecEq q q'
        exact decidable_of_iff (f = f' ∧ q = q') (by simp)
      · exact isFalse (fun h ↦ hk (by cases h; rfl))
    | .push k f q, .peek k' f' q' => isFalse (by intro h; cases h)
    | .push k f q, .pop k' f' q' => isFalse (by intro h; cases h)
    | .push k f q, .load f' q' => isFalse (by intro h; cases h)
    | .push k f q, .branch p' q' r' => isFalse (by intro h; cases h)
    | .push k f q, .goto f' => isFalse (by intro h; cases h)
    | .push k f q, .halt  => isFalse (by intro h; cases h)
    | .peek k f q, .push k' f' q' => isFalse (by intro h; cases h)
    | .peek k f q, .peek k' f' q' => by
      by_cases hk : k = k'
      · subst k'
        letI := tm2StmtDecEq q q'
        exact decidable_of_iff (f = f' ∧ q = q') (by simp)
      · exact isFalse (fun h ↦ hk (by cases h; rfl))
    | .peek k f q, .pop k' f' q' => isFalse (by intro h; cases h)
    | .peek k f q, .load f' q' => isFalse (by intro h; cases h)
    | .peek k f q, .branch p' q' r' => isFalse (by intro h; cases h)
    | .peek k f q, .goto f' => isFalse (by intro h; cases h)
    | .peek k f q, .halt  => isFalse (by intro h; cases h)
    | .pop k f q, .push k' f' q' => isFalse (by intro h; cases h)
    | .pop k f q, .peek k' f' q' => isFalse (by intro h; cases h)
    | .pop k f q, .pop k' f' q' => by
      by_cases hk : k = k'
      · subst k'
        letI := tm2StmtDecEq q q'
        exact decidable_of_iff (f = f' ∧ q = q') (by simp)
      · exact isFalse (fun h ↦ hk (by cases h; rfl))
    | .pop k f q, .load f' q' => isFalse (by intro h; cases h)
    | .pop k f q, .branch p' q' r' => isFalse (by intro h; cases h)
    | .pop k f q, .goto f' => isFalse (by intro h; cases h)
    | .pop k f q, .halt  => isFalse (by intro h; cases h)
    | .load f q, .push k' f' q' => isFalse (by intro h; cases h)
    | .load f q, .peek k' f' q' => isFalse (by intro h; cases h)
    | .load f q, .pop k' f' q' => isFalse (by intro h; cases h)
    | .load f q, .load f' q' => by
      letI := tm2StmtDecEq q q'
      exact decidable_of_iff (f = f' ∧ q = q') (by simp)
    | .load f q, .branch p' q' r' => isFalse (by intro h; cases h)
    | .load f q, .goto f' => isFalse (by intro h; cases h)
    | .load f q, .halt  => isFalse (by intro h; cases h)
    | .branch p q r, .push k' f' q' => isFalse (by intro h; cases h)
    | .branch p q r, .peek k' f' q' => isFalse (by intro h; cases h)
    | .branch p q r, .pop k' f' q' => isFalse (by intro h; cases h)
    | .branch p q r, .load f' q' => isFalse (by intro h; cases h)
    | .branch p q r, .branch p' q' r' => by
      letI := tm2StmtDecEq q q'
      letI := tm2StmtDecEq r r'
      exact decidable_of_iff (p = p' ∧ q = q' ∧ r = r') (by simp)
    | .branch p q r, .goto f' => isFalse (by intro h; cases h)
    | .branch p q r, .halt  => isFalse (by intro h; cases h)
    | .goto f, .push k' f' q' => isFalse (by intro h; cases h)
    | .goto f, .peek k' f' q' => isFalse (by intro h; cases h)
    | .goto f, .pop k' f' q' => isFalse (by intro h; cases h)
    | .goto f, .load f' q' => isFalse (by intro h; cases h)
    | .goto f, .branch p' q' r' => isFalse (by intro h; cases h)
    | .goto f, .goto f' => by
      exact decidable_of_iff (f = f') (by simp)
    | .goto f, .halt  => isFalse (by intro h; cases h)
    | .halt, .push k' f' q' => isFalse (by intro h; cases h)
    | .halt, .peek k' f' q' => isFalse (by intro h; cases h)
    | .halt, .pop k' f' q' => isFalse (by intro h; cases h)
    | .halt, .load f' q' => isFalse (by intro h; cases h)
    | .halt, .branch p' q' r' => isFalse (by intro h; cases h)
    | .halt, .goto f' => isFalse (by intro h; cases h)
    | .halt, .halt  => by
      exact isTrue rfl
termination_by structural a

instance tm2StmtDecidableEq : DecidableEq (TM2.Stmt Γ Λ σ) := tm2StmtDecEq

instance stackActionDecidableEq {k : K} : DecidableEq (TM2to1.StAct K Γ σ k)
  | .push f, .push g => decidable_of_iff (f = g) (by simp)
  | .peek f, .peek g => decidable_of_iff (f = g) (by simp)
  | .pop f, .pop g => decidable_of_iff (f = g) (by simp)
  | .push _, .peek _ | .push _, .pop _ | .peek _, .push _ | .peek _, .pop _
  | .pop _, .push _ | .pop _, .peek _ => isFalse (by intro h; cases h)

instance stackLabelDecidableEq : DecidableEq (TM2to1.Λ' K Γ Λ σ)
  | .normal l, .normal m => decidable_of_iff (l = m) (by simp)
  | .ret q, .ret r => decidable_of_iff (q = r) (by simp)
  | .go k a q, .go k' a' q' => by
    by_cases hk : k = k'
    · subst k'
      exact decidable_of_iff (a = a' ∧ q = q') (by simp)
    · exact isFalse (fun h ↦ hk (by cases h; rfl))
  | .normal _, .go _ _ _ | .normal _, .ret _ | .go _ _ _, .normal _
  | .go _ _ _, .ret _ | .ret _, .normal _ | .ret _, .go _ _ _ =>
      isFalse (by intro h; cases h)
end StackEquality

section BinaryEquality
variable {Γ Λ σ : Type*} [Fintype Γ] [Fintype σ]
variable [DecidableEq Γ] [DecidableEq Λ] [DecidableEq σ]
instance binaryLabelDecidableEq : DecidableEq (TM1to1.Λ' Γ Λ σ)
  | .normal l, .normal m => decidable_of_iff (l = m) (by simp)
  | .write a q, .write b r => decidable_of_iff (a = b ∧ q = r) (by simp)
  | .normal _, .write _ _ | .write _ _, .normal _ => isFalse (by intro h; cases h)
end BinaryEquality

/-- Equality on Mathlib's reducible alphabet wrapper. -/
instance stackAlphabetDecidableEq {K : Type*} {Γ : K → Type*} [Fintype K]
    [∀ k, DecidableEq (Γ k)] : DecidableEq (TM2to1.Γ' K Γ) :=
  inferInstanceAs (DecidableEq (Bool × ∀ k, Option (Γ k)))

/-- Equality on Mathlib's reducible Post-control wrapper. -/
instance postLabelDecidableEq {Γ Λ σ : Type*} [Fintype Γ] [Fintype σ]
    [DecidableEq Γ] [DecidableEq Λ] [DecidableEq σ] (M : Λ → TM1.Stmt Γ Λ σ) :
    DecidableEq (TM1to0.Λ' M) :=
  inferInstanceAs (DecidableEq (Option (TM1.Stmt Γ Λ σ) × σ))

section Collectors
variable {Γ Λ σ : Type*} [Fintype Γ] [Fintype σ]
variable [DecidableEq Γ] [DecidableEq Λ] [DecidableEq σ]

/-- Executable subterm closure. -/
def subterms : TM1.Stmt Γ Λ σ → Finset (TM1.Stmt Γ Λ σ)
  | Q@(.move _ q) | Q@(.write _ q) | Q@(.load _ q) => insert Q (subterms q)
  | Q@(.branch _ q r) => insert Q (subterms q ∪ subterms r)
  | Q => {Q}

theorem subterms_eq (q : TM1.Stmt Γ Λ σ) : subterms q = TM1.stmts₁ q := by
  induction q <;> ext x <;> simp_all [subterms, TM1.stmts₁]

/-- Executable finite support for lowering TM1 into TM0. -/
def postSupport (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) :
    Finset (Option (TM1.Stmt Γ Λ σ) × σ) :=
  (Finset.insertNone (S.biUnion fun l ↦ subterms (M l))) ×ˢ Finset.univ

theorem postSupport_eq (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) :
    postSupport M S = TM1to0.trStmts M S := by
  ext x
  simp [postSupport, TM1to0.trStmts, TM1.stmts, subterms_eq]

/-- Executable auxiliary labels for binary alphabet reduction. -/
def binaryWrites : TM1.Stmt Γ Λ σ → Finset (TM1to1.Λ' Γ Λ σ)
  | .move _ q | .load _ q => binaryWrites q
  | .write _ q => (Finset.univ.image fun a ↦ TM1to1.Λ'.write a q) ∪ binaryWrites q
  | .branch _ q r => binaryWrites q ∪ binaryWrites r
  | .goto _ | .halt => ∅

theorem binaryWrites_eq (q : TM1.Stmt Γ Λ σ) : binaryWrites q = TM1to1.writes q := by
  induction q <;> ext x <;> simp_all [binaryWrites, TM1to1.writes]

/-- Executable finite control for binary alphabet reduction. -/
def binarySupport (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) :
    Finset (TM1to1.Λ' Γ Λ σ) :=
  S.biUnion fun l ↦ insert (.normal l) (binaryWrites (M l))

theorem binarySupport_eq (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) :
    binarySupport M S = TM1to1.trSupp M S := by
  ext x
  simp [binarySupport, TM1to1.trSupp, binaryWrites_eq]
end Collectors

section StackCollectors
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ] [DecidableEq Λ]
variable [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)]

/-- Executable auxiliary labels introduced by stack lowering. -/
def stackLabels : TM2.Stmt Γ Λ σ → Finset (TM2to1.Λ' K Γ Λ σ)
  | .push k f q => {.go k (.push f) q, .ret q} ∪ stackLabels q
  | .peek k f q => {.go k (.peek f) q, .ret q} ∪ stackLabels q
  | .pop k f q => {.go k (.pop f) q, .ret q} ∪ stackLabels q
  | .load _ q => stackLabels q
  | .branch _ q r => stackLabels q ∪ stackLabels r
  | .goto _ | .halt => ∅

theorem stackLabels_eq (q : TM2.Stmt Γ Λ σ) : stackLabels q = TM2to1.trStmts₁ q := by
  induction q <;> ext x <;> simp_all [stackLabels, TM2to1.trStmts₁]

/-- Executable finite control for stack lowering. -/
def stackSupport (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ) :
    Finset (TM2to1.Λ' K Γ Λ σ) :=
  S.biUnion fun l ↦ insert (.normal l) (stackLabels (M l))

theorem stackSupport_eq (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ) :
    stackSupport M S = TM2to1.trSupp M S := by
  ext x
  simp [stackSupport, TM2to1.trSupp, stackLabels_eq]
end StackCollectors

section Restriction
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ]
variable (M : TM0.Machine Γ Λ) (S : Finset Λ) (ss : TM0.Supports M ↑S)

/-- The initial label is retained by supported control restriction. -/
@[instance_reducible] def restrictedInhabited : Inhabited S := ⟨⟨default, ss.1⟩⟩

/-- Retraction into the given finite support; its default branch is unreachable. -/
def restrictLabel (q : Λ) : S := if h : q ∈ S then ⟨q, h⟩ else ⟨default, ss.1⟩

/-- Restrict a machine to its proved finite support. -/
def restrictMachine : @TM0.Machine Γ S (restrictedInhabited M S ss) :=
  letI := restrictedInhabited M S ss
  M.map (⟨id, rfl⟩ : PointedMap Γ Γ) (⟨id, rfl⟩ : PointedMap Γ Γ) (restrictLabel M S ss) Subtype.val

/-- Restriction preserves halting in both directions for every finite tape input. -/
theorem restrictMachine_dom (l : List Γ) :
    letI := restrictedInhabited M S ss
    (TM0.eval (restrictMachine M S ss) l).Dom ↔ (TM0.eval M l).Dom := by
  let := restrictedInhabited M S ss
  let g : PointedMap Λ S := ⟨restrictLabel M S ss, by
    apply Subtype.ext
    change (restrictLabel M S ss default).val = default
    unfold restrictLabel
    split <;> rfl⟩
  have h := TM0.Machine.map_respects M (⟨id, rfl⟩ : PointedMap Γ Γ) (⟨id, rfl⟩ : PointedMap Γ Γ) g
    Subtype.val ss (fun _ ↦ rfl) (by
      intro q hq
      change (restrictLabel M S ss q).val = q
      simp only [restrictLabel, dite_eq_left (show q ∈ S from hq)])
  have hi : (TM0.init l : TM0.Cfg Γ Λ).q ∈ (S : Set Λ) ∧
      TM0.Cfg.map (⟨id, rfl⟩ : PointedMap Γ Γ) g (TM0.init l) = TM0.init l := by
    refine ⟨ss.1, ?_⟩
    simpa using TM0.map_init (⟨id, rfl⟩ : PointedMap Γ Γ) g l
  exact StateTransition.tr_eval_dom h hi
end Restriction

section ListCollectors
variable {Γ Λ σ : Type*}

/-- Ordered subterm traversal, retaining duplicates to avoid quotient choice. -/
def subtermList : TM1.Stmt Γ Λ σ → List (TM1.Stmt Γ Λ σ)
  | Q@(.move _ q) | Q@(.write _ q) | Q@(.load _ q) => Q :: subtermList q
  | Q@(.branch _ q r) => Q :: (subtermList q ++ subtermList r)
  | Q => [Q]

theorem mem_subtermList (q r : TM1.Stmt Γ Λ σ) : r ∈ subtermList q ↔ r ∈ TM1.stmts₁ q := by
  classical
  induction q <;> simp_all [subtermList, TM1.stmts₁]

/-- Ordered auxiliary write-label traversal using an explicit alphabet. -/
def binaryWriteList (symbols : List Γ) : TM1.Stmt Γ Λ σ → List (TM1to1.Λ' Γ Λ σ)
  | .move _ q | .load _ q => binaryWriteList symbols q
  | .write _ q => symbols.map (fun a ↦ .write a q) ++ binaryWriteList symbols q
  | .branch _ q r => binaryWriteList symbols q ++ binaryWriteList symbols r
  | .goto _ | .halt => []

theorem mem_binaryWriteList [Fintype Γ] (symbols : List Γ) (cover : ∀ a, a ∈ symbols)
    (q : TM1.Stmt Γ Λ σ) (r : TM1to1.Λ' Γ Λ σ) :
    r ∈ binaryWriteList symbols q ↔ r ∈ TM1to1.writes q := by
  classical
  induction q <;> simp_all [binaryWriteList, TM1to1.writes]

/-- Ordered support traversal for binary reduction. -/
def binarySupportList (M : Λ → TM1.Stmt Γ Λ σ) (labels : List Λ) (symbols : List Γ) :
    List (TM1to1.Λ' Γ Λ σ) :=
  labels.flatMap fun l ↦ .normal l :: binaryWriteList symbols (M l)

theorem mem_binarySupportList [Fintype Γ] [DecidableEq Λ] (M : Λ → TM1.Stmt Γ Λ σ)
    (labels : List Λ) (symbols : List Γ) (cover : ∀ a, a ∈ symbols)
    (r : TM1to1.Λ' Γ Λ σ) :
    r ∈ binarySupportList M labels symbols ↔ r ∈ TM1to1.trSupp M labels.toFinset := by
  classical
  simp [binarySupportList, TM1to1.trSupp, mem_binaryWriteList symbols cover]

/-- Ordered product of subterms and local states, including the halted control. -/
def postSupportList (M : Λ → TM1.Stmt Γ Λ σ) (labels : List Λ) (stores : List σ) :
    List (TM1to0.Λ' M) :=
  (none :: (labels.flatMap fun l ↦ (subtermList (M l)).map some)).flatMap
    fun q ↦ stores.map fun v ↦ (q, v)

set_option backward.isDefEq.respectTransparency false in
theorem mem_postSupportList [Fintype σ] [DecidableEq Λ] (M : Λ → TM1.Stmt Γ Λ σ)
    (labels : List Λ) (stores : List σ) (cover : ∀ v, v ∈ stores) (r : TM1to0.Λ' M) :
    r ∈ postSupportList M labels stores ↔ r ∈ TM1to0.trStmts M labels.toFinset := by
  classical
  dsimp only [TM1to0.Λ'] at r ⊢
  obtain ⟨q, v⟩ := r
  cases q <;>
    simp [postSupportList, TM1to0.trStmts, TM1.stmts, cover, mem_subtermList, eq_comm,
      Finset.mem_product, Prod.mk.injEq]
end ListCollectors

section StackListCollectors
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- Ordered auxiliary label traversal for the multi-stack compiler. -/
def stackLabelList : TM2.Stmt Γ Λ σ → List (TM2to1.Λ' K Γ Λ σ)
  | .push k f q => .go k (.push f) q :: .ret q :: stackLabelList q
  | .peek k f q => .go k (.peek f) q :: .ret q :: stackLabelList q
  | .pop k f q => .go k (.pop f) q :: .ret q :: stackLabelList q
  | .load _ q => stackLabelList q
  | .branch _ q r => stackLabelList q ++ stackLabelList r
  | .goto _ | .halt => []

theorem mem_stackLabelList (q : TM2.Stmt Γ Λ σ) (r : TM2to1.Λ' K Γ Λ σ) :
    r ∈ stackLabelList q ↔ r ∈ TM2to1.trStmts₁ q := by
  classical
  induction q <;> simp_all [stackLabelList, TM2to1.trStmts₁]

/-- Ordered support traversal for stack lowering. -/
def stackSupportList (M : Λ → TM2.Stmt Γ Λ σ) (labels : List Λ) :
    List (TM2to1.Λ' K Γ Λ σ) :=
  labels.flatMap fun l ↦ .normal l :: stackLabelList (M l)

theorem mem_stackSupportList [DecidableEq Λ] (M : Λ → TM2.Stmt Γ Λ σ) (labels : List Λ)
    (r : TM2to1.Λ' K Γ Λ σ) :
    r ∈ stackSupportList M labels ↔ r ∈ TM2to1.trSupp M labels.toFinset := by
  classical
  simp [stackSupportList, TM2to1.trSupp, mem_stackLabelList]
end StackListCollectors

section Numbering
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ]
variable (M : TM0.Machine Γ Λ) (labels : List Λ)

/-- First occurrence numbering; the source initial state always has index zero. -/
def numberLabel (q : Λ) : Fin (labels.length + 1) :=
  if h : q ∈ default :: labels then
    ⟨(default :: labels).idxOf q, List.idxOf_lt_length_iff.mpr h⟩ else 0

/-- Decode a numbered state by the explicit initial-first label list. -/
def unnumberLabel (q : Fin (labels.length + 1)) : Λ := (default :: labels).get q

theorem unnumber_number {q : Λ} (hq : q ∈ default :: labels) :
    unnumberLabel labels (numberLabel labels q) = q := by
  simp only [numberLabel, dite_eq_left hq, unnumberLabel, List.get_eq_getElem]
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hq)

theorem numberLabel_default : numberLabel labels default = 0 := by
  apply Fin.ext
  simp [numberLabel]

/-- Executable numbering into a literal finite state type. Duplicate rows are retained. -/
def numberMachine : TM0.Machine Γ (Fin (labels.length + 1)) :=
  M.map ⟨id, rfl⟩ ⟨id, rfl⟩ (numberLabel labels) (unnumberLabel labels)

/-- Numbering preserves halting whenever the list covers a support invariant. -/
theorem numberMachine_dom (S : Set Λ) (ss : TM0.Supports M S)
    (cover : ∀ q ∈ S, q ∈ default :: labels) (l : List Γ) :
    (TM0.eval (numberMachine M labels) l).Dom ↔ (TM0.eval M l).Dom := by
  let g : PointedMap Λ (Fin (labels.length + 1)) :=
    ⟨numberLabel labels, numberLabel_default labels⟩
  have h := TM0.Machine.map_respects M ⟨id, rfl⟩ ⟨id, rfl⟩ g
    (unnumberLabel labels) ss (fun _ ↦ rfl) (fun q hq ↦ unnumber_number labels (cover q hq))
  apply StateTransition.tr_eval_dom h
  refine ⟨ss.1, ?_⟩
  simpa using TM0.map_init (⟨id, rfl⟩ : PointedMap Γ Γ) g l
end Numbering

end ConjectureMachines.Compilation
