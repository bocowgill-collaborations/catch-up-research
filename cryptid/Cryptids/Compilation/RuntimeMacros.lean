/-
Copyright 2026 The Cryptids Authors.
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The non-return macro proofs below are adapted from Mathlib's
Mathlib/Computability/TuringMachine/ToPartrec.lean (Mario Carneiro).
-/
module

public import Mathlib.Computability.TuringMachine.ToPartrec

/-! # Four-stack macros with arbitrary return dispatch

The machine may change every return-label instruction. Agreement on all other labels suffices
for the positive reachability proofs, which stop on entry to the supplied terminal label.
-/

@[expose] public section

namespace ConjectureMachines.Compilation.RuntimeMacros

open Turing PartrecToTM2 K' Relation StateTransition
open Function (update)

set_option backward.isDefEq.respectTransparency false

/-- Exactly the labels whose instructions remain Mathlib's stack operations. -/
def NonRet : Λ' → Prop
  | .ret _ => False
  | _ => True

/-- A machine may reinterpret every return label, but agrees at every other label. -/
def Agrees (M : Λ' → Stmt') : Prop := ∀ label, NonRet label → M label = tr label

variable {M : Λ' → Stmt'} (hM : Agrees M)

include hM

/-- Transfer a single operation; no step out of a return label is used. -/
theorem step_of_tr {label : Λ'} {s : Option Γ'} {S : K' → List Γ'} {next : Cfg'}
    (nonret : NonRet label) (h : next ∈ TM2.step tr ⟨some label, s, S⟩) :
    next ∈ TM2.step M ⟨some label, s, S⟩ := by
  simpa only [TM2.step, hM label nonret] using h

theorem move_ok {p k₁ k₂ q s L₁ o L₂} {S : K' → List Γ'} (h₁ : k₁ ≠ k₂)
    (e : splitAtPred p (S k₁) = (L₁, o, L₂)) :
    Reaches₁ (TM2.step M) ⟨some (Λ'.move p k₁ k₂ q), s, S⟩
      ⟨some q, o, update (update S k₁ L₂) k₂ (L₁.reverseAux (S k₂))⟩ := by
  induction L₁ generalizing S s with
  | nil =>
    rw [(_ : [].reverseAux _ = _), Function.update_eq_self]
    swap
    · rw [Function.update_of_ne h₁.symm, List.reverseAux_nil]
    refine TransGen.head' (step_of_tr hM (by trivial) rfl) ?_
    simp only [tr_move, pop', TM2.stepAux]
    grind [splitAtPred.eq_def]
  | cons a L₁ IH =>
    refine TransGen.head (step_of_tr hM (by trivial) rfl) ?_
    rw [tr]; simp only [pop', Option.elim, TM2.stepAux, push']
    rcases e₁ : S k₁ with - | ⟨a', Sk⟩ <;> rw [e₁, splitAtPred] at e
    · cases e
    cases e₂ : p a' <;> simp only [e₂, cond] at e
    swap
    · cases e
    rcases e₃ : splitAtPred p Sk with ⟨_, _, _⟩
    rw [e₃] at e
    cases e
    simp only [List.head?_cons, e₂, List.tail_cons, Bool.cond_false]
    convert! @IH _ (update (update S k₁ Sk) k₂ (a :: S k₂)) _ using 2 <;>
      simp [Function.update_of_ne, h₁, h₁.symm, e₃, List.reverseAux]
    simp [Function.update_comm h₁.symm]

theorem unrev_ok {q s} {S : K' → List Γ'} :
    Reaches₁ (TM2.step M) ⟨some (unrev q), s, S⟩
      ⟨some q, none, update (update S rev []) main (List.reverseAux (S rev) (S main))⟩ :=
  move_ok hM (by decide) <| splitAtPred_false _

theorem move₂_ok {p k₁ k₂ q s L₁ o L₂} {S : K' → List Γ'}
    (h₁ : k₁ ≠ rev ∧ k₂ ≠ rev ∧ k₁ ≠ k₂)
    (h₂ : S rev = []) (e : splitAtPred p (S k₁) = (L₁, o, L₂)) :
    Reaches₁ (TM2.step M) ⟨some (move₂ p k₁ k₂ q), s, S⟩
      ⟨some q, none,
        update (update S k₁ (o.elim id List.cons L₂)) k₂ (L₁ ++ S k₂)⟩ := by
  refine (move_ok hM h₁.1 e).trans (TransGen.head (step_of_tr hM (by trivial) rfl) ?_)
  simp only [TM2.step, Option.mem_def, Option.elim]
  cases o <;> simp only <;> rw [tr]
    <;> simp only [id, TM2.stepAux, Option.isSome, Bool.cond_true, Bool.cond_false]
  · convert! move_ok hM h₁.2.1.symm (splitAtPred_false _) using 2
    simp only [Function.update_comm h₁.1, Function.update_idem]
    rw [show update S rev [] = S by rw [← h₂, Function.update_eq_self]]
    simp only [Function.update_of_ne h₁.2.2.symm, Function.update_of_ne h₁.2.1,
      Function.update_of_ne h₁.1.symm, List.reverseAux_eq, h₂, Function.update_self,
      List.append_nil, List.reverse_reverse]
  · simp only [Option.getD_some]
    convert! move_ok hM h₁.2.1.symm (splitAtPred_false _) using 2
    simp only [h₂, Function.update_comm h₁.1, List.reverseAux_eq, Function.update_self,
      List.append_nil, Function.update_idem]
    rw [show update S rev [] = S by rw [← h₂, Function.update_eq_self]]
    simp only [Function.update_of_ne h₁.1.symm, Function.update_of_ne h₁.2.2.symm,
      Function.update_of_ne h₁.2.1, Function.update_self, List.reverse_reverse]

theorem clear_ok {p k q s L₁ o L₂} {S : K' → List Γ'}
    (e : splitAtPred p (S k) = (L₁, o, L₂)) :
    Reaches₁ (TM2.step M) ⟨some (Λ'.clear p k q), s, S⟩
      ⟨some q, o, update S k L₂⟩ := by
  induction L₁ generalizing S s with
  | nil =>
    refine TransGen.head' (step_of_tr hM (by trivial) rfl) ?_
    rw [tr]; simp only [pop', TM2.step, Option.mem_def, TM2.stepAux, Option.elim]
    revert e; rcases S k with - | ⟨a, Sk⟩ <;> intro e
    · cases e
      rfl
    simp only [splitAtPred, List.head?, List.tail_cons] at e ⊢
    revert e; cases p a <;> intro e <;>
      simp only [Bool.cond_false, Bool.cond_true, Prod.mk.injEq, true_and, false_and,
        reduceCtorEq] at e ⊢
    rcases e with ⟨e₁, e₂⟩
    rw [e₁, e₂]
  | cons a L₁ IH =>
    refine TransGen.head (step_of_tr hM (by trivial) rfl) ?_
    rw [tr]; simp only [pop', TM2.step, Option.mem_def, TM2.stepAux, Option.elim]
    rcases e₁ : S k with - | ⟨a', Sk⟩ <;> rw [e₁, splitAtPred] at e
    · cases e
    cases e₂ : p a' <;> simp only [e₂, cond] at e
    swap
    · cases e
    rcases e₃ : splitAtPred p Sk with ⟨_, _, _⟩
    rw [e₃] at e
    cases e
    simp only [List.head?_cons, e₂, List.tail_cons, Bool.cond_false]
    convert! @IH _ (update S k Sk) _ using 2 <;> simp [e₃]

set_option backward.isDefEq.respectTransparency false in
theorem copy_ok (q s a b c d) :
    Reaches₁ (TM2.step M) ⟨some (Λ'.copy q), s, K'.elim a b c d⟩
      ⟨some q, none, K'.elim (List.reverseAux b a) [] c (List.reverseAux b d)⟩ := by
  induction b generalizing a d s with
  | nil =>
    refine TransGen.single (step_of_tr hM (by trivial) ?_)
    simp
  | cons x b IH =>
    refine TransGen.head (step_of_tr hM (by trivial) rfl) ?_
    rw [tr]
    simp only [TM2.step, Option.mem_def, TM2.stepAux, elim_rev, List.head?_cons, Option.isSome_some,
      List.tail_cons, elim_update_rev, elim_main, elim_update_main,
      elim_stack, elim_update_stack, Bool.cond_true, List.reverseAux_cons, pop', push']
    exact IH _ _ _


theorem head_main_ok {q s L} {c d : List Γ'} :
    Reaches₁ (TM2.step M) ⟨some (head main q), s, K'.elim (trList L) [] c d⟩
      ⟨some q, none, K'.elim (trList [L.headI]) [] c d⟩ := by
  let o : Option Γ' := List.casesOn L none fun _ _ => some Γ'.cons
  refine
    (move_ok hM (by decide)
          (splitAtPred_eq _ _ (trNat L.headI) o (trList L.tail) (trNat_natEnd _) ?_)).trans
      (TransGen.head (step_of_tr hM (by trivial) rfl)
        (TransGen.head (step_of_tr hM (by trivial) rfl) ?_))
  · cases L <;> simp [o]
  rw [tr]
  simp only [TM2.step, Option.mem_def, TM2.stepAux, elim_update_main, elim_rev, elim_update_rev,
    Function.update_self, trList]
  rw [ite_eq_right (show o ≠ some Γ'.consₗ by cases L <;> simp [o])]
  refine (clear_ok hM (splitAtPred_eq _ _ _ none [] ?_ ⟨rfl, rfl⟩)).trans ?_
  · exact fun x h => Bool.decide_false (trList_ne_consₗ _ _ h)
  convert! unrev_ok hM using 2; simp [List.reverseAux_eq]

theorem head_stack_ok {q s L₁ L₂ L₃} :
    Reaches₁ (TM2.step M)
      ⟨some (head stack q), s, K'.elim (trList L₁) [] [] (trList L₂ ++ Γ'.consₗ :: L₃)⟩
      ⟨some q, none, K'.elim (trList (L₂.headI :: L₁)) [] [] L₃⟩ := by
  rcases L₂ with - | ⟨a, L₂⟩
  · refine
      TransGen.trans
        (move_ok hM (by decide)
          (splitAtPred_eq _ _ [] (some Γ'.consₗ) L₃ (by rintro _ ⟨⟩) ⟨rfl, rfl⟩))
        (TransGen.head (step_of_tr hM (by trivial) rfl)
          (TransGen.head (step_of_tr hM (by trivial) rfl) ?_))
    rw [tr]
    simp only [TM2.step, Option.mem_def, TM2.stepAux, ite_true, id_eq, trList, List.nil_append,
      elim_update_stack, elim_rev, List.reverseAux_nil, elim_update_rev, Function.update_self,
      List.headI_nil, trNat_default]
    convert! unrev_ok hM using 2
    simp
  · refine
      TransGen.trans
        (move_ok hM (by decide)
          (splitAtPred_eq _ _ (trNat a) (some Γ'.cons) (trList L₂ ++ Γ'.consₗ :: L₃)
            (trNat_natEnd _) ⟨rfl, by simp⟩))
        (TransGen.head (step_of_tr hM (by trivial) rfl)
          (TransGen.head (step_of_tr hM (by trivial) rfl) ?_))
    simp only [TM2.step, Option.mem_def, trList, List.append_assoc,
      List.cons_append, elim_update_stack, elim_rev, elim_update_rev, Function.update_self,
      List.headI_cons]
    refine
      TransGen.trans
        (clear_ok hM
          (splitAtPred_eq _ _ (trList L₂) (some Γ'.consₗ) L₃
            (fun x h => Bool.decide_false (trList_ne_consₗ _ _ h)) ⟨rfl, by simp⟩))
        ?_
    convert! unrev_ok hM using 2
    simp [List.reverseAux_eq]

set_option backward.isDefEq.respectTransparency false in
theorem succ_ok {q s n} {c d : List Γ'} :
    Reaches₁ (TM2.step M) ⟨some (Λ'.succ q), s, K'.elim (trList [n]) [] c d⟩
      ⟨some q, none, K'.elim (trList [n.succ]) [] c d⟩ := by
  simp only [trList, trNat.eq_1, Nat.cast_succ, Num.add_one]
  rcases (n : Num) with - | a
  · refine TransGen.head (step_of_tr hM (by trivial) rfl) ?_
    simp only [Option.mem_def]
    convert! unrev_ok hM using 1
    simp only [elim_update_rev, elim_rev, elim_main, List.reverseAux_nil, elim_update_main]
    rfl
  simp only [trNum, Num.succ, Num.succ']
  suffices ∀ l₁, ∃ l₁' l₂' s',
      List.reverseAux l₁ (trPosNum a.succ) = List.reverseAux l₁' l₂' ∧
        Reaches₁ (TM2.step M) ⟨some q.succ, s, K'.elim (trPosNum a ++ [Γ'.cons]) l₁ c d⟩
          ⟨some (unrev q), s', K'.elim (l₂' ++ [Γ'.cons]) l₁' c d⟩ by
    obtain ⟨l₁', l₂', s', e, h⟩ := this []
    simp only [List.reverseAux] at e
    refine h.trans ?_
    convert! unrev_ok hM using 2
    simp [e, List.reverseAux_eq]
  induction a generalizing s with intro l₁
  | one =>
    refine ⟨Γ'.bit0 :: l₁, [Γ'.bit1], some Γ'.cons, rfl,
      TransGen.head (step_of_tr hM (by trivial) rfl)
        (TransGen.single (step_of_tr hM (by trivial) ?_))⟩
    simp [trPosNum]
  | bit1 m IH =>
    obtain ⟨l₁', l₂', s', e, h⟩ := IH (Γ'.bit0 :: l₁)
    refine ⟨l₁', l₂', s', e, TransGen.head (step_of_tr hM (by trivial) ?_) h⟩
    simp [trPosNum]
    rfl
  | bit0 m _ =>
    refine ⟨l₁, _, some Γ'.bit0, rfl, TransGen.single (step_of_tr hM (by trivial) ?_)⟩
    simp only [TM2.step]; rw [tr]
    simp only [TM2.stepAux, pop', elim_main, elim_update_main,
      elim_rev, elim_update_rev, Function.update_self, Option.mem_def, Option.some.injEq]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem pred_ok (q₁ q₂ s v) (c d : List Γ') : ∃ s',
    Reaches₁ (TM2.step M) ⟨some (Λ'.pred q₁ q₂), s, K'.elim (trList v) [] c d⟩
      (v.headI.rec ⟨some q₁, s', K'.elim (trList v.tail) [] c d⟩ fun n _ =>
        ⟨some q₂, s', K'.elim (trList (n::v.tail)) [] c d⟩) := by
  rcases v with (_ | ⟨_ | n, v⟩)
  · refine ⟨none, TransGen.single (step_of_tr hM (by trivial) ?_)⟩
    simp
  · refine ⟨some Γ'.cons, TransGen.single (step_of_tr hM (by trivial) ?_)⟩
    simp
  refine ⟨none, ?_⟩
  simp only [trList, trNat.eq_1, trNum, Nat.cast_succ, Num.add_one, Num.succ,
    List.tail_cons, List.headI_cons]
  rcases (n : Num) with - | a
  · simp only [trPosNum, Num.succ', List.singleton_append, List.nil_append]
    refine TransGen.head (step_of_tr hM (by trivial) rfl) ?_
    rw [tr]; simp only [pop', TM2.stepAux]
    convert! unrev_ok hM using 2
    simp
  simp only [Num.succ']
  suffices ∀ l₁, ∃ l₁' l₂' s',
    List.reverseAux l₁ (trPosNum a) = List.reverseAux l₁' l₂' ∧
      Reaches₁ (TM2.step M)
        ⟨some (q₁.pred q₂), s, K'.elim (trPosNum a.succ ++ Γ'.cons :: trList v) l₁ c d⟩
        ⟨some (unrev q₂), s', K'.elim (l₂' ++ Γ'.cons :: trList v) l₁' c d⟩ by
    obtain ⟨l₁', l₂', s', e, h⟩ := this []
    simp only [List.reverseAux] at e
    refine h.trans ?_
    convert! unrev_ok hM using 2
    simp [e, List.reverseAux_eq]
  induction a generalizing s with intro l₁
  | one =>
    refine ⟨Γ'.bit1::l₁, [], some Γ'.cons, rfl,
      TransGen.head (step_of_tr hM (by trivial) rfl)
        (TransGen.single (step_of_tr hM (by trivial) ?_))⟩
    simp [trPosNum, show PosNum.one.succ = PosNum.one.bit0 from rfl]
  | bit1 m IH =>
    obtain ⟨l₁', l₂', s', e, h⟩ := IH (some Γ'.bit0) (Γ'.bit1 :: l₁)
    refine ⟨l₁', l₂', s', e, TransGen.head (step_of_tr hM (by trivial) ?_) h⟩
    simp
    rfl
  | bit0 m IH =>
    obtain ⟨a, l, e, h⟩ : ∃ a l, (trPosNum m = a::l) ∧ natEnd a = false := by
      cases m <;> refine ⟨_, _, rfl, rfl⟩
    refine ⟨Γ'.bit0 :: l₁, _, some a, rfl, TransGen.single (step_of_tr hM (by trivial) ?_)⟩
    simp [trPosNum, PosNum.succ, e, h, show some Γ'.bit1 ≠ some Γ'.bit0 by decide,
      show natEnd Γ'.bit1 = false from rfl, Option.getD, -natEnd]


/-- Push one constant symbol, preserving the local store and all other stacks. -/
theorem push_ok (k : K') (value : Γ') (q : Λ') (s : Option Γ') (S : K' → List Γ') :
    Reaches₁ (TM2.step M) ⟨some (.push k (fun _ ↦ some value) q), s, S⟩
      ⟨some q, s, update S k (value :: S k)⟩ := by
  refine TransGen.single (step_of_tr hM (by trivial) ?_)
  simp [TM2.step, tr, TM2.stepAux]

/-- Arbitrary-stack form of Mathlib's reverse-copy operation. -/
theorem copy_all_ok (q : Λ') (s : Option Γ') (S : K' → List Γ') :
    Reaches₁ (TM2.step M) ⟨some (.copy q), s, S⟩
      ⟨some q, none,
        update (update (update S rev []) main (List.reverseAux (S rev) (S main)))
          stack (List.reverseAux (S rev) (S stack))⟩ := by
  convert! copy_ok hM q s (S main) (S rev) (S aux) (S stack) using 2
  · funext k
    cases k <;> rfl
  · funext k
    cases k <;> simp

/-- Move one delimited binary natural, consuming its source delimiter and preserving its bits. -/
def moveWord (src dst : K') (q : Λ') : Λ' :=
  .move natEnd src rev (.push dst (fun _ ↦ some .cons) (.move (fun _ ↦ false) rev dst q))

theorem moveWord_ok (src dst : K') (q : Λ') (s : Option Γ') (S : K' → List Γ')
    (n : Nat) (suffix : List Γ') (hsrc : src ≠ rev) (hdst : dst ≠ rev) (hne : src ≠ dst)
    (hrev : S rev = []) (hword : S src = trNat n ++ Γ'.cons :: suffix) :
    Reaches₁ (TM2.step M) ⟨some (moveWord src dst q), s, S⟩
      ⟨some q, none, update (update S src suffix) dst (trList [n] ++ S dst)⟩ := by
  have split : splitAtPred natEnd (S src) = (trNat n, some Γ'.cons, suffix) := by
    rw [hword]
    exact splitAtPred_eq _ _ _ _ _ (trNat_natEnd n) ⟨rfl, rfl⟩
  let A := update (update S src suffix) rev ((trNat n).reverseAux (S rev))
  let B := update A dst (Γ'.cons :: A dst)
  have hm : Reaches₁ (TM2.step M) ⟨some (moveWord src dst q), s, S⟩
      ⟨some (.push dst (fun _ ↦ some Γ'.cons) (.move (fun _ ↦ false) rev dst q)),
        some Γ'.cons, A⟩ := move_ok hM hsrc split
  refine hm.trans ((push_ok hM dst Γ'.cons _ (some Γ'.cons) A).trans ?_)
  convert! move_ok hM hdst.symm (splitAtPred_false (B rev)) using 2
  funext k
  cases src <;> cases dst <;> cases k <;>
    simp_all [A, B, List.reverseAux_eq, trList, List.append_assoc]

/-- Remove one source word and copy it to both value stacks; the source may be either target. -/
def copyWord (src : K') (q : Λ') : Λ' :=
  .move natEnd src rev (.push main (fun _ ↦ some .cons)
    (.push stack (fun _ ↦ some .cons) (.copy q)))

theorem copyWord_ok (src : K') (q : Λ') (s : Option Γ') (S : K' → List Γ')
    (n : Nat) (suffix : List Γ') (hsrc : src ≠ rev) (hrev : S rev = [])
    (hword : S src = trNat n ++ Γ'.cons :: suffix) :
    Reaches₁ (TM2.step M) ⟨some (copyWord src q), s, S⟩
      ⟨some q, none,
        update (update (update S src suffix) main
          (trList [n] ++ (update S src suffix) main)) stack
          (trList [n] ++ (update S src suffix) stack)⟩ := by
  have split : splitAtPred natEnd (S src) = (trNat n, some Γ'.cons, suffix) := by
    rw [hword]
    exact splitAtPred_eq _ _ _ _ _ (trNat_natEnd n) ⟨rfl, rfl⟩
  let A := update (update S src suffix) rev ((trNat n).reverseAux (S rev))
  let B := update A main (Γ'.cons :: A main)
  let C := update B stack (Γ'.cons :: B stack)
  have hm : Reaches₁ (TM2.step M) ⟨some (copyWord src q), s, S⟩
      ⟨some (.push main (fun _ ↦ some Γ'.cons)
        (.push stack (fun _ ↦ some Γ'.cons) (.copy q))), some Γ'.cons, A⟩ :=
    move_ok hM hsrc split
  refine hm.trans ((push_ok hM main Γ'.cons _ (some Γ'.cons) A).trans
    ((push_ok hM stack Γ'.cons _ (some Γ'.cons) B).trans ?_))
  convert! copy_all_ok hM q (some Γ'.cons) C using 2
  funext k
  cases src <;> cases k <;>
    simp_all [A, B, C, List.reverseAux_eq, trList, List.append_assoc]

/-- Preserve all of `main` while prefixing an identical copy to `stack`. -/
def copyValues (q : Λ') : Λ' := .move (fun _ ↦ false) main rev (.copy q)

theorem copyValues_ok (q : Λ') (s : Option Γ') (S : K' → List Γ') (hrev : S rev = []) :
    Reaches₁ (TM2.step M) ⟨some (copyValues q), s, S⟩
      ⟨some q, none, update S stack (S main ++ S stack)⟩ := by
  let A := update (update S main []) rev ((S main).reverseAux (S rev))
  have hm : Reaches₁ (TM2.step M) ⟨some (copyValues q), s, S⟩
      ⟨some (.copy q), none, A⟩ := move_ok hM (by decide) (splitAtPred_false _)
  refine hm.trans ?_
  convert! copy_all_ok hM q none A using 2
  funext k
  cases k <;> simp [A, hrev, List.reverseAux_eq]

end ConjectureMachines.Compilation.RuntimeMacros
