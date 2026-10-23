/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.RuntimeData

/-! # Raw opcode boundaries of the fixed four-stack interpreter

Each proof starts at an opcode phase, consumes its two child words, and stops at the next
evaluation or return phase. The program table and arbitrary older frame symbols are preserved.
-/

@[expose] public section
namespace ConjectureMachines.Compilation.Runtime
open Turing PartrecToTM2 K' StateTransition Relation Function

set_option backward.isDefEq.respectTransparency false

private abbrev raw (q : Λ') (s : Option Γ') (a c d : List Γ') : Cfg' :=
  ⟨some q, s, K'.elim a [] c d⟩

private theorem discard_word (src : K') (q : Λ') (s : Option Γ')
    (S : K' → List Γ') (n : Nat) (suffix : List Γ')
    (word : S src = trNat n ++ Γ'.cons :: suffix) :
    Reaches₁ (TM2.step machine) ⟨some (discardWord src q), s, S⟩
      ⟨some q, some Γ'.cons, update S src suffix⟩ := by
  apply RuntimeMacros.clear_ok agrees
  exact splitAtPred_eq natEnd _ (trNat n) (some Γ'.cons) suffix (trNat_natEnd n)
    ⟨rfl, word⟩

private theorem discard_stack (n : Nat) (q : Λ') (s : Option Γ') (a c d : List Γ') :
    Reaches₁ (TM2.step machine)
      (raw (discardWord stack q) s a c (trList [n] ++ d))
      (raw q (some Γ'.cons) a c d) := by
  simpa only [raw, elim_stack, elim_update_stack] using
    discard_word stack q s (K'.elim a [] c (trList [n] ++ d)) n d
      (by simp [trList])

private theorem move_stack_aux (n : Nat) (q : Λ') (s : Option Γ') (a c d : List Γ') :
    Reaches₁ (TM2.step machine)
      (raw (moveWord stack aux q) s a c (trList [n] ++ d))
      (raw q none a (trList [n] ++ c) d) := by
  simpa only [raw, elim_stack, elim_aux, elim_update_stack, elim_update_aux] using
    moveWord_reaches stack aux q s (K'.elim a [] c (trList [n] ++ d)) n d
      (by decide) (by decide) (by decide) rfl (by simp [trList])

private theorem move_stack_main (n : Nat) (q : Λ') (s : Option Γ') (a c d : List Γ') :
    Reaches₁ (TM2.step machine)
      (raw (moveWord stack main q) s a c (trList [n] ++ d))
      (raw q none (trList [n] ++ a) c d) := by
  simpa only [raw, elim_stack, elim_main, elim_update_stack, elim_update_main] using
    moveWord_reaches stack main q s (K'.elim a [] c (trList [n] ++ d)) n d
      (by decide) (by decide) (by decide) rfl (by simp [trList])

private theorem move_aux_main (n : Nat) (q : Λ') (s : Option Γ') (a c d : List Γ') :
    Reaches₁ (TM2.step machine)
      (raw (moveWord aux main q) s a (trList [n] ++ c) d)
      (raw q none (trList [n] ++ a) c d) := by
  simpa only [raw, elim_aux, elim_main, elim_update_aux, elim_update_main] using
    moveWord_reaches aux main q s (K'.elim a [] (trList [n] ++ c) d) n c
      (by decide) (by decide) (by decide) rfl (by simp [trList])

private theorem move_aux_stack (n : Nat) (q : Λ') (s : Option Γ') (a c d : List Γ') :
    Reaches₁ (TM2.step machine)
      (raw (moveWord aux stack q) s a (trList [n] ++ c) d)
      (raw q none a c (trList [n] ++ d)) := by
  simpa only [raw, elim_aux, elim_stack, elim_update_aux, elim_update_stack] using
    moveWord_reaches aux stack q s (K'.elim a [] (trList [n] ++ c) d) n c
      (by decide) (by decide) (by decide) rfl (by simp [trList])

private theorem copy_aux (n : Nat) (q : Λ') (s : Option Γ') (a c d : List Γ') :
    Reaches₁ (TM2.step machine)
      (raw (copyWord aux q) s a (trList [n] ++ c) d)
      (raw q none (trList [n] ++ a) c (trList [n] ++ d)) := by
  simpa only [raw, elim_aux, elim_main, elim_stack, elim_update_aux,
    elim_update_main, elim_update_stack] using
    copyWord_reaches aux q s (K'.elim a [] (trList [n] ++ c) d) n c
      (by decide) rfl (by simp [trList])

private theorem push_main (n : Nat) (q : Λ') (s : Option Γ') (a c d : List Γ') :
    Reaches (TM2.step machine) (raw (pushWord main n q) s a c d)
      (raw q s (trList [n] ++ a) c d) := by
  simpa only [raw, elim_main, elim_update_main] using
    pushWord_reaches main n q s (K'.elim a [] c d)

private theorem push_stack (n : Nat) (q : Λ') (s : Option Γ') (a c d : List Γ') :
    Reaches (TM2.step machine) (raw (pushWord stack n q) s a c d)
      (raw q s a c (trList [n] ++ d)) := by
  simpa only [raw, elim_stack, elim_update_stack] using
    pushWord_reaches stack n q s (K'.elim a [] c d)

private theorem copy_values (q : Λ') (s : Option Γ') (a c d : List Γ') :
    Reaches₁ (TM2.step machine) (raw (copyValues q) s a c d)
      (raw q none a c (a ++ d)) := by
  simpa only [raw, copyValues, RuntimeMacros.copyValues, elim_rev, elim_main,
    elim_stack, elim_update_stack] using
    RuntimeMacros.copyValues_ok agrees q s (K'.elim a [] c d) rfl

private theorem push_frame (q : Λ') (s : Option Γ') (a c d : List Γ') :
    Reaches₁ (TM2.step machine)
      (raw (.push stack (fun _ => some Γ'.consₗ) q) s a c d)
      (raw q s a c (Γ'.consₗ :: d)) := by
  simpa only [raw, elim_stack, elim_update_stack] using
    RuntimeMacros.push_ok agrees stack Γ'.consₗ q s (K'.elim a [] c d)

/-- The zero opcode ignores both child words and prepends zero to the complete value list. -/
theorem zero_reaches (s : Option Γ') (v table : List Nat) (left right : Nat)
    (frames : List Γ') :
    ∃ outStore, Reaches₁ (TM2.step machine)
      (dataCfg .zero s v table (trList [left, right] ++ frames))
      (dataCfg .returned outStore (0 :: v) table frames) := by
  refine ⟨some Γ'.cons, ?_⟩
  have start := phase_reaches .zero s
    (K'.elim (trList v) [] (trList table) (trList [left, right] ++ frames)) (by decide)
  simp only [entry, trList, List.append_assoc, List.nil_append, List.cons_append] at start
  have first := discard_stack left
    (discardWord stack (pushWord main 0 (label .returned))) s
    (trList v) (trList table) (trList [right] ++ frames)
  have second := discard_stack right (pushWord main 0 (label .returned)) (some Γ'.cons)
    (trList v) (trList table) frames
  have finish := push_main 0 (label .returned) (some Γ'.cons)
    (trList v) (trList table) frames
  simp only [raw, trList, List.append_assoc, List.nil_append, List.cons_append] at first second
  simpa only [StateTransition.Reaches₁, dataCfg, raw, trList, List.append_assoc, List.nil_append,
    List.cons_append] using start.trans (first.trans second) |>.trans_left finish

/-- Successor first keeps exactly the defaulted head, including on the empty value list. -/
theorem successor_reaches (s : Option Γ') (v table : List Nat) (left right : Nat)
    (frames : List Γ') :
    ∃ outStore, Reaches₁ (TM2.step machine)
      (dataCfg .successor s v table (trList [left, right] ++ frames))
      (dataCfg .returned outStore [v.headI + 1] table frames) := by
  refine ⟨none, ?_⟩
  have start := phase_reaches .successor s
    (K'.elim (trList v) [] (trList table) (trList [left, right] ++ frames)) (by decide)
  simp only [entry, trList, List.append_assoc, List.nil_append, List.cons_append] at start
  have first := discard_stack left
    (discardWord stack (head main (.succ (label .returned)))) s
    (trList v) (trList table) (trList [right] ++ frames)
  have second := discard_stack right (head main (.succ (label .returned))) (some Γ'.cons)
    (trList v) (trList table) frames
  have keep := RuntimeMacros.head_main_ok agrees (q := .succ (label .returned))
    (s := some Γ'.cons) (L := v) (c := trList table) (d := frames)
  have finish := RuntimeMacros.succ_ok agrees (q := label .returned) (s := none)
    (n := v.headI) (c := trList table) (d := frames)
  simp only [raw, trList, List.append_assoc, List.nil_append, List.cons_append] at first second
  simpa only [StateTransition.Reaches₁, dataCfg, raw, trList, List.append_assoc, List.nil_append,
    List.cons_append] using start.trans (first.trans (second.trans (keep.trans finish)))

/-- Tail also accepts empty values; only the first complete natural word is discarded. -/
theorem tail_reaches (s : Option Γ') (v table : List Nat) (left right : Nat)
    (frames : List Γ') :
    ∃ outStore, Reaches₁ (TM2.step machine)
      (dataCfg .tail s v table (trList [left, right] ++ frames))
      (dataCfg .returned outStore v.tail table frames) := by
  have start := phase_reaches .tail s
    (K'.elim (trList v) [] (trList table) (trList [left, right] ++ frames)) (by decide)
  simp only [entry, trList, List.append_assoc, List.nil_append, List.cons_append] at start
  have first := discard_stack left
    (discardWord stack (discardWord main (label .returned))) s
    (trList v) (trList table) (trList [right] ++ frames)
  have second := discard_stack right (discardWord main (label .returned)) (some Γ'.cons)
    (trList v) (trList table) frames
  simp only [raw, trList, List.append_assoc, List.nil_append, List.cons_append] at first second
  have begin : Reaches₁ (TM2.step machine)
      (dataCfg .tail s v table (trList [left, right] ++ frames))
      (raw (discardWord main (label .returned)) (some Γ'.cons)
        (trList v) (trList table) frames) := by
    simpa only [StateTransition.Reaches₁, dataCfg, raw, entry, trList, List.append_assoc,
      List.nil_append, List.cons_append] using start.trans (first.trans second)
  cases v with
  | nil =>
    refine ⟨none, begin.trans ?_⟩
    simpa only [dataCfg, raw, discardWord, trList, List.tail_nil, elim_update_main,
      StateTransition.Reaches₁] using
      RuntimeMacros.clear_ok agrees (k := main) (q := label .returned)
        (s := some Γ'.cons) (S := K'.elim [] [] (trList table) frames)
        (show splitAtPred natEnd [] = ([], none, []) from rfl)
  | cons n rest =>
    refine ⟨some Γ'.cons, begin.trans ?_⟩
    simpa only [dataCfg, raw, trList, List.tail_cons, elim_update_main,
      StateTransition.Reaches₁] using
      discard_word main (label .returned) (some Γ'.cons)
        (K'.elim (trList (n :: rest)) [] (trList table) frames) n (trList rest) rfl

/-- Cons saves the input values behind a frame delimiter and evaluates its left child. -/
theorem cons_reaches (s : Option Γ') (v table : List Nat) (left right : Nat)
    (frames : List Γ') :
    ∃ outStore, Reaches₁ (TM2.step machine)
      (dataCfg .cons s v table (trList [left, right] ++ frames))
      (dataCfg .evaluate outStore (left :: v) table
        (trList [1] ++ trList v ++ Γ'.consₗ :: (trList [right] ++ frames))) := by
  refine ⟨none, ?_⟩
  have start := phase_reaches .cons s
    (K'.elim (trList v) [] (trList table) (trList [left, right] ++ frames)) (by decide)
  have moved := move_stack_aux left
    (.push stack (fun _ => some Γ'.consₗ)
      (copyValues (pushWord stack 1 (moveWord aux main (label .evaluate))))) s
    (trList v) (trList table) (trList [right] ++ frames)
  have marked := push_frame
    (copyValues (pushWord stack 1 (moveWord aux main (label .evaluate)))) none
    (trList v) (trList [left] ++ trList table) (trList [right] ++ frames)
  have copied := copy_values (pushWord stack 1 (moveWord aux main (label .evaluate))) none
    (trList v) (trList [left] ++ trList table) (Γ'.consₗ :: (trList [right] ++ frames))
  have tagged := push_stack 1 (moveWord aux main (label .evaluate)) none
    (trList v) (trList [left] ++ trList table)
    (trList v ++ Γ'.consₗ :: (trList [right] ++ frames))
  have finish := move_aux_main left (label .evaluate) none (trList v) (trList table)
    (trList [1] ++ (trList v ++ Γ'.consₗ :: (trList [right] ++ frames)))
  simp only [entry, raw, trList, List.append_assoc, List.nil_append, List.cons_append]
    at start moved marked copied tagged finish
  simpa only [StateTransition.Reaches₁, dataCfg, trList, List.append_assoc,
    List.nil_append, List.cons_append] using
    (start.trans (moved.trans (marked.trans copied))).trans_left tagged |>.trans finish

/-- Composition saves its left child and evaluates its right child on the original values. -/
theorem comp_reaches (s : Option Γ') (v table : List Nat) (left right : Nat)
    (frames : List Γ') :
    ∃ outStore, Reaches₁ (TM2.step machine)
      (dataCfg .comp s v table (trList [left, right] ++ frames))
      (dataCfg .evaluate outStore (right :: v) table (trList [3, left] ++ frames)) := by
  refine ⟨none, ?_⟩
  have start := phase_reaches .comp s
    (K'.elim (trList v) [] (trList table) (trList [left, right] ++ frames)) (by decide)
  have moved := move_stack_aux left
    (moveWord stack main (moveWord aux stack (pushWord stack 3 (label .evaluate)))) s
    (trList v) (trList table) (trList [right] ++ frames)
  have child := move_stack_main right
    (moveWord aux stack (pushWord stack 3 (label .evaluate))) none
    (trList v) (trList [left] ++ trList table) frames
  have saved := move_aux_stack left (pushWord stack 3 (label .evaluate)) none
    (trList [right] ++ trList v) (trList table) frames
  have tagged := push_stack 3 (label .evaluate) none
    (trList [right] ++ trList v) (trList table) (trList [left] ++ frames)
  simp only [entry, raw, trList, List.append_assoc, List.nil_append, List.cons_append]
    at start moved child saved tagged
  simpa only [StateTransition.Reaches₁, dataCfg, trList, List.append_assoc,
    List.nil_append, List.cons_append] using
    start.trans (moved.trans (child.trans saved)) |>.trans_left tagged

/-- Branch uses the defaulted head, consumes zero, and decrements a positive head. -/
theorem branch_reaches (s : Option Γ') (v table : List Nat) (left right : Nat)
    (frames : List Γ') :
    ∃ outStore, Reaches₁ (TM2.step machine)
      (dataCfg .branch s v table (trList [left, right] ++ frames))
      (dataCfg .evaluate outStore
        (if v.headI = 0 then left :: v.tail else right :: (v.headI - 1) :: v.tail)
        table frames) := by
  have start := phase_reaches .branch s
    (K'.elim (trList v) [] (trList table) (trList [left, right] ++ frames)) (by decide)
  obtain ⟨middle, tested⟩ := RuntimeMacros.pred_ok agrees
    (moveWord stack aux (discardWord stack (moveWord aux main (label .evaluate))))
    (discardWord stack (moveWord stack main (label .evaluate))) s v
    (trList table) (trList [left, right] ++ frames)
  cases head : v.headI with
  | zero =>
    refine ⟨none, ?_⟩
    simp only [head, Nat.rec_zero] at tested
    have moved := move_stack_aux left
      (discardWord stack (moveWord aux main (label .evaluate))) middle
      (trList v.tail) (trList table) (trList [right] ++ frames)
    have discarded := discard_stack right (moveWord aux main (label .evaluate)) none
      (trList v.tail) (trList [left] ++ trList table) frames
    have finish := move_aux_main left (label .evaluate) (some Γ'.cons)
      (trList v.tail) (trList table) frames
    simp only [entry, raw, trList, List.append_assoc, List.nil_append, List.cons_append]
      at start tested moved discarded finish
    simpa only [StateTransition.Reaches₁, dataCfg, head, ite_true, trList,
      List.append_assoc, List.nil_append, List.cons_append] using
      start.trans (tested.trans (moved.trans (discarded.trans finish)))
  | succ n =>
    refine ⟨none, ?_⟩
    simp only [head] at tested
    have discarded := discard_stack left (moveWord stack main (label .evaluate)) middle
      (trList (n :: v.tail)) (trList table) (trList [right] ++ frames)
    have finish := move_stack_main right (label .evaluate) (some Γ'.cons)
      (trList (n :: v.tail)) (trList table) frames
    simp only [entry, raw, trList, List.append_assoc, List.nil_append, List.cons_append]
      at start tested discarded finish
    simpa only [StateTransition.Reaches₁, dataCfg, head, Nat.succ_ne_zero, ite_false,
      Nat.add_one_sub_one, Nat.succ_eq_add_one, trList, List.append_assoc,
      List.nil_append, List.cons_append] using
      start.trans (tested.trans (discarded.trans finish))

theorem branch_zero_reaches (s : Option Γ') (v table : List Nat) (left right : Nat)
    (frames : List Γ') (zero : v.headI = 0) :
    ∃ outStore, Reaches₁ (TM2.step machine)
      (dataCfg .branch s v table (trList [left, right] ++ frames))
      (dataCfg .evaluate outStore (left :: v.tail) table frames) := by
  simpa only [zero, ite_true] using branch_reaches s v table left right frames

theorem branch_succ_reaches (s : Option Γ') (v table : List Nat) (left right : Nat)
    (frames : List Γ') (positive : v.headI ≠ 0) :
    ∃ outStore, Reaches₁ (TM2.step machine)
      (dataCfg .branch s v table (trList [left, right] ++ frames))
      (dataCfg .evaluate outStore (right :: (v.headI - 1) :: v.tail) table frames) := by
  simpa only [positive, ite_false] using branch_reaches s v table left right frames

/-- Fix saves the same left child that it evaluates; the unused right child is removed. -/
theorem fix_reaches (s : Option Γ') (v table : List Nat) (left right : Nat)
    (frames : List Γ') :
    ∃ outStore, Reaches₁ (TM2.step machine)
      (dataCfg .fix s v table (trList [left, right] ++ frames))
      (dataCfg .evaluate outStore (left :: v) table (trList [4, left] ++ frames)) := by
  refine ⟨none, ?_⟩
  have start := phase_reaches .fix s
    (K'.elim (trList v) [] (trList table) (trList [left, right] ++ frames)) (by decide)
  have moved := move_stack_aux left
    (discardWord stack (copyWord aux (pushWord stack 4 (label .evaluate)))) s
    (trList v) (trList table) (trList [right] ++ frames)
  have discarded := discard_stack right
    (copyWord aux (pushWord stack 4 (label .evaluate))) none
    (trList v) (trList [left] ++ trList table) frames
  have copied := copy_aux left (pushWord stack 4 (label .evaluate)) (some Γ'.cons)
    (trList v) (trList table) frames
  have tagged := push_stack 4 (label .evaluate) none
    (trList [left] ++ trList v) (trList table) (trList [left] ++ frames)
  simp only [entry, raw, trList, List.append_assoc, List.nil_append, List.cons_append]
    at start moved discarded copied tagged
  simpa only [StateTransition.Reaches₁, dataCfg, trList, List.append_assoc,
    List.nil_append, List.cons_append] using
    start.trans (moved.trans (discarded.trans copied)) |>.trans_left tagged

end ConjectureMachines.Compilation.Runtime
