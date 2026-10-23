/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.RuntimeData
public import Cryptids.Compilation.CodeDAG

/-! # Indexed instruction lookup with full table restoration -/

@[expose] public section
namespace ConjectureMachines.Compilation.RuntimeLookup
open Turing PartrecToTM2 K' Relation StateTransition Function
open ConjectureMachines.Compilation.Runtime

set_option backward.isDefEq.respectTransparency false

/-- A raw macro boundary, with no restriction on the older frame symbols. -/
def cfg (pc : Λ') (store : Option Γ') (values table : List Nat) (frames : List Γ') : Cfg' :=
  ⟨some pc, store, K'.elim (trList values) [] (trList table) frames⟩

theorem move_aux_stack (next : Λ') (store : Option Γ') (values table : List Nat)
    (n : Nat) (frames : List Γ') :
    Reaches₁ (TM2.step machine) (cfg (moveWord aux stack next) store values (n :: table) frames)
      (cfg next none values table (trList [n] ++ frames)) := by
  simpa [cfg, trList, List.append_assoc] using
    moveWord_reaches aux stack next store (K'.elim (trList values) [] (trList (n :: table)) frames)
      n (trList table) (by decide) (by decide) (by decide) rfl rfl

theorem move_main_stack (next : Λ') (store : Option Γ') (values table : List Nat)
    (n : Nat) (frames : List Γ') :
    Reaches₁ (TM2.step machine) (cfg (moveWord main stack next) store (n :: values) table frames)
      (cfg next none values table (trList [n] ++ frames)) := by
  simpa [cfg, trList, List.append_assoc] using
    moveWord_reaches main stack next store (K'.elim (trList (n :: values)) [] (trList table) frames)
      n (trList values) (by decide) (by decide) (by decide) rfl rfl

theorem move_stack_aux (next : Λ') (store : Option Γ') (values table : List Nat)
    (n : Nat) (frames : List Γ') :
    Reaches₁ (TM2.step machine)
      (cfg (moveWord stack aux next) store values table (trList [n] ++ frames))
      (cfg next none values (n :: table) frames) := by
  simpa [cfg, trList, List.append_assoc] using
    moveWord_reaches stack aux next store
      (K'.elim (trList values) [] (trList table) (trList [n] ++ frames))
      n frames (by decide) (by decide) (by decide) rfl
      (by simp [trList, List.append_assoc])

theorem copy_aux (next : Λ') (store : Option Γ') (values table : List Nat)
    (n : Nat) (frames : List Γ') :
    Reaches₁ (TM2.step machine) (cfg (copyWord aux next) store values (n :: table) frames)
      (cfg next none (n :: values) table (trList [n] ++ frames)) := by
  simpa [cfg, trList, List.append_assoc] using
    copyWord_reaches aux next store (K'.elim (trList values) [] (trList (n :: table)) frames)
      n (trList table) (by decide) rfl rfl

/-- Restoration inspects exactly one stack symbol, leaving the older suffix untouched. -/
theorem restore_probe (store : Option Γ') (values table : List Nat)
    (symbol : Γ') (frames : List Γ') :
    Reaches₁ (TM2.step machine) (cfg (label .restore) store values table (symbol :: frames))
      (cfg (if symbol = .consₗ then moveWord main stack (moveWord main stack (label .dispatch))
        else .push stack id (moveWord stack aux (label .restore)))
        (some symbol) values table frames) := by
  let next : Option Γ' → Λ' := fun current ↦
    if current = some .consₗ then moveWord main stack (moveWord main stack (label .dispatch))
    else .push stack id (moveWord stack aux (label .restore))
  have moved : Reaches₁ (TM2.step machine)
      (cfg (.move (fun _ ↦ true) stack rev (.read next)) store values table (symbol :: frames))
      (cfg (.read next) (some symbol) values table frames) := by
    simpa [cfg] using RuntimeMacros.move_ok agrees (q := .read next)
      (s := store) (S := K'.elim (trList values) [] (trList table) (symbol :: frames))
      (k₁ := stack) (k₂ := rev) (p := fun _ ↦ true) (L₁ := []) (o := some symbol)
      (L₂ := frames) (by decide) rfl
  have read : Reaches₁ (TM2.step machine)
      (cfg (.read next) (some symbol) values table frames)
      (cfg (next (some symbol)) (some symbol) values table frames) :=
    .single (RuntimeMacros.step_of_tr agrees (by trivial) rfl)
  simpa only [StateTransition.Reaches₁, cfg, entry, next, Option.some.injEq] using
    (phase_reaches .restore store (K'.elim (trList values) [] (trList table) (symbol :: frames))
      (by decide)).trans (moved.trans read)

/-- The fresh marker ends restoration and saves the two operands above the older frames. -/
theorem restore_marker (store : Option Γ') (values table : List Nat)
    (tag left right : Nat) (frames : List Γ') :
    Reaches₁ (TM2.step machine)
      (cfg (label .restore) store (right :: left :: tag :: values) table (.consₗ :: frames))
      (cfg (label .dispatch) none (tag :: values) table (trList [left, right] ++ frames)) := by
  have probe := restore_probe store (right :: left :: tag :: values) table .consₗ frames
  simp only [↓reduceIte] at probe
  simpa only [StateTransition.Reaches₁, trList, List.append_assoc, List.cons_append,
    List.nil_append] using
    probe.trans ((move_main_stack (moveWord main stack (label .dispatch)) (some .consₗ)
      (left :: tag :: values) table right frames).trans
      (move_main_stack (label .dispatch) none (tag :: values) table left
        (trList [right] ++ frames)))

/-- One ordinary encoded word is returned to the front of the table. -/
theorem restore_word (store : Option Γ') (values table : List Nat)
    (n : Nat) (frames : List Γ') :
    Reaches₁ (TM2.step machine)
      (cfg (label .restore) store values table (trList [n] ++ frames))
      (cfg (label .restore) none values (n :: table) frames) := by
  have nonempty : trList [n] ≠ [] := by simp [trList]
  obtain ⟨symbol, rest, encoded⟩ := List.exists_cons_of_ne_nil nonempty
  have ordinary : symbol ≠ Γ'.consₗ := trList_ne_consₗ [n] symbol
    (by rw [encoded]; exact List.mem_cons_self)
  have probe := restore_probe store values table symbol (rest ++ frames)
  simp only [ordinary, ↓reduceIte] at probe
  have pushed : Reaches₁ (TM2.step machine)
      (cfg (.push stack id (moveWord stack aux (label .restore))) (some symbol)
        values table (rest ++ frames))
      (cfg (moveWord stack aux (label .restore)) (some symbol)
        values table (trList [n] ++ frames)) := by
    rw [encoded]
    apply TransGen.single
    simp [cfg, TM2.step, machine, tr, TM2.stepAux]
  simpa only [StateTransition.Reaches₁, encoded, List.cons_append] using
    probe.trans (pushed.trans (move_stack_aux (label .restore) (some symbol) values table n frames))

/-- Every copied or skipped word is restored, stopping at the fresh marker. -/
theorem restore_prefix (prefixWords : List Nat) (store : Option Γ') (values table : List Nat)
    (tag left right : Nat) (frames : List Γ') :
    Reaches₁ (TM2.step machine)
      (cfg (label .restore) store (right :: left :: tag :: values) table
        (trList prefixWords ++ .consₗ :: frames))
      (cfg (label .dispatch) none (tag :: values) (prefixWords.reverse ++ table)
        (trList [left, right] ++ frames)) := by
  induction prefixWords generalizing store table with
  | nil => simpa only [trList, List.nil_append, List.reverse_nil] using
      restore_marker store values table tag left right frames
  | cons n rest ih =>
    simpa only [StateTransition.Reaches₁, trList, List.nil_append, List.cons_append,
      List.reverse_cons, List.append_assoc, List.singleton_append] using
      (restore_word store (right :: left :: tag :: values) table n
        (trList rest ++ .consₗ :: frames)).trans (ih none (n :: table))

/-- The actual readRow body copies all three instruction words to values and restoration data. -/
theorem read_row (store : Option Γ') (values table : List Nat)
    (tag left right : Nat) (frames : List Γ') :
    Reaches₁ (TM2.step machine)
      (cfg (label .readRow) store values (tag :: left :: right :: table) frames)
      (cfg (label .restore) none (right :: left :: tag :: values) table
        (trList [right, left, tag] ++ frames)) := by
  simpa only [StateTransition.Reaches₁, cfg, entry, trList, List.nil_append,
    List.cons_append, List.append_assoc] using
    (phase_reaches .readRow store
      (K'.elim (trList values) [] (trList (tag :: left :: right :: table)) frames)
      (by decide)).trans
      ((copy_aux (copyWord aux (copyWord aux (label .restore))) store values
        (left :: right :: table) tag frames).trans
        ((copy_aux (copyWord aux (label .restore)) none (tag :: values) (right :: table)
          left (trList [tag] ++ frames)).trans
          (copy_aux (label .restore) none (left :: tag :: values) table right
            (trList [left] ++ (trList [tag] ++ frames)))))

/-- Zero removes the index and selects the current row without disturbing the tape suffixes. -/
theorem lookup_zero (store : Option Γ') (values table : List Nat) (frames : List Γ') :
    ∃ out, Reaches₁ (TM2.step machine) (cfg (label .lookup) store (0 :: values) table frames)
      (cfg (label .readRow) out values table frames) := by
  obtain ⟨out, path⟩ := RuntimeMacros.pred_ok agrees (label .readRow)
    (moveWord aux stack (moveWord aux stack (moveWord aux stack (label .lookup))))
    store (0 :: values) (trList table) frames
  simp only [List.headI_cons, List.tail_cons, Nat.rec_zero] at path
  refine ⟨out, ?_⟩
  simpa only [StateTransition.Reaches₁, cfg, entry] using
    (phase_reaches .lookup store
      (K'.elim (trList (0 :: values)) [] (trList table) frames) (by decide)).trans path

/-- A positive index skips exactly one triple, preserving each word for later restoration. -/
theorem lookup_successor (store : Option Γ') (values table : List Nat)
    (index first second third : Nat) (frames : List Γ') :
    Reaches₁ (TM2.step machine)
      (cfg (label .lookup) store ((index + 1) :: values) (first :: second :: third :: table) frames)
      (cfg (label .lookup) none (index :: values) table
        (trList [third, second, first] ++ frames)) := by
  obtain ⟨out, path⟩ := RuntimeMacros.pred_ok agrees (label .readRow)
    (moveWord aux stack (moveWord aux stack (moveWord aux stack (label .lookup))))
    store ((index + 1) :: values) (trList (first :: second :: third :: table)) frames
  simp only [List.headI_cons, List.tail_cons] at path
  simpa only [StateTransition.Reaches₁, cfg, entry, trList, List.nil_append,
    List.cons_append, List.append_assoc] using
    (phase_reaches .lookup store
      (K'.elim (trList ((index + 1) :: values)) []
        (trList (first :: second :: third :: table)) frames) (by decide)).trans
      (path.trans ((move_aux_stack (moveWord aux stack (moveWord aux stack (label .lookup)))
        out (index :: values) (second :: third :: table) first frames).trans
        ((move_aux_stack (moveWord aux stack (label .lookup)) none (index :: values)
          (third :: table) second (trList [first] ++ frames)).trans
          (move_aux_stack (label .lookup) none (index :: values) table third
            (trList [second] ++ (trList [first] ++ frames))))))

/-- Indexed skipping retains the exact reverse word prefix above arbitrary older symbols. -/
theorem lookup_prefix (index : Nat) (prefixWords : List Nat) (store : Option Γ')
    (values suffix : List Nat) (frames : List Γ') (length : prefixWords.length = 3 * index) :
    ∃ out, Reaches₁ (TM2.step machine)
      (cfg (label .lookup) store (index :: values) (prefixWords ++ suffix) frames)
      (cfg (label .readRow) out values suffix (trList prefixWords.reverse ++ frames)) := by
  induction index generalizing prefixWords store frames with
  | zero =>
    have empty : prefixWords = [] := List.length_eq_zero_iff.mp (by omega)
    subst prefixWords
    simpa only [List.nil_append, List.reverse_nil, trList] using
      lookup_zero store values suffix frames
  | succ index ih =>
    rcases prefixWords with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
    all_goals simp only [List.length_nil, List.length_cons] at length
    all_goals try omega
    obtain ⟨out, remaining⟩ := ih rest none (trList [third, second, first] ++ frames) (by omega)
    refine ⟨out, ?_⟩
    simpa only [StateTransition.Reaches₁, List.cons_append, List.reverse_cons, trList_append,
      trList, List.nil_append, List.singleton_append, List.append_assoc] using
      (lookup_successor store values (rest ++ suffix) index first second third frames).trans
        remaining

/-- Evaluation places its own fresh marker above arbitrary older frames. -/
theorem evaluate_start (store : Option Γ') (values table : List Nat) (frames : List Γ') :
    Reaches₁ (TM2.step machine) (cfg (label .evaluate) store values table frames)
      (cfg (label .lookup) store values table (.consₗ :: frames)) := by
  simpa only [StateTransition.Reaches₁, cfg, entry, elim_update_stack, elim_stack] using
    (phase_reaches .evaluate store (K'.elim (trList values) [] (trList table) frames)
      (by decide)).trans
      (RuntimeMacros.push_ok agrees stack .consₗ (label .lookup) store
        (K'.elim (trList values) [] (trList table) frames))

/-- Lookup reads a raw indexed triple and restores the whole prefix, row, and suffix. -/
theorem lookup_triple (index : Nat) (prefixWords : List Nat) (store : Option Γ')
    (values suffix : List Nat) (tag left right : Nat) (frames : List Γ')
    (length : prefixWords.length = 3 * index) :
    Reaches₁ (TM2.step machine)
      (dataCfg .evaluate store (index :: values)
        (prefixWords ++ tag :: left :: right :: suffix) frames)
      (dataCfg .dispatch none (tag :: values) (prefixWords ++ tag :: left :: right :: suffix)
        (trList [left, right] ++ frames)) := by
  obtain ⟨out, skipped⟩ := lookup_prefix index prefixWords store values
    (tag :: left :: right :: suffix) (.consₗ :: frames) length
  have read := read_row out values suffix tag left right
    (trList prefixWords.reverse ++ .consₗ :: frames)
  have restored := restore_prefix ([right, left, tag] ++ prefixWords.reverse) none values suffix
    tag left right frames
  have restored' : Reaches₁ (TM2.step machine)
      (cfg (label .restore) none (right :: left :: tag :: values) suffix
        (trList [right, left, tag] ++ (trList prefixWords.reverse ++ .consₗ :: frames)))
      (dataCfg .dispatch none (tag :: values) (prefixWords ++ tag :: left :: right :: suffix)
        (trList [left, right] ++ frames)) := by
    simpa only [cfg, dataCfg, trList_append, trList, List.append_assoc, List.reverse_append,
      List.reverse_reverse, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.cons_append] using restored
  simpa only [StateTransition.Reaches₁, cfg, dataCfg] using
    (evaluate_start store (index :: values)
      (prefixWords ++ tag :: left :: right :: suffix) frames).trans
      (skipped.trans (read.trans restored'))

theorem node_words_length (rows : List CodeDAG.Node) :
    (rows.flatMap CodeDAG.Node.words).length = 3 * rows.length := by
  induction rows with
  | nil => rfl
  | cons node rows ih =>
    simp [CodeDAG.Node.words_length, ih, Nat.mul_add, Nat.add_comm]

/-- Every in-bounds serialized node is read from tape, preserving the entire serialized table. -/
theorem lookup_node (rows : Array CodeDAG.Node) (index : Nat) (node : CodeDAG.Node)
    (row : rows[index]? = some node) (tag left right : Nat)
    (words : node.words = [tag, left, right]) (store : Option Γ')
    (values : List Nat) (frames : List Γ') :
    Reaches₁ (TM2.step machine)
      (dataCfg .evaluate store (index :: values) (rows.toList.flatMap CodeDAG.Node.words) frames)
      (dataCfg .dispatch none (tag :: values) (rows.toList.flatMap CodeDAG.Node.words)
        (trList [left, right] ++ frames)) := by
  obtain ⟨bound, equal⟩ := Array.getElem?_eq_some_iff.mp row
  have parts : rows.toList = rows.toList.take index ++ node :: rows.toList.drop (index + 1) := by
    have joined := List.take_append_drop index rows.toList
    rw [List.drop_eq_getElem_cons (by simpa only [Array.length_toList] using bound),
      Array.getElem_toList, equal] at joined
    exact joined.symm
  have encoded : rows.toList.flatMap CodeDAG.Node.words =
      (rows.toList.take index).flatMap CodeDAG.Node.words ++
        tag :: left :: right :: (rows.toList.drop (index + 1)).flatMap CodeDAG.Node.words := by
    simpa only [List.flatMap_append, List.flatMap_cons, words, List.cons_append,
      List.nil_append] using congrArg (List.flatMap CodeDAG.Node.words) parts
  have length : ((rows.toList.take index).flatMap CodeDAG.Node.words).length = 3 * index := by
    rw [node_words_length, List.length_take, Array.length_toList,
      Nat.min_eq_left (Nat.le_of_lt bound)]
  simpa only [← encoded] using
    lookup_triple index ((rows.toList.take index).flatMap CodeDAG.Node.words) store values
      ((rows.toList.drop (index + 1)).flatMap CodeDAG.Node.words) tag left right frames length

end ConjectureMachines.Compilation.RuntimeLookup
