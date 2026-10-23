/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.NatCode

/-! # Explicit dynamic list programs

These are actual `ToPartrec.Code` syntax trees. Dynamic indexing uses zero beyond the input,
as does the underlying scalar instruction set. Operations needing an end boundary use an
explicit length; they never infer a list length by treating a zero word as an end marker.
-/

@[expose] public section

namespace ConjectureMachines.Compilation.ListCode

open Turing.ToPartrec

set_option backward.isDefEq.respectTransparency false

attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some

/-- A zero tag terminates a `Code.fix`, returning the remainder of its result. -/
theorem fix_stop (body : Code) (v out : List ℕ)
    (h : body.eval v = pure (0 :: out)) :
    (Code.fix body).eval v = pure out := by
  apply Part.eq_some_iff.mpr
  exact PFun.fix_stop (by simp [h])

/-- A positive tag continues a `Code.fix` with the remainder of its result. -/
theorem fix_next (body : Code) (v next : List ℕ)
    (h : body.eval v = pure (1 :: next)) :
    (Code.fix body).eval v = (Code.fix body).eval next := by
  exact PFun.fix_fwd_eq (by simp [h])

/-- The positive continuation tag, written without unnecessary arithmetic. -/
def one : Code := .comp .succ .zero

@[simp] theorem one_eval (v : List ℕ) : one.eval v = pure [1] := by
  simp [one, Bind.bind]

/-- Decrease the counter and remove one residual word, or stop at counter zero. -/
def dropBody : Code :=
  .case .zero' (.cons (one) (.cons .head (.comp .tail .tail)))

@[simp] theorem dropBody_zero (v : List ℕ) :
    dropBody.eval (0 :: v) = pure (0 :: v) := by
  simp [dropBody]

@[simp] theorem dropBody_succ (n : ℕ) (v : List ℕ) :
    dropBody.eval ((n + 1) :: v) = pure (1 :: n :: v.tail) := by
  simp [dropBody, Bind.bind]

/-- Drop a dynamic number of words: the input is `count :: data`. -/
def drop : Code := .fix dropBody

@[simp] theorem drop_eval (n : ℕ) (v : List ℕ) :
    drop.eval (n :: v) = pure (v.drop n) := by
  induction n generalizing v with
  | zero => exact fix_stop dropBody _ _ (dropBody_zero v)
  | succ n ih =>
    rw [drop, fix_next dropBody _ _ (dropBody_succ n v)]
    have h := ih v.tail
    cases v <;> simpa [drop] using h

/-- Missing counter means zero, so dropping from empty input returns empty. -/
theorem drop_eval_all (v : List ℕ) :
    drop.eval v = pure (v.tail.drop v.headI) := by
  cases v with
  | nil => exact fix_stop dropBody _ _ (by simp [dropBody])
  | cons n v => exact drop_eval n v

/-- Dynamic indexing, returning the selected word or zero beyond the end. -/
def get : Code := .comp .head drop

@[simp] theorem get_eval (n : ℕ) (v : List ℕ) :
    get.eval (n :: v) = pure [v[n]?.getD 0] := by
  have h : ∀ w : List ℕ, w.headI = w.head?.getD 0 := by
    intro w
    cases w <;> rfl
  simp [get, Bind.bind, h, List.head?_drop]

theorem get_eval_all (v : List ℕ) :
    get.eval v = pure [(v.tail[v.headI]?).getD 0] := by
  cases v with
  | nil => simp [get, drop_eval_all, Bind.bind]
  | cons n v => exact get_eval n v

/-- An explicit binary-stack cell. Zero represents an empty stack. -/
def pack (x rest : ℕ) : ℕ := 2 ^ x * (2 * rest + 1)

theorem pack_pos (x rest : ℕ) : 0 < pack x rest := by
  exact Nat.mul_pos (pow_pos (by omega) _) (by omega)

/-- Power of two, by primitive recursion on the first word. -/
def powTwo : Code := Code.prec (one) (.comp NatCode.double (NatCode.nth 1))

@[simp] theorem powTwo_eval (v : List ℕ) :
    powTwo.eval v = pure [2 ^ v.headI] := by
  have h := NatCode.prec_eval_all (one)
    (.comp NatCode.double (NatCode.nth 1)) (fun _ ↦ 1) (fun _ b _ ↦ 2 * b)
    (fun _ ↦ by simp) (fun _ _ _ ↦ by simp [Bind.bind]) v
  have hr : ∀ n, Nat.rec 1 (fun _ b ↦ 2 * b) n = 2 ^ n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change 2 * Nat.rec 1 (fun _ b ↦ 2 * b) n = 2 ^ (n + 1)
      rw [ih, pow_succ, Nat.mul_comm]
  simpa only [powTwo, hr] using h

/-- Construct a binary-stack cell from the first two words. -/
def packCode : Code :=
  .comp NatCode.mul (NatCode.tuple
    [powTwo, .comp .succ (.comp NatCode.double (NatCode.nth 1))])

@[simp] theorem packCode_eval (x rest : ℕ) (v : List ℕ) :
    packCode.eval (x :: rest :: v) = pure [pack x rest] := by
  simp [packCode, NatCode.tuple, pack, Bind.bind]

/-- Remove factors of two, retaining the exponent and the decoded residual stack. -/
def unpackBody : Code :=
  let half := .comp NatCode.div (NatCode.tuple [.head, NatCode.literal 2])
  let oddRest := .comp NatCode.div
    (NatCode.tuple [.pred, NatCode.literal 2])
  let stop := .cons .zero (.cons (NatCode.nth 1) (.cons oddRest (NatCode.drop 2)))
  let zeroStop := .cons .zero (.cons (NatCode.nth 1) (.cons .zero (NatCode.drop 2)))
  let step := .cons (one)
    (.cons half (.cons (.comp .succ (NatCode.nth 1)) (NatCode.drop 2)))
  NatCode.ifZero .head zeroStop
    (NatCode.ifZero (.comp NatCode.mod
      (NatCode.tuple [.head, NatCode.literal 2])) step stop)

theorem unpackBody_odd (rest count : ℕ) (v : List ℕ) :
    unpackBody.eval ((2 * rest + 1) :: count :: v) = pure (0 :: count :: rest :: v) := by
  simp [unpackBody, NatCode.ifZero, NatCode.tuple, Bind.bind]

theorem unpackBody_even (n count : ℕ) (v : List ℕ) (hn : n ≠ 0) :
    unpackBody.eval ((2 * n) :: count :: v) = pure (1 :: n :: (count + 1) :: v) := by
  have hn2 : 2 * n ≠ 0 := Nat.mul_ne_zero (by omega) hn
  simp only [unpackBody]
  rw [NatCode.ifZero_eval _ _ _ _ [2 * n] (by simp)]
  simp only [List.headI_cons, hn2, ↓reduceIte]
  rw [NatCode.ifZero_eval _ _ _ _ [0] (by simp [NatCode.tuple, Bind.bind])]
  simp [NatCode.tuple, Bind.bind]

/-- The factor-removal loop. Its proof uses the actual fixpoint semantics. -/
def unpackLoop : Code := .fix unpackBody

theorem unpackLoop_eval (x rest count : ℕ) (v : List ℕ) :
    unpackLoop.eval (pack x rest :: count :: v) = pure ((count + x) :: rest :: v) := by
  induction x generalizing count with
  | zero =>
    simpa [unpackLoop, pack] using
      fix_stop unpackBody _ _ (unpackBody_odd rest count v)
  | succ x ih =>
    have hp : pack (x + 1) rest = 2 * pack x rest := by
      simp [pack, pow_succ]
      ring
    rw [hp, unpackLoop,
      fix_next unpackBody _ _ (unpackBody_even _ count v (Nat.ne_of_gt (pack_pos x rest)))]
    simpa [unpackLoop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (count + 1)

/-- Decode a nonzero binary-stack cell, retaining an arbitrary suffix. -/
def unpack : Code := .comp unpackLoop (.cons .head (.cons .zero .tail))

@[simp] theorem unpack_eval (x rest : ℕ) (v : List ℕ) :
    unpack.eval (pack x rest :: v) = pure (x :: rest :: v) := by
  simp [unpack, unpackLoop_eval, Bind.bind]

/-- A finite stack encoded as a natural number. This is data, not a primitive instruction. -/
def stack : List ℕ → ℕ
  | [] => 0
  | x :: xs => pack x (stack xs)

/-- The stack's bit length grows at most linearly in the sum of its words and their count. -/
theorem stack_lt_pow (xs : List ℕ) : stack xs < 2 ^ (xs.sum + xs.length) := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    have hb : 2 * stack xs + 1 < 2 ^ (xs.sum + xs.length + 1) := by
      rw [pow_succ]
      omega
    have hh := Nat.mul_lt_mul_of_pos_left hb (show 0 < 2 ^ x by positivity)
    rw [← pow_add] at hh
    simpa [stack, pack, List.sum_cons, List.length_cons, Nat.add_assoc] using hh

/-- Collect a specified prefix onto a reversed, numerically encoded accumulator. -/
def splitBody : Code :=
  .case .zero' (.cons (one) (.cons .head
    (.cons (.comp packCode (NatCode.tuple [NatCode.nth 2, NatCode.nth 1]))
      (NatCode.drop 3))))

theorem splitBody_zero (acc : ℕ) (v : List ℕ) :
    splitBody.eval (0 :: acc :: v) = pure (0 :: acc :: v) := by
  simp [splitBody]

theorem splitBody_succ (n acc x : ℕ) (v : List ℕ) :
    splitBody.eval ((n + 1) :: acc :: x :: v) = pure (1 :: n :: pack x acc :: v) := by
  simp [splitBody, NatCode.tuple, Bind.bind]

/-- Prefix collection loop. -/
def splitLoop : Code := .fix splitBody

theorem splitLoop_eval (xs acc v : List ℕ) :
    splitLoop.eval (xs.length :: stack acc :: (xs ++ v)) =
      pure (stack (xs.reverse ++ acc) :: v) := by
  induction xs generalizing acc with
  | nil => exact fix_stop splitBody _ _ (splitBody_zero (stack acc) v)
  | cons x xs ih =>
    rw [List.length_cons, List.cons_append, splitLoop,
      fix_next splitBody _ _ (splitBody_succ xs.length (stack acc) x (xs ++ v))]
    simpa [splitLoop, stack, List.reverse_cons, List.append_assoc] using ih (x :: acc)

/-- Input `n :: data` becomes `encodedReversePrefix :: residualData`. -/
def split : Code := .comp splitLoop (.cons .head (.cons .zero .tail))

theorem split_eval (xs v : List ℕ) :
    split.eval (xs.length :: (xs ++ v)) = pure (stack xs.reverse :: v) := by
  simpa [split, Bind.bind, stack] using splitLoop_eval xs [] v

/-- Decode one stack cell and push its word onto the output list. -/
def restoreBody : Code :=
  NatCode.ifZero .head (.comp .zero' .tail)
    (.comp (.cons (one)
      (.cons (NatCode.nth 1) (.cons .head (NatCode.drop 2)))) unpack)

theorem restoreBody_zero (v : List ℕ) :
    restoreBody.eval (0 :: v) = pure (0 :: v) := by
  simp [restoreBody, NatCode.ifZero, Bind.bind]

theorem restoreBody_pack (x acc : ℕ) (v : List ℕ) :
    restoreBody.eval (pack x acc :: v) = pure (1 :: acc :: x :: v) := by
  rw [restoreBody, NatCode.ifZero_eval _ _ _ _ [pack x acc] (by simp)]
  simp [Nat.ne_of_gt (pack_pos x acc), Bind.bind]

/-- Restore a numerically encoded stack in reverse order before an arbitrary suffix. -/
def restore : Code := .fix restoreBody

theorem restore_eval (xs v : List ℕ) :
    restore.eval (stack xs :: v) = pure (xs.reverse ++ v) := by
  induction xs generalizing v with
  | nil => exact fix_stop restoreBody _ _ (restoreBody_zero v)
  | cons x xs ih =>
    rw [stack, restore, fix_next restoreBody _ _ (restoreBody_pack x (stack xs) v)]
    simpa [restore, List.reverse_cons, List.append_assoc] using ih (x :: v)

/-- Take a counted prefix. Its contract specifies a prefix actually present in the input. -/
def take : Code := .comp restore (.comp .head split)

theorem take_eval (xs v : List ℕ) :
    take.eval (xs.length :: (xs ++ v)) = pure xs := by
  simp [take, split_eval, Bind.bind, restore_eval]

/-- The length of a length-framed list is its first word. -/
def length : Code := .head

@[simp] theorem length_eval (xs : List ℕ) :
    length.eval (xs.length :: xs) = pure [xs.length] := by
  simp [length]

/-- Concatenate two framed lists: `length xs :: xs ++ length ys :: ys`. -/
def append : Code :=
  .comp restore (.comp (.cons .head (NatCode.drop 2)) split)

theorem append_eval (xs ys : List ℕ) :
    append.eval (xs.length :: (xs ++ ys.length :: ys)) = pure (xs ++ ys) := by
  simp [append, split_eval, Bind.bind, restore_eval]

/-- Preserve one scalar parameter while collecting a prefix, then transform the suffix. -/
def editBody (edit : Code) : Code :=
  .case (.cons .zero (.cons .head (.comp edit .tail)))
    (.cons (one) (.cons .head
      (.cons (.comp packCode (NatCode.tuple [NatCode.nth 3, NatCode.nth 1]))
        (.cons (NatCode.nth 2) (NatCode.drop 4)))))

theorem editBody_zero (edit : Code) (E : List ℕ → List ℕ)
    (he : ∀ v, edit.eval v = pure (E v)) (acc param : ℕ) (v : List ℕ) :
    (editBody edit).eval (0 :: acc :: param :: v) = pure (0 :: acc :: E (param :: v)) := by
  simp [editBody, he, Bind.bind]

theorem editBody_succ (edit : Code) (n acc param x : ℕ) (v : List ℕ) :
    (editBody edit).eval ((n + 1) :: acc :: param :: x :: v) =
      pure (1 :: n :: pack x acc :: param :: v) := by
  simp [editBody, NatCode.tuple, Bind.bind]

theorem editLoop_eval (edit : Code) (E : List ℕ → List ℕ)
    (he : ∀ v, edit.eval v = pure (E v)) (xs acc : List ℕ) (param : ℕ) (v : List ℕ) :
    (Code.fix (editBody edit)).eval (xs.length :: stack acc :: param :: (xs ++ v)) =
      pure (stack (xs.reverse ++ acc) :: E (param :: v)) := by
  induction xs generalizing acc with
  | nil => exact fix_stop _ _ _ (editBody_zero edit E he (stack acc) param v)
  | cons x xs ih =>
    rw [List.length_cons, List.cons_append,
      fix_next _ _ _ (editBody_succ edit xs.length (stack acc) param x (xs ++ v))]
    simpa [stack, List.reverse_cons, List.append_assoc] using ih (x :: acc)

/-- Transform a suffix after a counted prefix, retaining that prefix exactly. -/
def editPrefix (edit : Code) : Code :=
  .comp restore (.comp (.fix (editBody edit)) (.cons .head (.cons .zero .tail)))

theorem editPrefix_eval (edit : Code) (E : List ℕ → List ℕ)
    (he : ∀ v, edit.eval v = pure (E v)) (xs : List ℕ) (param : ℕ) (v : List ℕ) :
    (editPrefix edit).eval (xs.length :: param :: (xs ++ v)) = pure (xs ++ E (param :: v)) := by
  have h := editLoop_eval edit E he xs [] param v
  simpa [editPrefix, Bind.bind, stack, restore_eval] using
    congrArg (fun r ↦ r >>= restore.eval) h

/-- Replace the word after a counted present prefix; empty suffix inserts the replacement. -/
def replacePrefix : Code := editPrefix (.cons .head (NatCode.drop 2))

theorem replacePrefix_eval (xs : List ℕ) (x : ℕ) (v : List ℕ) :
    replacePrefix.eval (xs.length :: x :: (xs ++ v)) = pure (xs ++ x :: v.tail) := by
  exact editPrefix_eval _ (fun w ↦ w.headI :: w.tail.tail)
    (fun _ ↦ by simp [Bind.bind, List.drop_add_one_eq_tail_drop]) xs x v

/-- Insert a word after a counted present prefix. -/
def insertPrefix : Code := editPrefix .id

theorem insertPrefix_eval (xs : List ℕ) (x : ℕ) (v : List ℕ) :
    insertPrefix.eval (xs.length :: x :: (xs ++ v)) = pure (xs ++ x :: v) := by
  exact editPrefix_eval _ id (fun _ ↦ by simp) xs x v

/-- Delete the word after a counted present prefix. A dummy scalar parameter is ignored. -/
def erasePrefix : Code := editPrefix (NatCode.drop 2)

theorem erasePrefix_eval (xs : List ℕ) (param : ℕ) (v : List ℕ) :
    erasePrefix.eval (xs.length :: param :: (xs ++ v)) = pure (xs ++ v.tail) := by
  exact editPrefix_eval _ (fun w ↦ w.tail.tail)
    (fun _ ↦ by simp [List.drop_add_one_eq_tail_drop]) xs param v

/-- A replacement after an in-range index agrees with ordinary list update. -/
theorem replacePrefix_inBounds (n x : ℕ) (v : List ℕ) (hn : n < v.length) :
    replacePrefix.eval (n :: x :: v) = pure (v.set n x) := by
  have h := replacePrefix_eval (v.take n) x (v.drop n)
  simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn), List.take_append_drop,
    List.tail_drop, List.set_eq_take_append_cons_drop, hn] using h

/-- Total framed update: `index :: trueLength :: replacement :: data`. -/
def set : Code :=
  NatCode.ifZero (.comp NatCode.lt (NatCode.tuple [NatCode.nth 0, NatCode.nth 1]))
    (NatCode.drop 3)
    (.comp replacePrefix (.cons .head (.cons (NatCode.nth 2) (NatCode.drop 3))))

theorem set_eval (n x : ℕ) (v : List ℕ) :
    set.eval (n :: v.length :: x :: v) = pure (v.set n x) := by
  rw [set, NatCode.ifZero_eval _ _ _ _ [if n < v.length then 1 else 0]
    (by simp [NatCode.tuple, Bind.bind])]
  by_cases hn : n < v.length
  · simp [hn, Bind.bind, replacePrefix_inBounds n x v hn]
  · simp [hn, List.set_eq_of_length_le (Nat.le_of_not_gt hn)]

/-- Cap a requested prefix by the explicitly supplied true list length. -/
def takeBounded : Code :=
  .comp take (.cons
    (NatCode.ifZero (.comp NatCode.le (NatCode.tuple [NatCode.nth 0, NatCode.nth 1]))
      (NatCode.nth 1) .head) (NatCode.drop 2))

theorem takeBounded_eval (n : ℕ) (v : List ℕ) :
    takeBounded.eval (n :: v.length :: v) = pure (v.take n) := by
  have h : take.eval ((v.take n).length :: v) = pure (v.take n) := by
    simpa only [List.take_append_drop] using take_eval (v.take n) (v.drop n)
  simp only [takeBounded, Code.comp_eval, Code.cons_eval]
  rw [NatCode.ifZero_eval _ _ _ _ [if n ≤ v.length then 1 else 0]
    (by simp [NatCode.tuple, Bind.bind])]
  by_cases hn : n ≤ v.length
  · simpa [Bind.bind, hn, List.length_take, Nat.min_eq_left hn] using h
  · simpa [Bind.bind, hn, List.length_take, Nat.min_eq_right (Nat.le_of_not_ge hn)] using h

/-- Fold over a finite encoded list, retaining the scalar accumulator and all parameters. -/
def foldBody (step : Code) : Code :=
  NatCode.ifZero .head (.comp .zero' .tail)
    (.comp (.cons (one) (.cons (NatCode.nth 1)
      (.cons (.comp step (.cons .head (NatCode.drop 2))) (NatCode.drop 3)))) unpack)

theorem foldBody_zero (step : Code) (acc : ℕ) (v : List ℕ) :
    (foldBody step).eval (0 :: acc :: v) = pure (0 :: acc :: v) := by
  simp [foldBody, NatCode.ifZero, Bind.bind]

theorem foldBody_pack (step : Code) (F : ℕ → ℕ → List ℕ → ℕ)
    (hs : ∀ x acc v, step.eval (x :: acc :: v) = pure [F x acc v])
    (x rest acc : ℕ) (v : List ℕ) :
    (foldBody step).eval (pack x rest :: acc :: v) =
      pure (1 :: rest :: F x acc v :: v) := by
  rw [foldBody, NatCode.ifZero_eval _ _ _ _ [pack x rest] (by simp)]
  simp [Nat.ne_of_gt (pack_pos x rest), hs, Bind.bind]

/-- A concrete finite-list primitive recursion operator. -/
def foldStack (step : Code) : Code := .fix (foldBody step)

theorem foldStack_eval (step : Code) (F : ℕ → ℕ → List ℕ → ℕ)
    (hs : ∀ x acc v, step.eval (x :: acc :: v) = pure [F x acc v])
    (xs : List ℕ) (acc : ℕ) (v : List ℕ) :
    (foldStack step).eval (stack xs :: acc :: v) =
      pure (xs.foldl (fun a x ↦ F x a v) acc :: v) := by
  induction xs generalizing acc with
  | nil => exact fix_stop _ _ _ (foldBody_zero step acc v)
  | cons x xs ih =>
    rw [stack, foldStack,
      fix_next _ _ _ (foldBody_pack step F hs x (stack xs) acc v)]
    exact ih (F x acc v)

theorem foldl_pack (xs acc : List ℕ) :
    xs.foldl (fun a x ↦ pack x a) (stack acc) = stack (xs.reverse ++ acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simpa [List.foldl_cons, stack, List.reverse_cons, List.append_assoc] using ih (x :: acc)

/-- Reverse a counted prefix, retaining all words after it. -/
def reverse : Code := .comp restore
  (.comp (foldStack packCode) (.comp (.cons .head (.cons .zero .tail)) split))

theorem reverse_eval (xs v : List ℕ) :
    reverse.eval (xs.length :: (xs ++ v)) = pure (xs.reverse ++ v) := by
  have h := foldStack_eval packCode (fun x acc _ ↦ pack x acc)
    (fun x acc v ↦ packCode_eval x acc v) xs.reverse 0 v
  have hf : xs.reverse.foldl (fun a x ↦ pack x a) 0 = stack xs := by
    simpa [stack] using foldl_pack xs.reverse []
  simp [reverse, split_eval, Bind.bind, h, hf, restore_eval]

/-- Erasure after a present prefix agrees with ordinary list deletion. -/
theorem erasePrefix_inBounds (n : ℕ) (v : List ℕ) (hn : n < v.length) :
    erasePrefix.eval (n :: 0 :: v) = pure (v.eraseIdx n) := by
  have h := erasePrefix_eval (v.take n) 0 (v.drop n)
  simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn), List.take_append_drop,
    List.tail_drop, List.eraseIdx_eq_take_drop_succ] using h

/-- Total framed deletion: `index :: trueLength :: data`. -/
def erase : Code :=
  NatCode.ifZero (.comp NatCode.lt (NatCode.tuple [NatCode.nth 0, NatCode.nth 1]))
    (NatCode.drop 2)
    (.comp erasePrefix (.cons .head (.cons .zero (NatCode.drop 2))))

theorem erase_eval (n : ℕ) (v : List ℕ) :
    erase.eval (n :: v.length :: v) = pure (v.eraseIdx n) := by
  rw [erase, NatCode.ifZero_eval _ _ _ _ [if n < v.length then 1 else 0]
    (by simp [NatCode.tuple, Bind.bind])]
  by_cases hn : n < v.length
  · simp [hn, Bind.bind, erasePrefix_inBounds n v hn]
  · simp [hn, List.eraseIdx_of_length_le (Nat.le_of_not_gt hn)]

theorem insertPrefix_inBounds (n x : ℕ) (v : List ℕ) (hn : n ≤ v.length) :
    insertPrefix.eval (n :: x :: v) = pure (v.take n ++ x :: v.drop n) := by
  have h := insertPrefix_eval (v.take n) x (v.drop n)
  simpa [List.length_take, Nat.min_eq_left hn, List.take_append_drop] using h

/-- Total framed insertion. Index equal to the length appends; larger indices leave data alone. -/
def insert : Code :=
  NatCode.ifZero (.comp NatCode.le (NatCode.tuple [NatCode.nth 0, NatCode.nth 1]))
    (NatCode.drop 3)
    (.comp insertPrefix (.cons .head (.cons (NatCode.nth 2) (NatCode.drop 3))))

theorem insert_eval (n x : ℕ) (v : List ℕ) :
    insert.eval (n :: v.length :: x :: v) =
      pure (if n ≤ v.length then v.take n ++ x :: v.drop n else v) := by
  rw [insert, NatCode.ifZero_eval _ _ _ _ [if n ≤ v.length then 1 else 0]
    (by simp [NatCode.tuple, Bind.bind])]
  by_cases hn : n ≤ v.length
  · simp [hn, Bind.bind, insertPrefix_inBounds n x v hn]
  · simp [hn]

/-- Rule-procedure fixtures include zeros as data, empty lists, and out-of-range indices. -/
theorem fixtures :
    get.eval [1, 7, 0, 9] = pure [0] ∧
    get.eval [5, 7, 0, 9] = pure [0] ∧
    drop.eval [2, 7, 0, 9] = pure [9] ∧
    takeBounded.eval [7, 3, 7, 0, 9] = pure [7, 0, 9] ∧
    takeBounded.eval [0, 0] = pure [] ∧
    set.eval [1, 3, 4, 7, 0, 9] = pure [7, 4, 9] ∧
    set.eval [5, 3, 4, 7, 0, 9] = pure [7, 0, 9] ∧
    erase.eval [1, 3, 7, 0, 9] = pure [7, 9] ∧
    erase.eval [5, 3, 7, 0, 9] = pure [7, 0, 9] ∧
    insert.eval [3, 3, 0, 7, 0, 9] = pure [7, 0, 9, 0] ∧
    insert.eval [4, 3, 0, 7, 0, 9] = pure [7, 0, 9] ∧
    append.eval [2, 7, 0, 2, 9, 0] = pure [7, 0, 9, 0] ∧
    reverse.eval [3, 7, 0, 9] = pure [9, 0, 7] := by
  have ht := takeBounded_eval 7 [7, 0, 9]
  have hte := takeBounded_eval 0 []
  have hs := set_eval 1 4 [7, 0, 9]
  have hso := set_eval 5 4 [7, 0, 9]
  have he := erase_eval 1 [7, 0, 9]
  have heo := erase_eval 5 [7, 0, 9]
  have hi := insert_eval 3 0 [7, 0, 9]
  have hio := insert_eval 4 0 [7, 0, 9]
  have ha := append_eval [7, 0] [9, 0]
  have hr := reverse_eval [7, 0, 9] []
  exact ⟨get_eval 1 [7, 0, 9], get_eval 5 [7, 0, 9], drop_eval 2 [7, 0, 9],
    ht, hte, hs, hso, he, heo, hi, hio, ha, hr⟩

/-- Execute mathlib's sequential `Code` semantics for a bounded number of steps. -/
def run : ℕ → Cfg → Option (List ℕ)
  | 0, _ => none
  | _ + 1, .halt v => some v
  | fuel + 1, .ret k v => run fuel (stepRet k v)

/-- An executable fixture entry point; timeout is represented by `none`. -/
def runCode (fuel : ℕ) (c : Code) (v : List ℕ) : Option (List ℕ) :=
  run fuel (stepNormal c .halt v)

/-- Direct sequential executions supplement the general partial-semantics proofs. -/
theorem execution_fixtures :
    runCode 200 get [1, 7, 0, 9] = some [0] ∧
    runCode 500 get [5, 7, 0, 9] = some [0] ∧
    runCode 200 drop [2, 7, 0, 9] = some [9] ∧
    runCode 20 drop [] = some [] := by
  decide

end ConjectureMachines.Compilation.ListCode
