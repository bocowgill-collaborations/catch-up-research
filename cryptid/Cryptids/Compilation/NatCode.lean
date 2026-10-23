/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Computability.TuringMachine.Config
public import Mathlib.Data.Nat.Bits
public import Mathlib.Tactic

/-! # Explicit natural-number programs in the `ToPartrec.Code` basis

All procedures below are syntax trees over mathlib's seven `Code` constructors. Their
specifications are equalities of the actual partial semantics, including empty and short inputs.
-/

@[expose] public section

namespace ConjectureMachines.Compilation.NatCode

open Turing.ToPartrec

set_option backward.isDefEq.respectTransparency false

attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some

/-- Drop a fixed number of input words. -/
def drop : ℕ → Code
  | 0 => .id
  | n + 1 => .comp (drop n) .tail

@[simp] theorem drop_eval (n : ℕ) (v : List ℕ) : (drop n).eval v = pure (v.drop n) := by
  induction n generalizing v with
  | zero => simp [drop]
  | succ n ih => simpa [drop, Bind.bind] using ih v.tail

/-- Select one input word, returning zero beyond the end of the list. -/
def nth (n : ℕ) : Code := .comp .head (drop n)

@[simp] theorem nth_eval (n : ℕ) (v : List ℕ) :
    (nth n).eval v = pure [v[n]?.getD 0] := by
  have h : ∀ w : List ℕ, w.headI = w.head?.getD 0 := by
    intro w
    cases w <;> rfl
  simp [nth, Bind.bind, h, List.head?_drop]

/-- Collect the head of each result, with zero for an empty result. -/
def tuple : List Code → Code
  | [] => .nil
  | c :: cs => .cons c (tuple cs)

/-- Unconditional partial semantics of tuple construction, including divergent components. -/
theorem tuple_eval_part (cs : List Code) (v : List ℕ) :
    (tuple cs).eval v = cs.mapM (fun c ↦ (c.eval v).map List.headI) := by
  induction cs with
  | nil => simp [tuple]
  | cons c cs ih => simp [tuple, ih, List.mapM_cons, Bind.bind, Part.bind_map]

theorem tuple_eval (cs : List Code) (fs : List (List ℕ → List ℕ))
    (h : List.Forall₂ (fun c f ↦ ∀ v, c.eval v = pure (f v)) cs fs) (v : List ℕ) :
    (tuple cs).eval v = pure (fs.map fun f ↦ (f v).headI) := by
  induction h with
  | nil => simp [tuple]
  | cons h hs ih => simp [tuple, h, ih, Bind.bind]

/-- Primitive recursion, with the residual input retained unchanged during every iteration. -/
theorem prec_eval (f g : Code) (F : List ℕ → ℕ) (G : ℕ → ℕ → List ℕ → ℕ)
    (hf : ∀ v, f.eval v = pure [F v])
    (hg : ∀ a b v, g.eval (a :: b :: v) = pure [G a b v]) (n : ℕ) (v : List ℕ) :
    (Code.prec f g).eval (n :: v) = pure [Nat.rec (F v) (fun a b ↦ G a b v) n] := by
  induction n with
  | zero => simp [Code.prec, hf, Bind.bind]
  | succ n _ =>
    suffices ∀ a b, a + b = n →
        (n.succ :: 0 :: G n (Nat.rec (F v) (fun a b ↦ G a b v) n) v :: v : List ℕ) ∈
          PFun.fix
            (fun w : List ℕ ↦ Part.bind (g.eval (w.headI :: w.tail.tail))
              (fun x ↦ Part.some (if w.tail.headI = 0
                then Sum.inl
                  (w.headI.succ :: w.tail.headI.pred :: x.headI :: w.tail.tail.tail)
                else Sum.inr
                  (w.headI.succ :: w.tail.headI.pred :: x.headI :: w.tail.tail.tail))))
            (a :: b :: Nat.rec (F v) (fun a b ↦ G a b v) a :: v) by
      have h := Part.eq_some_iff.mpr (this 0 n (Nat.zero_add n))
      simp [Code.prec, hf, Part.bind_assoc, Bind.bind]
      simp_all
    intro a b e
    induction b generalizing a with
    | zero =>
      refine PFun.mem_fix_iff.2 (Or.inl <| Part.eq_some_iff.1 ?_)
      simp only [hg, ← e, Part.bind_some, List.tail_cons, pure]
      rfl
    | succ b ih =>
      refine PFun.mem_fix_iff.2 (Or.inr ⟨_, ?_, ih (a + 1) (by omega)⟩)
      simp only [hg, Part.bind_some, List.tail_cons, pure]
      exact Part.mem_some_iff.2 rfl

/-- The recursion theorem also covers the empty input, interpreted as zero with no parameters. -/
theorem prec_eval_all (f g : Code) (F : List ℕ → ℕ) (G : ℕ → ℕ → List ℕ → ℕ)
    (hf : ∀ v, f.eval v = pure [F v])
    (hg : ∀ a b v, g.eval (a :: b :: v) = pure [G a b v]) (v : List ℕ) :
    (Code.prec f g).eval v =
      pure [Nat.rec (F v.tail) (fun a b ↦ G a b v.tail) v.headI] := by
  cases v with
  | nil => simp [Code.prec, hf, Bind.bind]
  | cons n v => exact prec_eval f g F G hf hg n v

/-- Add the first two words (missing words are zero). -/
def add : Code := Code.prec .head (.comp .succ (nth 1))

@[simp] theorem add_eval (v : List ℕ) :
    add.eval v = pure [v.headI + v.tail.headI] := by
  have h := prec_eval_all .head (.comp .succ (nth 1))
    (fun w ↦ w.headI) (fun _ b _ ↦ b + 1)
    (fun w ↦ by simp) (fun a b w ↦ by simp [Bind.bind]) v
  have hr : ∀ n, Nat.rec v.tail.headI (fun _ b ↦ b + 1) n = n + v.tail.headI := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      change Nat.rec _ _ n + 1 = n + 1 + v.tail.headI
      rw [ih]
      omega
  simpa only [add, hr] using h

/-- Iterate predecessor; the count is the first word. -/
def subtractCount : Code := Code.prec .head (.comp .pred (nth 1))

@[simp] theorem subtractCount_eval (v : List ℕ) :
    subtractCount.eval v = pure [v.tail.headI - v.headI] := by
  have h := prec_eval_all .head (.comp .pred (nth 1))
    (fun w ↦ w.headI) (fun _ b _ ↦ b.pred)
    (fun w ↦ by simp) (fun a b w ↦ by simp [Bind.bind]) v
  have hr : ∀ n, Nat.rec v.tail.headI (fun _ b ↦ b.pred) n = v.tail.headI - n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      change (Nat.rec (motive := fun _ ↦ ℕ) v.tail.headI (fun _ b ↦ b.pred) n).pred =
        v.tail.headI - (n + 1)
      rw [ih]
      rw [Nat.pred_eq_sub_one]
      omega
  simpa only [subtractCount, hr] using h

/-- Truncated subtraction of the second word from the first. -/
def sub : Code := .comp subtractCount (tuple [nth 1, nth 0])

@[simp] theorem sub_eval (v : List ℕ) :
    sub.eval v = pure [v.headI - v.tail.headI] := by
  have h₀ : ∀ w : List ℕ, w[0]?.getD 0 = w.headI := by intro w; cases w <;> rfl
  have h₁ : ∀ w : List ℕ, w[1]?.getD 0 = w.tail.headI := by
    intro w
    cases w with
    | nil => rfl
    | cons a w => exact h₀ w
  simp [sub, tuple, Bind.bind, h₀, h₁]

/-- Multiply the first two words by repeated addition. -/
def mul : Code := Code.prec .zero (.comp add (tuple [nth 1, nth 2]))

@[simp] theorem mul_eval (v : List ℕ) :
    mul.eval v = pure [v.headI * v.tail.headI] := by
  have h := prec_eval_all .zero (.comp add (tuple [nth 1, nth 2]))
    (fun _ ↦ 0) (fun _ b w ↦ b + w.headI)
    (fun w ↦ by simp) (fun a b w ↦ by
      cases w <;> simp [tuple, Bind.bind]) v
  have hr : ∀ n, Nat.rec 0 (fun _ b ↦ b + v.tail.headI) n = n * v.tail.headI := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp [ih, Nat.succ_mul]
  simpa [mul, hr] using h

/-- Twice the first word. -/
def double : Code := .comp add (tuple [.head, .head])

@[simp] theorem double_eval (v : List ℕ) : double.eval v = pure [2 * v.headI] := by
  simp [double, tuple, Bind.bind, two_mul]

/-- Binary literal construction: exactly one recursive subtree is used at each binary digit. -/
def literal : ℕ → Code :=
  Nat.binaryRec .zero fun b _ c ↦
    if b then .comp .succ (.comp double c) else .comp double c

theorem literal_bit (b : Bool) (n : ℕ) (h : n = 0 → b = true) :
    literal (Nat.bit b n) =
      if b then .comp .succ (.comp double (literal n)) else .comp double (literal n) := by
  exact Nat.binaryRec_eq b n (Or.inr h)

@[simp] theorem literal_eval (n : ℕ) (v : List ℕ) : (literal n).eval v = pure [n] := by
  induction n using Nat.binaryRec' with
  | zero => simp [literal]
  | bit b n hn ih =>
    rw [literal_bit b n hn]
    cases b <;> simp [ih, Bind.bind, Nat.bit_val]

/-- Count constructor occurrences, including repeated subtrees in the fully expanded syntax. -/
def nodes : Code → ℕ
  | .zero' | .succ | .tail => 1
  | .cons f g | .comp f g | .case f g => 1 + nodes f + nodes g
  | .fix f => 1 + nodes f

/-- Literal syntax is bounded linearly in the binary length, independently of its numeric value. -/
theorem literal_nodes (n : ℕ) :
    nodes (literal n) ≤ nodes Code.zero + (nodes double + 3) * Nat.size n := by
  induction n using Nat.binaryRec' with
  | zero => simp [literal, Nat.size]
  | bit b n hn ih =>
    rw [literal_bit b n hn]
    have hs : Nat.size (Nat.bit b n) = Nat.size n + 1 := by
      rw [Nat.size, Nat.binaryRec_eq _ _ (Or.inr hn)]
      rfl
    rw [hs]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, nodes] <;>
      change _ ≤ nodes Code.zero + (nodes double + 3) * (Nat.size n + 1) <;>
      rw [Nat.mul_add] <;> omega

/-- A numeric version of the binary-size bound for fully expanded constructor trees. -/
theorem literal_nodes_linear (n : ℕ) : nodes (literal n) ≤ 5 + 107 * Nat.size n := by
  simpa only [show nodes Code.zero = 5 from rfl, show nodes double = 104 from rfl,
    Nat.reduceAdd] using literal_nodes n

/-- Return one exactly when the first word is zero. -/
def isZero : Code := .case (.comp .succ .zero) .zero

@[simp] theorem isZero_eval (v : List ℕ) :
    isZero.eval v = pure [if v.headI = 0 then 1 else 0] := by
  cases h : v.headI <;> simp [isZero, h, Bind.bind]

/-- Return one exactly when the first word is positive. -/
def positive : Code := .case .zero (.comp .succ .zero)

@[simp] theorem positive_eval (v : List ℕ) :
    positive.eval v = pure [if v.headI = 0 then 0 else 1] := by
  cases h : v.headI <;> simp [positive, h, Bind.bind]

/-- Return one exactly when the first word is at most the second. -/
def le : Code := .comp isZero sub

@[simp] theorem le_eval (v : List ℕ) :
    le.eval v = pure [if v.headI ≤ v.tail.headI then 1 else 0] := by
  simp [le, Bind.bind, Nat.sub_eq_zero_iff_le]

/-- Return one exactly when the first word is strictly less than the second. -/
def lt : Code := .comp positive subtractCount

@[simp] theorem lt_eval (v : List ℕ) :
    lt.eval v = pure [if v.headI < v.tail.headI then 1 else 0] := by
  by_cases h : v.headI < v.tail.headI
  · simp [lt, Bind.bind, Nat.sub_eq_zero_iff_le, h, Nat.not_le_of_lt h]
  · simp [lt, Bind.bind, h, Nat.le_of_not_gt h]

/-- Branch on a computed head, preserving all original input words for the selected branch. -/
def ifZero (test yes no : Code) : Code :=
  .comp (.case yes (.comp no .tail)) (.cons test .id)

theorem ifZero_eval (test yes no : Code) (v w : List ℕ) (h : test.eval v = pure w) :
    (ifZero test yes no).eval v = if w.headI = 0 then yes.eval v else no.eval v := by
  cases hw : w.headI <;> simp [ifZero, h, hw, Bind.bind]

/-- Equality test on the first two words, with one for equality and zero otherwise. -/
def eq : Code :=
  .comp isZero (.comp add (tuple [sub, subtractCount]))

@[simp] theorem eq_eval (v : List ℕ) :
    eq.eval v = pure [if v.headI = v.tail.headI then 1 else 0] := by
  have h : (v.headI - v.tail.headI = 0 ∧ v.tail.headI - v.headI = 0) ↔
      v.headI = v.tail.headI := by omega
  simp [eq, tuple, Bind.bind, h]

/-- Repeated-subtraction loop body on `[remainder, divisor, quotient]`. -/
def divisionBody : Code :=
  let stop := tuple [.zero, nth 2, nth 0]
  let step := tuple [literal 1, sub, nth 1, .comp .succ (nth 2)]
  ifZero (nth 1) stop (ifZero (.comp le (tuple [nth 1, nth 0])) stop step)

@[simp] theorem divisionBody_eval (a b q : ℕ) :
    divisionBody.eval [a, b, q] =
      pure (if b = 0 ∨ a < b then [0, q, a] else [1, a - b, b, q + 1]) := by
  cases b with
  | zero => simp [divisionBody, ifZero, tuple, Bind.bind]
  | succ b =>
    by_cases hab : a < b + 1
    · simp [divisionBody, ifZero, tuple, Bind.bind, hab, Nat.not_le_of_gt hab]
    · simp [divisionBody, ifZero, tuple, Bind.bind, hab, Nat.le_of_not_gt hab]

/-- Division loop; zero divisors follow Lean's conventions: quotient zero, remainder the input. -/
def divisionLoop : Code := .fix divisionBody

theorem divisionLoop_eval (a b q : ℕ) :
    divisionLoop.eval [a, b, q] = pure [q + a / b, a % b] := by
  apply Part.eq_some_iff.mpr
  change [q + a / b, a % b] ∈
    PFun.fix (fun v ↦ (divisionBody.eval v).map fun w ↦
      if w.headI = 0 then Sum.inl w.tail else Sum.inr w.tail) [a, b, q]
  induction a using Nat.strong_induction_on generalizing q with
  | h a ih =>
    by_cases stop : b = 0 ∨ a < b
    · refine PFun.mem_fix_iff.mpr (Or.inl ?_)
      rcases stop with hb | hab
      · subst b
        simp
      · simp [hab, Nat.div_eq_of_lt hab, Nat.mod_eq_of_lt hab]
    · have hb : 0 < b := by omega
      have hab : b ≤ a := by omega
      have hd : a / b = (a - b) / b + 1 := Nat.div_eq_sub_div hb hab
      have hm : a % b = (a - b) % b := Nat.mod_eq_sub_mod hab
      refine PFun.mem_fix_iff.mpr (Or.inr ⟨[a - b, b, q + 1], ?_, ?_⟩)
      · simp [stop]
      · simpa only [hd, hm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          ih (a - b) (by omega) (q + 1)

/-- Quotient of the first two words. -/
def div : Code := .comp .head (.comp divisionLoop (tuple [nth 0, nth 1, .zero]))

/-- Remainder of the first two words. -/
def mod : Code := .comp (nth 1) (.comp divisionLoop (tuple [nth 0, nth 1, .zero]))

@[simp] theorem div_eval (v : List ℕ) : div.eval v = pure [v.headI / v.tail.headI] := by
  cases v with
  | nil => simp [div, tuple, Bind.bind, divisionLoop_eval]
  | cons a v =>
    cases v <;> simp [div, tuple, Bind.bind, divisionLoop_eval]

@[simp] theorem mod_eval (v : List ℕ) : mod.eval v = pure [v.headI % v.tail.headI] := by
  cases v with
  | nil => simp [mod, tuple, Bind.bind, divisionLoop_eval]
  | cons a v =>
    cases v <;> simp [mod, tuple, Bind.bind, divisionLoop_eval]

end ConjectureMachines.Compilation.NatCode
