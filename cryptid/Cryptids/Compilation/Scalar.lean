/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.NatCode
public import Cryptids.Compilation.ListCode

/-! # Scalar expressions with a concrete compiler

Environments are lists of natural numbers. The bounded fold passes its iteration index and
accumulator before the original environment. Every constructor has exact `Code.eval` semantics;
this compiler does not invoke a Lean evaluator or assume a computability oracle.
-/

@[expose] public section

namespace ConjectureMachines.Compilation.Scalar

open Turing.ToPartrec

inductive Expr where
  | literal : Nat → Expr
  | input : Nat → Expr
  | lookup : Expr → Expr
  | drop : Nat → Expr → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr
  | mod : Expr → Expr → Expr
  | eq : Expr → Expr → Expr
  | le : Expr → Expr → Expr
  | lt : Expr → Expr → Expr
  | ifZero : Expr → Expr → Expr → Expr
  | fold : Expr → Expr → Expr → Expr
  deriving DecidableEq

/-- Total source semantics, including out-of-range zero-valued reads. -/
def eval : Expr → List Nat → Nat
  | .literal n, _ => n
  | .input n, v => v[n]?.getD 0
  | .lookup i, v => v[eval i v]?.getD 0
  | .drop n expression, v => eval expression (v.drop n)
  | .add a b, v => eval a v + eval b v
  | .sub a b, v => eval a v - eval b v
  | .mul a b, v => eval a v * eval b v
  | .div a b, v => eval a v / eval b v
  | .mod a b, v => eval a v % eval b v
  | .eq a b, v => if eval a v = eval b v then 1 else 0
  | .le a b, v => if eval a v ≤ eval b v then 1 else 0
  | .lt a b, v => if eval a v < eval b v then 1 else 0
  | .ifZero c a b, v => if eval c v = 0 then eval a v else eval b v
  | .fold n z step, v =>
    Nat.rec (eval z v) (fun i a ↦ eval step (i :: a :: v)) (eval n v)

/-- Compile a binary primitive, evaluating both operands in the original environment. -/
def binary (op a b : Code) : Code := .comp op (NatCode.tuple [a, b])

/-- Actual syntax in the seven-constructor `ToPartrec.Code` basis. -/
def compile : Expr → Code
  | .literal n => NatCode.literal n
  | .input n => NatCode.nth n
  | .lookup i => .comp ListCode.get (.cons (compile i) .id)
  | .drop n expression => .comp (compile expression) (NatCode.drop n)
  | .add a b => binary NatCode.add (compile a) (compile b)
  | .sub a b => binary NatCode.sub (compile a) (compile b)
  | .mul a b => binary NatCode.mul (compile a) (compile b)
  | .div a b => binary NatCode.div (compile a) (compile b)
  | .mod a b => binary NatCode.mod (compile a) (compile b)
  | .eq a b => binary NatCode.eq (compile a) (compile b)
  | .le a b => binary NatCode.le (compile a) (compile b)
  | .lt a b => binary NatCode.lt (compile a) (compile b)
  | .ifZero c a b => NatCode.ifZero (compile c) (compile a) (compile b)
  | .fold n z step =>
    .comp (Code.prec (compile z) (compile step)) (.cons (compile n) .id)

set_option backward.isDefEq.respectTransparency false

attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some

/-- Every source expression agrees with the actual partial-function semantics of its code. -/
theorem compile_eval (expression : Expr) (v : List Nat) :
    (compile expression).eval v = pure [eval expression v] := by
  induction expression generalizing v with
  | literal n => exact NatCode.literal_eval n v
  | input n => exact NatCode.nth_eval n v
  | lookup i ih =>
    simp only [compile, eval, Code.comp_eval, Code.cons_eval, ih, Code.id_eval,
      Bind.bind, Part.bind_some, List.headI_cons, pure]
    exact ListCode.get_eval _ _
  | drop n expression ih => simp [compile, eval, ih, Bind.bind, Part.bind_some]
  | add a b ha hb => simp [compile, eval, binary, NatCode.tuple, ha, hb, Bind.bind, Part.bind_some]
  | sub a b ha hb => simp [compile, eval, binary, NatCode.tuple, ha, hb, Bind.bind, Part.bind_some]
  | mul a b ha hb => simp [compile, eval, binary, NatCode.tuple, ha, hb, Bind.bind, Part.bind_some]
  | div a b ha hb => simp [compile, eval, binary, NatCode.tuple, ha, hb, Bind.bind, Part.bind_some]
  | mod a b ha hb => simp [compile, eval, binary, NatCode.tuple, ha, hb, Bind.bind, Part.bind_some]
  | eq a b ha hb => simp [compile, eval, binary, NatCode.tuple, ha, hb, Bind.bind, Part.bind_some]
  | le a b ha hb => simp [compile, eval, binary, NatCode.tuple, ha, hb, Bind.bind, Part.bind_some]
  | lt a b ha hb => simp [compile, eval, binary, NatCode.tuple, ha, hb, Bind.bind, Part.bind_some]
  | ifZero c a b hc ha hb =>
    rw [compile, NatCode.ifZero_eval _ _ _ _ _ (hc v)]
    by_cases h : eval c v = 0 <;> simp [eval, h, ha, hb]
  | fold n z step hn hz hs =>
    simp only [compile, Code.comp_eval, Code.cons_eval, hn, Code.id_eval, Bind.bind,
      Part.bind_some, Part.pure_eq_some, List.headI_cons]
    exact NatCode.prec_eval _ _ _ _ hz (fun a b w => hs (a :: b :: w)) _ _

end ConjectureMachines.Compilation.Scalar
