/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.Scalar

/-! # Structured commands compiled to concrete partial-recursive code

States are flat lists of naturals. Fixed-index assignment pads missing earlier registers with
zero. The command language has an independent inductive big-step relation, and its compiler's
actual `Code.eval` is proved equivalent to that relation in both directions.
-/

@[expose] public section

namespace ConjectureMachines.Compilation.Commands

open Turing.ToPartrec
open Scalar (Expr)

set_option backward.isDefEq.respectTransparency false

attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some

/-- Total register update, padding preceding missing registers with zero. -/
def write (index value : Nat) (v : List Nat) : List Nat :=
  (List.range index).map (fun i ↦ v[i]?.getD 0) ++ value :: v.drop (index + 1)

@[simp] theorem write_zero (value : Nat) (v : List Nat) :
    write 0 value v = value :: v.tail := by
  simp [write]

@[simp] theorem write_succ (index value x : Nat) (v : List Nat) :
    write (index + 1) value (x :: v) = x :: write index value v := by
  simp [write, List.range_succ_eq_map, List.map_map, Function.comp_def]

/-- Assignment agrees with ordinary list replacement whenever the register already exists. -/
theorem write_eq_set (index value : Nat) (v : List Nat) (h : index < v.length) :
    write index value v = v.set index value := by
  induction index generalizing v with
  | zero => cases v <;> simp_all
  | succ index ih =>
    cases v with
    | nil => simp at h
    | cons x v => simp only [write_succ, List.set_cons_succ, ih v (by simpa using h)]

/-- Total assignment preserves length in range and extends exactly as far as a new register. -/
theorem write_length (index value : Nat) (v : List Nat) :
    (write index value v).length = max v.length (index + 1) := by
  simp only [write, List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_drop]
  omega

/-- Preserve a fixed prefix of original input registers before a procedure's output. -/
def prefixCode : Nat → Code → Code
  | 0, c => c
  | n + 1, c => prefixCode n (.cons (NatCode.nth n) c)

theorem prefix_eval (n : Nat) (c : Code) (v w : List Nat) (h : c.eval v = pure w) :
    (prefixCode n c).eval v =
      pure ((List.range n).map (fun i ↦ v[i]?.getD 0) ++ w) := by
  induction n generalizing c w with
  | zero => simpa [prefixCode] using h
  | succ n ih =>
    have hc : (Code.cons (NatCode.nth n) c).eval v = pure (v[n]?.getD 0 :: w) := by
      simp [h, Bind.bind]
    simpa [prefixCode, List.range_succ, List.map_append, List.append_assoc] using ih _ _ hc

/-- The compiler for one total register assignment. The expression sees the original state. -/
def assignCode (index : Nat) (expression : Expr) : Code :=
  prefixCode index (.cons (Scalar.compile expression) (NatCode.drop (index + 1)))

@[simp] theorem assignCode_eval (index : Nat) (expression : Expr) (v : List Nat) :
    (assignCode index expression).eval v = pure (write index (Scalar.eval expression v) v) := by
  exact prefix_eval _ _ _ _ (by simp [Scalar.compile_eval, Bind.bind])

/-- A small imperative language over explicit scalar expressions. -/
inductive Cmd where
  | skip
  | assign : Nat → Expr → Cmd
  | push : Expr → Cmd
  | pop
  | seq : Cmd → Cmd → Cmd
  | ifZero : Expr → Cmd → Cmd → Cmd
  | while : Expr → Cmd → Cmd
  deriving DecidableEq

/-- Independent terminating big-step semantics. A positive while-test continues the loop. -/
inductive Exec : Cmd → List Nat → List Nat → Prop where
  | skip (v) : Exec .skip v v
  | assign (i e v) : Exec (.assign i e) v (write i (Scalar.eval e v) v)
  | push (e v) : Exec (.push e) v (Scalar.eval e v :: v)
  | pop (v) : Exec .pop v v.tail
  | seq {a b v u w} : Exec a v u → Exec b u w → Exec (.seq a b) v w
  | if_zero {e a b v w} : Scalar.eval e v = 0 → Exec a v w → Exec (.ifZero e a b) v w
  | if_pos {e a b v w} : Scalar.eval e v ≠ 0 → Exec b v w → Exec (.ifZero e a b) v w
  | while_zero {e body v} : Scalar.eval e v = 0 → Exec (.while e body) v v
  | while_pos {e body v u w} : Scalar.eval e v ≠ 0 → Exec body v u →
      Exec (.while e body) u w → Exec (.while e body) v w

/-- A loop body emits an exit tag followed by a state, or a continuation tag and updated state. -/
def loopBody (test : Expr) (body : Code) : Code :=
  NatCode.ifZero (Scalar.compile test) .zero' (.cons (NatCode.literal 1) body)

theorem loopBody_eval (test : Expr) (body : Code) (v : List Nat) :
    (loopBody test body).eval v = if Scalar.eval test v = 0 then pure (0 :: v)
      else (body.eval v).map (fun w ↦ 1 :: w) := by
  rw [loopBody, NatCode.ifZero_eval _ _ _ _ _ (Scalar.compile_eval test v)]
  by_cases h : Scalar.eval test v = 0 <;> simp [h, Bind.bind, Part.bind_some_eq_map]

/-- Partial state transition whose fixpoint is exactly the compiled while loop. -/
def loopStep (test : Expr) (body : Code) (v : List Nat) : Part (List Nat ⊕ List Nat) :=
  if Scalar.eval test v = 0 then pure (.inl v) else (body.eval v).map Sum.inr

theorem loopBody_step (test : Expr) (body : Code) (v : List Nat) :
    ((loopBody test body).eval v).map (fun w ↦
      if w.headI = 0 then Sum.inl w.tail else Sum.inr w.tail) = loopStep test body v := by
  rw [loopBody_eval]
  by_cases h : Scalar.eval test v = 0 <;> simp [loopStep, h, Part.map_map, Function.comp_def]

/-- Actual compiler to mathlib's seven-constructor code basis. -/
def compile : Cmd → Code
  | .skip => .id
  | .assign i e => assignCode i e
  | .push e => .cons (Scalar.compile e) .id
  | .pop => .tail
  | .seq a b => .comp (compile b) (compile a)
  | .ifZero e a b => NatCode.ifZero (Scalar.compile e) (compile a) (compile b)
  | .while e body => .fix (loopBody e (compile body))

theorem compile_while_eval (test : Expr) (body : Cmd) :
    (compile (.while test body)).eval = PFun.fix (loopStep test (compile body)) := by
  simp only [compile, Code.fix_eval, loopBody_step]

/-- Every terminating source execution is an actual terminating execution of its concrete code. -/
theorem Exec.sound {command : Cmd} {v w : List Nat} (execution : Exec command v w) :
    w ∈ (compile command).eval v := by
  induction execution with
  | skip v => simp [compile]
  | assign i e v => simp [compile]
  | push e v => simp [compile, Scalar.compile_eval, Bind.bind]
  | pop v => simp [compile]
  | seq first second ih₁ ih₂ =>
    simp only [compile, Code.comp_eval, Bind.bind]
    exact Part.mem_bind_iff.mpr ⟨_, ih₁, ih₂⟩
  | if_zero h execution ih =>
    rw [compile, NatCode.ifZero_eval _ _ _ _ _ (Scalar.compile_eval _ _)]
    simpa [h] using ih
  | if_pos h execution ih =>
    rw [compile, NatCode.ifZero_eval _ _ _ _ _ (Scalar.compile_eval _ _)]
    simpa [h] using ih
  | while_zero h =>
    rw [compile_while_eval]
    exact PFun.fix_stop (by simp [loopStep, h])
  | @while_pos e body v u w h first rest ih₁ ih₂ =>
    rw [compile_while_eval] at ih₂ ⊢
    refine PFun.mem_fix_iff.mpr (Or.inr ⟨u, ?_, ih₂⟩)
    simpa only [loopStep, h, ↓reduceIte] using
      (Part.mem_map_iff Sum.inr).mpr ⟨u, ih₁, rfl⟩

/-- Every actual terminating code execution has an independent source execution derivation. -/
theorem compile_complete (command : Cmd) (v w : List Nat)
    (execution : w ∈ (compile command).eval v) : Exec command v w := by
  induction command generalizing v w with
  | skip =>
    have h : w = v := by simpa [compile] using execution
    subst w
    exact .skip v
  | assign i e =>
    have h : w = write i (Scalar.eval e v) v := by simpa [compile] using execution
    subst w
    exact .assign i e v
  | push e =>
    have h : w = Scalar.eval e v :: v := by
      simpa [compile, Scalar.compile_eval, Bind.bind] using execution
    subst w
    exact .push e v
  | pop =>
    have h : w = v.tail := by simpa [compile] using execution
    subst w
    exact .pop v
  | seq a b ha hb =>
    simp only [compile, Code.comp_eval, Bind.bind, Part.mem_bind_iff] at execution
    obtain ⟨u, h₁, h₂⟩ := execution
    exact .seq (ha _ _ h₁) (hb _ _ h₂)
  | ifZero e a b ha hb =>
    rw [compile, NatCode.ifZero_eval _ _ _ _ _ (Scalar.compile_eval _ _)] at execution
    by_cases h : Scalar.eval e v = 0
    · exact .if_zero h (ha _ _ (by simpa [h] using execution))
    · exact .if_pos h (hb _ _ (by simpa [h] using execution))
  | «while» e body hb =>
    rw [compile_while_eval] at execution
    refine PFun.fixInduction' execution (fun state exit ↦ ?_) (fun state next _ step ih ↦ ?_)
    · by_cases h : Scalar.eval e state = 0
      · have hw : w = state := by simpa [loopStep, h] using exit
        subst w
        exact .while_zero h
      · simp [loopStep, h, Part.mem_map_iff] at exit
    · by_cases h : Scalar.eval e state = 0
      · simp [loopStep, h] at step
      · have hn : next ∈ (compile body).eval state := by
          simpa [loopStep, h, Part.mem_map_iff] using step
        exact .while_pos h (hb _ _ hn) ih

/-- Exact terminating semantics of the concrete compiler, in both directions. -/
theorem exec_iff_eval (command : Cmd) (v w : List Nat) :
    Exec command v w ↔ w ∈ (compile command).eval v :=
  ⟨Exec.sound, compile_complete command v w⟩

/-- A terminating execution determines the whole exact partial evaluation result. -/
theorem Exec.eval_eq {command : Cmd} {v w : List Nat} (execution : Exec command v w) :
    (compile command).eval v = pure w :=
  Part.eq_some_iff.mpr execution.sound

/-- A source command terminates exactly when its compiled partial evaluation is defined. -/
theorem terminates_iff_dom (command : Cmd) (v : List Nat) :
    (∃ w, Exec command v w) ↔ ((compile command).eval v).Dom := by
  simp only [exec_iff_eval, Part.dom_iff_mem]

/-- Terminating source execution is deterministic, as is the compiled partial function. -/
theorem Exec.deterministic {command : Cmd} {v w₁ w₂ : List Nat}
    (first : Exec command v w₁) (second : Exec command v w₂) : w₁ = w₂ :=
  Part.mem_unique first.sound second.sound

/-- A loop whose test never vanishes has no terminating code execution, for any body. -/
theorem while_never_zero (test : Expr) (body : Cmd)
    (nonzero : ∀ state, Scalar.eval test state ≠ 0) (v : List Nat) :
    (compile (.while test body)).eval v = Part.none := by
  apply Part.ext
  intro w
  simp only [Part.notMem_none, iff_false]
  intro execution
  rw [compile_while_eval] at execution
  refine PFun.fixInduction' execution (fun state exit ↦ ?_) (fun _ _ _ _ ih ↦ ih)
  simp [loopStep, nonzero state, Part.mem_map_iff] at exit

/-- Constant-true while loops diverge, including when the body itself may diverge. -/
theorem while_true_eval (body : Cmd) (v : List Nat) :
    (compile (.while (.literal 1) body)).eval v = Part.none :=
  while_never_zero _ _ (by intro state; simp [Scalar.eval]) v

/-- The independent source relation also excludes any finite constant-true loop execution. -/
theorem not_exec_while_true (body : Cmd) (v w : List Nat) :
    ¬Exec (.while (.literal 1) body) v w := by
  rw [exec_iff_eval, while_true_eval]
  exact Part.notMem_none w

end ConjectureMachines.Compilation.Commands
