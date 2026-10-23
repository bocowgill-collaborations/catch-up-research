/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see the repository LICENSE.
-/
import CatchUp.Search
import Mathlib.Computability.TuringMachine.Config

set_option backward.isDefEq.respectTransparency false

/-!
# Explicit source-program components

All program values in this file are built from `Turing.ToPartrec.Code` constructors. In
particular, none has a primitive operation that evaluates a Catch-Up game. The concrete
`program` searches for a counterexample and is proved to halt exactly when the conjecture fails.
-/

namespace CatchUp.Machine.Program

open Turing.ToPartrec

/-- Numeric outcome order used by the list interpreter: loss < draw < win. -/
def outcomeNumber : Outcome → ℕ
  | .loss => 0
  | .draw => 1
  | .win => 2

/-- Negate a numeric outcome; inputs outside `0,1,2` default to `0`. -/
def negateNumber : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | _ => 0

/-- The raw numeric negation agrees with changing player perspective. -/
theorem negate_number_outcome (outcome : Outcome) :
    negateNumber (outcomeNumber outcome) = outcomeNumber outcome.neg := by
  cases outcome <;> rfl

/-- The maximum of numeric outcomes agrees with the reference ternary fold. -/
theorem outcome_number_best (outcomes : List Outcome) :
    outcomeNumber (Outcome.best outcomes) =
      (outcomes.map outcomeNumber).foldl max 0 := by
  let combine : Outcome → Outcome → Outcome := fun
    | .win, _ => .win
    | _, .win => .win
    | .draw, _ => .draw
    | _, .draw => .draw
    | _, _ => .loss
  have hfold (acc : Outcome) :
      outcomeNumber (outcomes.foldl combine acc) =
        (outcomes.map outcomeNumber).foldl max (outcomeNumber acc) := by
    induction outcomes generalizing acc with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.foldl_cons, List.map_cons]
        rw [ih]
        congr 1
        cases acc <;> cases x <;> rfl
  exact hfold .loss

/-- A finite-game evaluator over raw lists and naturals, with explicit recursion depth. -/
def evalFuel : ℕ → List ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, remaining, deficit =>
      if remaining = [] then
        if deficit = 0 then 1 else 0
      else if remaining.sum < deficit then 0
      else
        (remaining.map fun x ↦
          let child := evalFuel fuel (remaining.erase x)
            (if x < deficit then deficit - x else x - deficit)
          if x < deficit then child else negateNumber child).foldl max 0

/-- Erasing one available counter has the expected set meaning for duplicate-free lists. -/
theorem to_finset_erase (remaining : List ℕ) (hnodup : remaining.Nodup) (x : ℕ) :
    (remaining.erase x).toFinset = remaining.toFinset.erase x := by
  ext y
  simp [hnodup.mem_erase_iff]

/-- `Outcome.best` depends only on which outcomes occur. -/
theorem best_eq_of_mem_iff (left right : List Outcome)
    (hmem : ∀ outcome, outcome ∈ left ↔ outcome ∈ right) :
    Outcome.best left = Outcome.best right := by
  have hloss : Outcome.best left ≠ .loss ↔ Outcome.best right ≠ .loss := by
    simp only [Outcome.best_ne_loss_iff]
    exact exists_congr fun o ↦ and_congr_left fun _ ↦ hmem o
  have hwin : Outcome.best left ≠ .win ↔ Outcome.best right ≠ .win := by
    simp only [Outcome.best_ne_win_iff]
    constructor <;> intro h o ho
    · exact h o ((hmem o).mpr ho)
    · exact h o ((hmem o).mp ho)
  cases hl : Outcome.best left <;> cases hr : Outcome.best right <;> simp_all

/-- With more fuel than available counters, the raw evaluator is exactly reference minimax. -/
theorem eval_fuel_eq_value (fuel : ℕ) (remaining : List ℕ) (deficit : ℕ)
    (hnodup : remaining.Nodup) (hfuel : remaining.length < fuel) :
    evalFuel fuel remaining deficit =
      outcomeNumber (Position.value ⟨remaining.toFinset, deficit⟩) := by
  induction fuel generalizing remaining deficit with
  | zero => omega
  | succ fuel ih =>
      rw [evalFuel, Position.value.eq_def]
      by_cases hempty : remaining = []
      · subst remaining
        simp only [List.toFinset_nil, ↓reduceIte]
        split_ifs <;> rfl
      · simp only [hempty, ↓reduceIte, List.toFinset_eq_empty_iff]
        have hsum : remaining.toFinset.sum (fun x ↦ x) = remaining.sum := by
          simpa using List.sum_toFinset (fun x : ℕ ↦ x) hnodup
        rw [hsum]
        by_cases hterminal : remaining.sum < deficit
        · simp [hterminal, outcomeNumber]
        · simp only [hterminal, ↓reduceIte]
          let moves := (remaining.toFinset.attach.toList.map fun x ↦
            if x.1 < deficit then
              Position.value (Position.afterPick ⟨remaining.toFinset, deficit⟩ x.1)
            else
              (Position.value (Position.afterPick ⟨remaining.toFinset, deficit⟩ x.1)).neg)
          let outcomes := remaining.map fun x ↦
            if x < deficit then
              Position.value (Position.afterPick ⟨remaining.toFinset, deficit⟩ x)
            else
              (Position.value (Position.afterPick ⟨remaining.toFinset, deficit⟩ x)).neg
          have hbest : Outcome.best outcomes = Outcome.best moves := by
            apply best_eq_of_mem_iff
            intro outcome
            simp only [outcomes, moves, List.mem_map, Finset.mem_toList, Finset.mem_attach,
              true_and]
            constructor
            · rintro ⟨x, hx, hvalue⟩
              exact ⟨⟨x, List.mem_toFinset.mpr hx⟩, hvalue⟩
            · rintro ⟨⟨x, hx⟩, hvalue⟩
              exact ⟨x, List.mem_toFinset.mp hx, hvalue⟩
          change _ = outcomeNumber (Outcome.best moves)
          rw [← hbest, outcome_number_best]
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro x hx
          have hlen : (remaining.erase x).length < fuel := by
            have := List.length_erase_add_one hx
            omega
          have hchild := ih (remaining.erase x)
            (if x < deficit then deficit - x else x - deficit) (hnodup.erase x) hlen
          rw [hchild, to_finset_erase remaining hnodup]
          dsimp [outcomes, Position.afterPick]
          split_ifs with hxlt
          · rfl
          · exact negate_number_outcome _

/-- A raw-list exact test for interval counterexamples. -/
def intervalTest (n : ℕ) : ℕ :=
  if Even (n * (n + 1) / 2) ∧ evalFuel (n + 1) (List.range' 1 n) 0 ≠ 1 then 0 else 1

/-- The list recurrence has precisely the test semantics required by the outer source loop. -/
theorem interval_test_eq (n : ℕ) :
    intervalTest n = if Search.isCounterexample n then 0 else 1 := by
  have heval := eval_fuel_eq_value (n + 1) (List.range' 1 n) 0
    List.nodup_range' (by simp)
  rw [List.toFinset_range'_1_1] at heval
  rw [initial_position_value_eq] at heval
  have houtcome (o : Outcome) : outcomeNumber o ≠ 1 ↔ o ≠ .draw := by
    cases o <;> simp [outcomeNumber]
  simp only [intervalTest, heval, houtcome, Search.isCounterexample,
    eval_initial_eq_value, Bool.and_eq_true, decide_eq_true_eq]

/-- A literal natural number, represented by an explicit constructor tree. -/
def literal : ℕ → Code
  | 0 => .zero
  | n + 1 => .comp .succ (literal n)

@[simp]
theorem literal_eval (n : ℕ) (v : List ℕ) : (literal n).eval v = pure [n] := by
  induction n with
  | zero => simp [literal]
  | succ n ih => simp [literal, ih]

/-- Explicit numeric outcome negation, implemented using two zero/successor cases. -/
def negateCode : Code := .case (literal 2) (.case (literal 1) .zero)

/-- This is a concrete compiled operation of the minimax evaluator. -/
theorem negate_code_eval (n : ℕ) (v : List ℕ) :
    negateCode.eval (n :: v) = pure [negateNumber n] := by
  cases n with
  | zero => simp [negateCode, negateNumber]
  | succ n => cases n <;> simp [negateCode, negateNumber]

/-- Addition with an unchanged trailing list, using only a decrement/increment loop. -/
def addCode : Code :=
  .fix (.case .zero'
    (.cons (literal 1) (.cons .head
      (.cons (.comp .succ .tail) (.comp .tail .tail)))))

/-- The arithmetic loop preserves the following interpreter state verbatim. -/
theorem add_code_eval (a b : ℕ) (v : List ℕ) :
    addCode.eval (a :: b :: v) = pure ((a + b) :: v) := by
  let body : List ℕ → Part (List ℕ ⊕ List ℕ) := fun v ↦
    ((Code.case Code.zero'
      (.cons (literal 1) (.cons .head
        (.cons (.comp .succ .tail) (.comp .tail .tail))))).eval v).map fun w ↦
      if w.headI = 0 then Sum.inl w.tail else Sum.inr w.tail
  have hzero (b : ℕ) : body (0 :: b :: v) = pure (Sum.inl (b :: v)) := by simp [body]
  have hsucc (a b : ℕ) : body ((a + 1) :: b :: v) =
      pure (Sum.inr (a :: (b + 1) :: v)) := by simp [body]
  change PFun.fix body (a :: b :: v) = pure ((a + b) :: v)
  apply Part.eq_some_iff.mpr
  induction a generalizing b with
  | zero => exact PFun.mem_fix_iff.mpr (Or.inl (by simp [hzero]))
  | succ a ih =>
      refine PFun.mem_fix_iff.mpr (Or.inr ⟨a :: (b + 1) :: v, ?_, ?_⟩)
      · simp [hsucc]
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (b + 1)

/-- Iterate a state-transforming code a supplied number of times. -/
def repeatCode (step : Code) : Code :=
  .fix (.case .zero' (.cons (literal 1) (.cons .head (.comp step .tail))))

/-- A direct correctness rule for counted iteration, with no existence-to-code extraction. -/
theorem repeat_code_eval (step : Code) (f : List ℕ → List ℕ)
    (hstep : ∀ v, step.eval v = pure (f v)) (n : ℕ) (v : List ℕ) :
    (repeatCode step).eval (n :: v) = pure (f^[n] v) := by
  let body : List ℕ → Part (List ℕ ⊕ List ℕ) := fun v ↦
    ((Code.case Code.zero'
      (.cons (literal 1) (.cons .head (.comp step .tail)))).eval v).map fun w ↦
      if w.headI = 0 then Sum.inl w.tail else Sum.inr w.tail
  have hzero (v : List ℕ) : body (0 :: v) = pure (Sum.inl v) := by simp [body]
  have hsucc (n : ℕ) (v : List ℕ) : body ((n + 1) :: v) =
      pure (Sum.inr (n :: f v)) := by simp [body, hstep]
  change PFun.fix body (n :: v) = pure (f^[n] v)
  apply Part.eq_some_iff.mpr
  induction n generalizing v with
  | zero => exact PFun.mem_fix_iff.mpr (Or.inl (by simp [hzero]))
  | succ n ih =>
      refine PFun.mem_fix_iff.mpr (Or.inr ⟨n :: f v, ?_, ?_⟩)
      · simp [hsucc]
      · simpa only [Function.iterate_succ_apply] using ih (f v)

/-- Total list-state addition, defaulting missing numeric inputs to zero. -/
def addState (v : List ℕ) : List ℕ :=
  (v.headI + v.tail.headI) :: v.tail.tail

/-- Normalize two arguments and run the concrete state-preserving addition code. -/
def addTotalCode : Code :=
  .comp addCode (.cons .head (.cons (.comp .head .tail) (.comp .tail .tail)))

@[simp]
theorem add_total_code_eval (v : List ℕ) : addTotalCode.eval v = pure (addState v) := by
  simp [addTotalCode, add_code_eval, addState]

/-- Sum a list with a supplied length, leaving any following interpreter state untouched. -/
def sumCode : Code := repeatCode addTotalCode

/-- The counted state transformation really adds exactly the listed counters. -/
theorem iterate_add_state (remaining : List ℕ) (acc : ℕ) (v : List ℕ) :
    addState^[remaining.length] (acc :: remaining ++ v) = (acc + remaining.sum) :: v := by
  induction remaining generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.length_cons, Function.iterate_succ_apply, List.cons_append,
        addState, List.headI_cons, List.tail_cons]
      simpa [List.cons_append, Nat.add_assoc] using ih (acc + x)

/-- A concrete compiled list sum, one of the terminal-test operations of minimax. -/
theorem sum_code_eval (remaining : List ℕ) (acc : ℕ) (v : List ℕ) :
    sumCode.eval (remaining.length :: acc :: remaining ++ v) =
      pure ((acc + remaining.sum) :: v) := by
  simp only [sumCode, List.cons_append]
  rw [repeat_code_eval addTotalCode addState add_total_code_eval]
  simpa only [List.cons_append] using congrArg (fun w ↦ (pure w : Part (List ℕ)))
    (iterate_add_state remaining acc v)

/-- Decrement the leading state register while retaining the following registers. -/
def predStateCode : Code := .cons .pred .tail

/-- Subtraction by repeated predecessor, followed by the original trailing registers. -/
def subCode : Code :=
  .comp (repeatCode predStateCode)
    (.cons (.comp .head .tail) (.cons .head (.comp .tail .tail)))

/-- The concrete subtraction code uses truncated natural subtraction. -/
theorem sub_code_eval (a b : ℕ) (v : List ℕ) :
    subCode.eval (a :: b :: v) = pure ((a - b) :: v) := by
  have hstep (v : List ℕ) :
      predStateCode.eval v = pure (v.headI.pred :: v.tail) := by simp [predStateCode]
  have hiterate (b a : ℕ) :
      (fun v : List ℕ ↦ v.headI.pred :: v.tail)^[b] (a :: v) = (a - b) :: v := by
    induction b generalizing a with
    | zero => simp
    | succ b ih =>
        rw [Function.iterate_succ_apply]
        simpa [Nat.sub_sub, Nat.pred_eq_sub_one, Nat.add_comm] using ih a.pred
  simp only [subCode, Code.comp_eval, Code.cons_eval, Code.head_eval, Code.tail_eval,
    Part.pure_eq_some, Bind.bind, Part.bind_some, List.headI_cons, List.tail_cons]
  rw [repeat_code_eval predStateCode _ hstep, hiterate]
  rfl

/-- Explicit maximum of two outcome registers, retaining trailing state. -/
def maxCode : Code :=
  .comp addCode (.comp subCode
    (.cons .head (.cons (.comp .head .tail) .tail)))

/-- Numeric minimax combination is compiled to the source basis as well. -/
theorem max_code_eval (a b : ℕ) (v : List ℕ) :
    maxCode.eval (a :: b :: v) = pure (max a b :: v) := by
  simp [maxCode, sub_code_eval, add_code_eval, Nat.sub_add_eq_max]

/-- The counted range-construction step retains the former counter on the list. -/
def rangeStepCode : Code := .cons .pred .id

/-- Construct the raw interval list `[1, ..., n]` from its endpoint. -/
def rangeCode : Code :=
  .comp .tail (.comp (repeatCode rangeStepCode) (.cons .head .head))

/-- The explicit counted loop builds the same ascending list as `List.range'`. -/
theorem iterate_range_state (n : ℕ) (v : List ℕ) :
    (fun w : List ℕ ↦ w.headI.pred :: w)^[n] (n :: v) =
      (0 :: List.range' 1 n) ++ v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      simp only [List.headI_cons, Nat.pred_succ]
      rw [ih]
      simp [List.range'_concat, List.append_assoc, Nat.add_comm]

/-- Initial interval construction is already a concrete program in the source basis. -/
theorem range_code_eval (n : ℕ) (v : List ℕ) :
    rangeCode.eval (n :: v) = pure (List.range' 1 n) := by
  have hstep (w : List ℕ) :
      rangeStepCode.eval w = pure (w.headI.pred :: w) := by simp [rangeStepCode]
  simp only [rangeCode, Code.comp_eval, Code.cons_eval, Code.head_eval,
    Part.pure_eq_some, Bind.bind, Part.bind_some, List.headI_cons]
  rw [repeat_code_eval rangeStepCode _ hstep, iterate_range_state]
  simp

/-- Toggle a parity register; the register is initialized at zero. -/
def parityStepCode : Code := .case (literal 1) .zero

/-- Compute the parity of the leading natural using a counted toggle loop. -/
def parityCode : Code :=
  .comp (repeatCode parityStepCode) (.cons .head .zero)

/-- The parity program has exact natural remainder semantics. -/
theorem parity_code_eval (n : ℕ) (v : List ℕ) :
    parityCode.eval (n :: v) = pure [n % 2] := by
  let toggle : List ℕ → List ℕ := fun w ↦ [if w.headI = 0 then 1 else 0]
  have hstep (w : List ℕ) : parityStepCode.eval w = pure (toggle w) := by
    cases h : w.headI <;> simp [parityStepCode, toggle, Code.case_eval, h]
  have hiter (n : ℕ) : toggle^[n] [0] = [n % 2] := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        dsimp [toggle]
        congr 1
        have hlt := Nat.mod_lt n (by decide : 0 < 2)
        split_ifs <;> omega
  simp only [parityCode, Code.comp_eval, Code.cons_eval, Code.head_eval, Code.zero_eval,
    Part.pure_eq_some, Bind.bind, Part.bind_some, List.headI_cons]
  rw [repeat_code_eval parityStepCode toggle hstep, hiter]
  rfl

/-- Summing the raw interval gives precisely the triangular expression in the conjecture. -/
theorem range_sum_eq_triangle (n : ℕ) :
    (List.range' 1 n).sum = n * (n + 1) / 2 := by
  have htwice (n : ℕ) : (List.range' 1 n).sum * 2 = n * (n + 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
        simp only [List.range'_concat, List.sum_append, List.sum_cons, List.sum_nil,
          Nat.one_mul, Nat.add_zero]
        nlinarith
  rw [← htwice, Nat.mul_div_cancel _ (by decide : 0 < 2)]

/-- Concrete compilation of the triangular-parity eligibility condition. -/
def eligibilityCode : Code :=
  .comp parityCode (.comp sumCode (.cons .head (.cons .zero rangeCode)))

/-- No division, multiplication, set operation, or game oracle occurs in this program. -/
theorem eligibility_code_eval (n : ℕ) (v : List ℕ) :
    eligibilityCode.eval (n :: v) = pure [(n * (n + 1) / 2) % 2] := by
  simp only [eligibilityCode, Code.comp_eval, Code.cons_eval, Code.head_eval, Code.zero_eval,
    range_code_eval, Part.pure_eq_some, Bind.bind, Part.bind_some, List.headI_cons]
  have hsum := sum_code_eval (List.range' 1 n) 0 []
  simp only [List.length_range', List.append_nil, Nat.zero_add] at hsum
  rw [hsum]
  simp only [Part.pure_eq_some, Part.bind_some, parity_code_eval, range_sum_eq_triangle]

/-- A zero eligibility result is exactly the reference arithmetic eligibility condition. -/
theorem eligibility_zero_iff (n : ℕ) :
    (n * (n + 1) / 2) % 2 = 0 ↔ Even (n * (n + 1) / 2) := by
  rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]

/-- Swap the first two natural registers, retaining every trailing register. -/
def swapCode : Code :=
  .cons (.comp .head .tail) (.cons .head (.comp .tail .tail))

@[simp]
theorem swap_code_eval (a b : ℕ) (v : List ℕ) :
    swapCode.eval (a :: b :: v) = pure (b :: a :: v) := by simp [swapCode]

/-- Convert a natural register to the `0`/`1` indicator of strict positivity. -/
def positiveCode : Code := .case .zero' (.cons (literal 1) .tail)

@[simp]
theorem positive_code_eval (n : ℕ) (v : List ℕ) :
    positiveCode.eval (n :: v) = pure ((if n = 0 then 0 else 1) :: v) := by
  cases n <;> simp [positiveCode]

/-- Compare two registers by subtracting in the opposite order. -/
def lessCode : Code := .comp positiveCode (.comp subCode swapCode)

/-- The strict comparison used for continuing the same turn is compiled explicitly. -/
theorem less_code_eval (a b : ℕ) (v : List ℕ) :
    lessCode.eval (a :: b :: v) = pure ((if a < b then 1 else 0) :: v) := by
  simp only [lessCode, Code.comp_eval, swap_code_eval, Part.pure_eq_some, Bind.bind,
    Part.bind_some, sub_code_eval]
  simp only [Part.pure_eq_some, positive_code_eval]
  congr 2
  split_ifs <;> omega

/-- Compile the next deficit by summing the two opposite truncated differences. -/
def differenceCode : Code :=
  .comp addCode (.cons subCode (.comp subCode swapCode))

/-- The exact normalized score update is a concrete source program. -/
theorem difference_code_eval (picked deficit : ℕ) (v : List ℕ) :
    differenceCode.eval (picked :: deficit :: v) =
      pure ((if picked < deficit then deficit - picked else picked - deficit) :: v) := by
  simp only [differenceCode, Code.comp_eval, Code.cons_eval, swap_code_eval, sub_code_eval,
    Part.pure_eq_some, Bind.bind, Part.bind_some, List.headI_cons, add_code_eval]
  congr 2
  split_ifs <;> omega

/-- Dispatch code: `0` means nonterminal, `1` terminal loss, `2` terminal draw. -/
def terminalCode : Code :=
  .case (.case (literal 2) (literal 1))
    (.comp lessCode (.cons
      (.comp sumCode (.cons .succ (.comp .zero' (.comp .tail .tail))))
      (.comp .head .tail)))

/-- The finite game's terminal conditions, including the early insufficient-sum rule. -/
def terminalNumber (remaining : List ℕ) (deficit : ℕ) : ℕ :=
  if remaining = [] then if deficit = 0 then 2 else 1
  else if remaining.sum < deficit then 1 else 0

/-- Terminal detection executes only comparisons, cases, and the compiled list-sum loop. -/
theorem terminal_code_eval (remaining : List ℕ) (deficit : ℕ) :
    terminalCode.eval (remaining.length :: deficit :: remaining) =
      pure [terminalNumber remaining deficit] := by
  cases remaining with
  | nil => cases deficit <;> simp [terminalCode, terminalNumber]
  | cons x xs =>
      have hsum := sum_code_eval (x :: xs) 0 []
      simp only [List.append_nil, Nat.zero_add] at hsum
      simp only [terminalCode, Code.case_eval, List.headI_cons, List.length_cons,
        List.tail_cons, Code.comp_eval, Code.cons_eval, Code.succ_eval, Code.tail_eval,
        Code.zero'_eval, Code.head_eval, Part.pure_eq_some, Bind.bind, Part.bind_some,
        List.headI_cons]
      simp only [List.length_cons, Nat.succ_eq_add_one] at hsum ⊢
      rw [hsum]
      simp [less_code_eval, terminalNumber]

/-- Drop a counted prefix of the remaining list-state. -/
def dropCode : Code := repeatCode .tail

/-- List addressing is a concrete counted traversal in the source basis. -/
theorem drop_code_eval (n : ℕ) (v : List ℕ) :
    dropCode.eval (n :: v) = pure (v.drop n) := by
  have hiter (n : ℕ) (v : List ℕ) : List.tail^[n] v = v.drop n := by
    induction n generalizing v with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply, ih, List.drop_tail]
  rw [dropCode, repeat_code_eval .tail List.tail (fun _ ↦ rfl), hiter]

/-- Fetch a list register at a supplied offset, defaulting beyond the list to zero. -/
def nthCode : Code := .comp .head dropCode

/-- The element-fetch operation has exact list semantics. -/
theorem nth_code_eval (n : ℕ) (v : List ℕ) :
    nthCode.eval (n :: v) = pure [(v.drop n).headI] := by
  simp [nthCode, drop_code_eval]

/-- Copy the first `n` entries in front of the original list, retaining it as continuation data. -/
def copyPrefixBody : Code :=
  .case (.comp .zero' .tail)
    (.cons (literal 1) (.cons .head (.cons (.comp .succ .tail)
      (.cons (.comp nthCode addCode) (.comp .tail .tail)))))

/-- Initialize a backwards copying loop with an empty output prefix. -/
def copyPrefixCode : Code :=
  .comp (.fix copyPrefixBody) (.cons .head (.comp .zero' .tail))

/-- The loop copies without an oracle, while preserving the complete original continuation. -/
theorem copy_prefix_loop_eval (n : ℕ) (acc original : List ℕ) (hn : n ≤ original.length) :
    (Code.fix copyPrefixBody).eval (n :: acc.length :: (acc ++ original)) =
      pure (original.take n ++ acc ++ original) := by
  let body : List ℕ → Part (List ℕ ⊕ List ℕ) := fun v ↦
    (copyPrefixBody.eval v).map fun w ↦
      if w.headI = 0 then Sum.inl w.tail else Sum.inr w.tail
  have hzero (acc : List ℕ) : body (0 :: acc.length :: (acc ++ original)) =
      pure (Sum.inl (acc ++ original)) := by simp [body, copyPrefixBody]
  have hsucc (n : ℕ) (acc : List ℕ) (hn : n < original.length) :
      body ((n + 1) :: acc.length :: (acc ++ original)) =
        pure (Sum.inr (n :: (acc.length + 1) :: (original[n] :: acc ++ original))) := by
    have hdrop : (acc ++ original).drop (n + acc.length) = original.drop n := by
      simp [List.drop_append]
    have hhead : (original.drop n).headI = original[n] := by
      rw [List.drop_eq_getElem_cons hn]
      rfl
    simp [body, copyPrefixBody, add_code_eval, nth_code_eval, hdrop, hhead]
  change PFun.fix body (n :: acc.length :: (acc ++ original)) =
    pure (original.take n ++ acc ++ original)
  apply Part.eq_some_iff.mpr
  induction n generalizing acc with
  | zero => exact PFun.mem_fix_iff.mpr (Or.inl (by simp [hzero]))
  | succ n ih =>
      have hlt : n < original.length := by omega
      refine PFun.mem_fix_iff.mpr (Or.inr
        ⟨n :: (acc.length + 1) :: (original[n] :: acc ++ original), ?_, ?_⟩)
      · simp [hsucc n acc hlt]
      · have hrec := ih (original[n] :: acc) (by omega)
        have hout : original.take (n + 1) ++ acc ++ original =
            original.take n ++ (original[n] :: acc) ++ original := by
          rw [List.take_succ_eq_append_getElem hlt]
          simp only [List.append_assoc, List.singleton_append]
        rw [hout]
        simpa only [List.length_cons, List.cons_append] using hrec

/-- Counted list copying is a certified concrete source program. -/
theorem copy_prefix_code_eval (n : ℕ) (original : List ℕ) (hn : n ≤ original.length) :
    copyPrefixCode.eval (n :: original) = pure (original.take n ++ original) := by
  simp only [copyPrefixCode, Code.comp_eval, Code.cons_eval, Code.head_eval, Code.tail_eval,
    Code.zero'_eval, Part.pure_eq_some, Bind.bind, Part.bind_some, List.headI_cons,
    List.tail_cons]
  simpa using copy_prefix_loop_eval n [] original hn

/-- Branch on a zero-valued test while restoring the original list input in both branches. -/
def branchZeroCode (test yes no : Code) : Code :=
  .comp (.case yes (.comp no .tail)) (.cons test .id)

/-- The branch helper changes control, without changing its data argument. -/
theorem branch_zero_code_eval (test yes no : Code) (v : List ℕ) (flag : ℕ)
    (htest : test.eval v = pure [flag]) :
    (branchZeroCode test yes no).eval v = if flag = 0 then yes.eval v else no.eval v := by
  cases flag <;> simp [branchZeroCode, htest]

/-- The numerical inequality indicator used when omitting a selected list index. -/
def differentCode : Code := .comp positiveCode differenceCode

@[simp]
theorem different_code_eval (a b : ℕ) (v : List ℕ) :
    differentCode.eval (a :: b :: v) = pure ((if a = b then 0 else 1) :: v) := by
  simp only [differentCode, Code.comp_eval, difference_code_eval, Part.pure_eq_some,
    Bind.bind, Part.bind_some, positive_code_eval]
  congr 2
  split_ifs <;> omega

/-- Extend a copied prefix backwards while omitting the chosen index. -/
def copyExceptBody : Code :=
  .case (.comp .zero' (.comp .tail .tail))
    (branchZeroCode
      (.comp differentCode
        (.cons .head (.cons (.comp .head (.comp .tail .tail)) .nil)))
      (.cons (literal 1) .id)
      (.cons (literal 1) (.cons .head (.cons (.comp .succ .tail)
        (.cons (.comp .head (.comp .tail .tail))
          (.cons
            (.comp nthCode (.cons addCode (.comp .tail (.comp .tail .tail))))
            (.comp .tail (.comp .tail .tail))))))))

/-- Copy a counted list prefix with one index removed, retaining the original as continuation. -/
def copyExceptCode : Code :=
  .comp (.fix copyExceptBody) (.cons .head (.comp .zero' .tail))

/-- The erased-prefix recurrence underlying the concrete backwards copying loop. -/
theorem erase_take_succ (original : List ℕ) (n skip : ℕ) (hn : n < original.length) :
    (original.take (n + 1)).eraseIdx skip =
      if n = skip then (original.take n).eraseIdx skip
      else (original.take n).eraseIdx skip ++ [original[n]] := by
  have hlen : (original.take n).length = n := by simp [Nat.le_of_lt hn]
  rw [List.take_succ_eq_append_getElem hn, List.eraseIdx_append, hlen]
  by_cases hskip : skip < n
  · have hne : n ≠ skip := by omega
    rw [ite_eq_left hskip, ite_eq_right hne]
  · have herase : (original.take n).eraseIdx skip = original.take n :=
      List.eraseIdx_of_length_le (by omega)
    rw [ite_eq_right hskip]
    by_cases heq : n = skip
    · rw [ite_eq_left heq, herase]
      subst skip
      simp only [Nat.sub_self, List.eraseIdx_zero, List.tail_cons, List.append_nil]
    · rw [ite_eq_right heq, herase]
      have hpos : [original[n]].length ≤ skip - n := by simp only [List.length_singleton]; omega
      rw [List.eraseIdx_of_length_le hpos]

/-- The child-list construction is executed by a finite constructor-only source program. -/
theorem copy_except_loop_eval (n skip : ℕ) (acc original : List ℕ)
    (hn : n ≤ original.length) :
    (Code.fix copyExceptBody).eval (n :: acc.length :: skip :: (acc ++ original)) =
      pure ((original.take n).eraseIdx skip ++ acc ++ original) := by
  let body : List ℕ → Part (List ℕ ⊕ List ℕ) := fun v ↦
    (copyExceptBody.eval v).map fun w ↦
      if w.headI = 0 then Sum.inl w.tail else Sum.inr w.tail
  have hzero (acc : List ℕ) : body (0 :: acc.length :: skip :: (acc ++ original)) =
      pure (Sum.inl (acc ++ original)) := by simp [body, copyExceptBody]
  have hsucc (n : ℕ) (acc : List ℕ) (hn : n < original.length) :
      body ((n + 1) :: acc.length :: skip :: (acc ++ original)) =
        pure (Sum.inr (if n = skip then n :: acc.length :: skip :: (acc ++ original)
          else n :: (acc.length + 1) :: skip :: (original[n] :: acc ++ original))) := by
    have hdrop : (acc ++ original).drop (n + acc.length) = original.drop n := by
      simp [List.drop_append]
    have hhead : (original.drop n).headI = original[n] := by
      rw [List.drop_eq_getElem_cons hn]
      rfl
    have htest :
        (Code.comp differentCode
          (.cons .head (.cons (.comp .head (.comp .tail .tail)) .nil))).eval
            (n :: acc.length :: skip :: (acc ++ original)) =
          pure [if n = skip then 0 else 1] := by simp
    simp only [body, copyExceptBody, Code.case_eval, List.headI_cons, List.tail_cons]
    rw [branch_zero_code_eval _ _ _ _ _ htest]
    by_cases heq : n = skip <;>
      simp [heq, add_code_eval, nth_code_eval, hdrop, hhead]
  change PFun.fix body (n :: acc.length :: skip :: (acc ++ original)) =
    pure ((original.take n).eraseIdx skip ++ acc ++ original)
  apply Part.eq_some_iff.mpr
  induction n generalizing acc with
  | zero => exact PFun.mem_fix_iff.mpr (Or.inl (by simp [hzero]))
  | succ n ih =>
      have hlt : n < original.length := by omega
      by_cases heq : n = skip
      · refine PFun.mem_fix_iff.mpr (Or.inr
          ⟨n :: acc.length :: skip :: (acc ++ original), ?_, ?_⟩)
        · rw [hsucc n acc hlt]
          simp [heq]
        · rw [erase_take_succ original n skip hlt, ite_eq_left heq]
          exact ih acc (by omega)
      · refine PFun.mem_fix_iff.mpr (Or.inr
          ⟨n :: (acc.length + 1) :: skip :: (original[n] :: acc ++ original), ?_, ?_⟩)
        · rw [hsucc n acc hlt]
          simp [heq]
        · have hrec := ih (original[n] :: acc) (by omega)
          rw [erase_take_succ original n skip hlt, ite_eq_right heq]
          simpa only [List.length_cons, List.cons_append, List.append_assoc,
            List.singleton_append, List.nil_append] using hrec

/-- A legal index can be removed while preserving the entire parent frame below the child list. -/
theorem copy_except_code_eval (n skip : ℕ) (original : List ℕ) (hn : n ≤ original.length) :
    copyExceptCode.eval (n :: skip :: original) =
      pure ((original.take n).eraseIdx skip ++ original) := by
  simp only [copyExceptCode, Code.comp_eval, Code.cons_eval, Code.head_eval, Code.tail_eval,
    Code.zero'_eval, Part.pure_eq_some, Bind.bind, Part.bind_some, List.headI_cons,
    List.tail_cons]
  simpa using copy_except_loop_eval n skip [] original hn

/-- A fixed register projection, expanded to a finite chain of source tail operations. -/
def registerCode : ℕ → Code
  | 0 => .head
  | n + 1 => .comp (registerCode n) .tail

@[simp]
theorem register_code_eval (n : ℕ) (v : List ℕ) :
    (registerCode n).eval v = pure [(v.drop n).headI] := by
  induction n generalizing v with
  | zero => simp [registerCode]
  | succ n ih => simp [registerCode, ih, List.drop_tail]

/-- A fixed number of source tail operations. -/
def tailsCode : ℕ → Code
  | 0 => .id
  | n + 1 => .comp (tailsCode n) .tail

@[simp]
theorem tails_code_eval (n : ℕ) (v : List ℕ) :
    (tailsCode n).eval v = pure (v.drop n) := by
  induction n generalizing v with
  | zero => simp [tailsCode]
  | succ n ih => simp [tailsCode, ih, List.drop_tail]

/-- Prefix a finite register record without replacing any field by a host-language operation. -/
def prefixCode (fields : List Code) (rest : Code) : Code := fields.foldr .cons rest

/-- Fetch the selected counter from a scan state `[length, deficit, index, accumulator, ...]`. -/
def selectedCode : Code :=
  .comp nthCode (.cons (registerCode 2) (tailsCode 4))

/-- Compute the child's normalized deficit from the selected counter. -/
def childDeficitCode : Code :=
  .comp differenceCode (.cons selectedCode (.cons (registerCode 1) .nil))

/-- Record whether returning from this child changes player perspective. -/
def childNegateCode : Code :=
  .comp parityStepCode (.comp lessCode
    (.cons selectedCode (.cons (registerCode 1) .nil)))

/-- Save the pending parent's continuation record above its unchanged remaining-counter list. -/
def parentFrameCode : Code :=
  prefixCode [childNegateCode, registerCode 0, registerCode 1,
    .comp .succ (registerCode 2), registerCode 3] (tailsCode 4)

/-- Copy the selected child's counter list above the saved parent continuation. -/
def childDataCode : Code :=
  .comp (.fix copyExceptBody)
    (prefixCode [registerCode 0, literal 5, registerCode 2] parentFrameCode)

/-- A concrete DFS call kernel: construct the child's active frame and save the parent. -/
def callChildCode : Code :=
  prefixCode [literal 0, .comp .pred (registerCode 0), childDeficitCode,
    literal 0, literal 0] childDataCode

/-- The selected counter's numeric fetch reads exactly the desired legal move. -/
theorem selected_code_eval (remaining stack : List ℕ) (deficit index acc : ℕ)
    (hindex : index < remaining.length) :
    selectedCode.eval (remaining.length :: deficit :: index :: acc :: (remaining ++ stack)) =
      pure [remaining[index]] := by
  have hdrop : ((remaining ++ stack).drop index).headI = remaining[index] := by
    rw [List.drop_eq_getElem_cons (by simp; omega)]
    simp [List.getElem_append_left hindex]
  simp [selectedCode, registerCode, tailsCode, nth_code_eval, hdrop]

/-- This kernel saves all six semantic facts needed to resume the minimax scan. -/
theorem call_child_code_eval (remaining stack : List ℕ) (deficit index acc : ℕ)
    (hindex : index < remaining.length) :
    callChildCode.eval (remaining.length :: deficit :: index :: acc :: (remaining ++ stack)) =
      pure ([0, remaining.length - 1,
          if remaining[index] < deficit then deficit - remaining[index]
            else remaining[index] - deficit, 0, 0] ++
        remaining.eraseIdx index ++
        [if remaining[index] < deficit then 0 else 1,
          remaining.length, deficit, index + 1, acc] ++ remaining ++ stack) := by
  let parent := [if remaining[index] < deficit then 0 else 1,
    remaining.length, deficit, index + 1, acc]
  let input := remaining.length :: deficit :: index :: acc :: (remaining ++ stack)
  have hpicked : selectedCode.eval input = pure [remaining[index]] :=
    selected_code_eval remaining stack deficit index acc hindex
  have hdeficit : childDeficitCode.eval input = pure
      [if remaining[index] < deficit then deficit - remaining[index]
        else remaining[index] - deficit] := by
    simp [childDeficitCode, hpicked, input, registerCode, difference_code_eval]
  have hnegate : childNegateCode.eval input =
      pure [if remaining[index] < deficit then 0 else 1] := by
    simp only [childNegateCode, Code.comp_eval, Code.cons_eval, hpicked,
      register_code_eval, input, List.drop_succ_cons, List.drop_zero, List.headI_cons,
      Code.nil_eval, Part.pure_eq_some, Bind.bind, Part.bind_some, List.headI_cons]
    rw [less_code_eval]
    split_ifs <;> simp [parityStepCode]
  have hparent : parentFrameCode.eval input = pure (parent ++ remaining ++ stack) := by
    simp [parentFrameCode, prefixCode, hnegate, input, parent, registerCode, tailsCode]
  have hdata : childDataCode.eval input =
      pure (remaining.eraseIdx index ++ parent ++ remaining ++ stack) := by
    have hcopy := copy_except_loop_eval remaining.length index parent (remaining ++ stack)
      (by simp)
    simp only [List.take_left] at hcopy
    simpa [childDataCode, prefixCode, hparent, input, registerCode,
      List.append_assoc, parent] using hcopy
  change callChildCode.eval input = _
  simp [callChildCode, prefixCode, hdata, hdeficit, input, registerCode, List.append_assoc, parent]

/-- The compiled child's data record is exactly the reference game's legal transition. -/
theorem child_position_eq_after_pick (remaining : List ℕ) (deficit index : ℕ)
    (hnodup : remaining.Nodup) (hindex : index < remaining.length) :
    (⟨(remaining.eraseIdx index).toFinset,
      if remaining[index] < deficit then deficit - remaining[index]
        else remaining[index] - deficit⟩ : Position) =
      (⟨remaining.toFinset, deficit⟩ : Position).afterPick remaining[index] := by
  rw [← hnodup.erase_getElem index hindex, to_finset_erase remaining hnodup]
  rfl

/-- Every compiled child call strictly reduces the same finite counter set as reference minimax. -/
theorem child_remaining_length_lt (remaining : List ℕ) (index : ℕ)
    (hindex : index < remaining.length) :
    (remaining.eraseIdx index).length < remaining.length := by
  have := List.length_eraseIdx_add_one hindex
  omega

/-- Read a returned child's result in the pending parent's perspective. -/
def returnedOutcomeCode : Code :=
  branchZeroCode (registerCode 1) (registerCode 0) (.comp negateCode (registerCode 0))

/-- Resume a pending parent's scan after applying perspective and updating its best outcome. -/
def resumeParentCode : Code :=
  prefixCode [literal 1, registerCode 2, registerCode 3, registerCode 4,
    .comp maxCode (.cons (registerCode 5) (.cons returnedOutcomeCode .nil))] (tailsCode 6)

/-- Returning through the saved continuation performs exactly the numeric minimax update. -/
theorem resume_parent_code_eval (result negate n deficit index acc : ℕ) (tail : List ℕ) :
    resumeParentCode.eval (result :: negate :: n :: deficit :: index :: acc :: tail) =
      pure ([1, n, deficit, index,
        max acc (if negate = 0 then result else negateNumber result)] ++ tail) := by
  let input := result :: negate :: n :: deficit :: index :: acc :: tail
  have htest : (registerCode 1).eval input = pure [negate] := by
    simp [input, registerCode]
  have hreturn : returnedOutcomeCode.eval input =
      pure [if negate = 0 then result else negateNumber result] := by
    rw [returnedOutcomeCode, branch_zero_code_eval _ _ _ _ _ htest]
    by_cases hnegate : negate = 0 <;>
      simp [hnegate, input, registerCode, negate_code_eval]
  simp [resumeParentCode, prefixCode, hreturn, input, registerCode, tailsCode, max_code_eval]

/-- An active entry record; mode zero performs terminal detection before scanning. -/
def enterState (remaining : List ℕ) (deficit : ℕ) (stack : List ℕ) : List ℕ :=
  [0, remaining.length, deficit, 0, 0] ++ remaining ++ stack

/-- An active move-scan record; mode one visits the next unexamined counter. -/
def scanState (remaining : List ℕ) (deficit index acc : ℕ) (stack : List ℕ) : List ℕ :=
  [1, remaining.length, deficit, index, acc] ++ remaining ++ stack

/-- A return record; the next stack word is either a parent perspective bit or root sentinel two. -/
def returnState (result : ℕ) (stack : List ℕ) : List ℕ := [2, result] ++ stack

/-- A parent continuation stored below a child's remaining counters. -/
def parentStack (remaining : List ℕ) (deficit index acc negate : ℕ)
    (stack : List ℕ) : List ℕ :=
  [negate, remaining.length, deficit, index, acc] ++ remaining ++ stack

/-- Read terminal status from an entry frame, skipping its scan registers. -/
def entryTerminalCode : Code :=
  .comp terminalCode (.cons (registerCode 0) (.cons (registerCode 1) (tailsCode 4)))

/-- Return a supplied numeric result, removing this frame's entire remaining-counter list. -/
def finishFrameCode (result : Code) : Code :=
  prefixCode [literal 1, literal 2, result]
    (.comp dropCode (.cons (registerCode 0) (tailsCode 4)))

/-- Enter a frame: either initialize its scan or return the exact terminal outcome. -/
def enterDispatchCode : Code :=
  branchZeroCode entryTerminalCode
    (.cons (literal 1) (.cons (literal 1) .id))
    (finishFrameCode (.comp .pred entryTerminalCode))

/-- Decide whether a scan has an unvisited legal move. -/
def scanHasMoveCode : Code :=
  .comp lessCode (.cons (registerCode 2) (.cons (registerCode 0) .nil))

/-- Scan one move or return the completed minimax maximum. -/
def scanDispatchCode : Code :=
  branchZeroCode scanHasMoveCode (finishFrameCode (registerCode 3))
    (.cons (literal 1) callChildCode)

/-- Distinguish the bottom sentinel from pending parents using their perspective bits. -/
def returnHasParentCode : Code :=
  .comp lessCode (.cons (registerCode 1) (literal 2))

/-- Resume a parent, or stop the fix loop at the sentinel with the root result. -/
def returnDispatchCode : Code :=
  branchZeroCode returnHasParentCode (.cons (literal 0) (registerCode 0))
    (.cons (literal 1) resumeParentCode)

/-- The complete finite-game dispatcher. Every non-root branch requests another iteration. -/
def gameBodyCode : Code :=
  .case enterDispatchCode (.case scanDispatchCode (.case returnDispatchCode .nil))

/-- A concrete, finite constructor tree for unbounded depth-first finite-game evaluation. -/
def gameLoopCode : Code := .fix gameBodyCode

/-- Terminal detection tolerates arbitrary continuation data after the counted counter list. -/
theorem terminal_code_eval_stack (remaining stack : List ℕ) (deficit : ℕ) :
    terminalCode.eval (remaining.length :: deficit :: (remaining ++ stack)) =
      pure [terminalNumber remaining deficit] := by
  cases remaining with
  | nil => cases deficit <;> simp [terminalCode, terminalNumber]
  | cons x xs =>
      have hsum := sum_code_eval (x :: xs) 0 stack
      simp only [List.cons_append, Nat.zero_add] at hsum
      simp only [terminalCode, Code.case_eval, List.headI_cons, List.length_cons,
        List.tail_cons, Code.comp_eval, Code.cons_eval, Code.succ_eval, Code.tail_eval,
        Code.zero'_eval, Code.head_eval, Part.pure_eq_some, Bind.bind, Part.bind_some,
        List.headI_cons, List.cons_append]
      simp only [List.length_cons, Nat.succ_eq_add_one] at hsum ⊢
      rw [hsum]
      simp [less_code_eval, terminalNumber]

/-- Returning a completed frame preserves exactly its following continuation. -/
theorem finish_frame_code_eval (result : Code) (remaining stack : List ℕ)
    (deficit index acc value : ℕ)
    (hresult : result.eval
      (remaining.length :: deficit :: index :: acc :: (remaining ++ stack)) = pure [value]) :
    (finishFrameCode result).eval
      (remaining.length :: deficit :: index :: acc :: (remaining ++ stack)) =
        pure (1 :: returnState value stack) := by
  simp [finishFrameCode, prefixCode, hresult, registerCode, tailsCode,
    drop_code_eval, returnState]

/-- The entry dispatch has the literal terminal/scan behavior of the list evaluator. -/
theorem game_body_enter_eval (remaining stack : List ℕ) (deficit : ℕ) :
    gameBodyCode.eval (enterState remaining deficit stack) =
      if terminalNumber remaining deficit = 0 then
        pure (1 :: scanState remaining deficit 0 0 stack)
      else pure (1 :: returnState (terminalNumber remaining deficit - 1) stack) := by
  let input := remaining.length :: deficit :: 0 :: 0 :: (remaining ++ stack)
  have hterminal : entryTerminalCode.eval input = pure [terminalNumber remaining deficit] := by
    simp [entryTerminalCode, input, registerCode, tailsCode, terminal_code_eval_stack]
  have hresult : (Code.comp .pred entryTerminalCode).eval input =
      pure [terminalNumber remaining deficit - 1] := by
    simp [hterminal, Nat.pred_eq_sub_one]
  change enterDispatchCode.eval input = _
  rw [enterDispatchCode, branch_zero_code_eval _ _ _ _ _ hterminal]
  by_cases hzero : terminalNumber remaining deficit = 0
  · simp [hzero, input, scanState]
  · rw [ite_eq_right hzero, finish_frame_code_eval _ remaining stack deficit 0 0 _ hresult]
    simp [hzero]

/-- A completed scan returns the accumulated best outcome. -/
theorem game_body_scan_done_eval (remaining stack : List ℕ) (deficit index acc : ℕ)
    (hindex : remaining.length ≤ index) :
    gameBodyCode.eval (scanState remaining deficit index acc stack) =
      pure (1 :: returnState acc stack) := by
  let input := remaining.length :: deficit :: index :: acc :: (remaining ++ stack)
  have htest : scanHasMoveCode.eval input = pure [0] := by
    simp [scanHasMoveCode, input, registerCode, less_code_eval, Nat.not_lt.mpr hindex]
  change scanDispatchCode.eval input = _
  rw [scanDispatchCode, branch_zero_code_eval _ _ _ _ _ htest]
  simp only [↓reduceIte]
  apply finish_frame_code_eval
  simp [registerCode]

/-- A legal scan step calls exactly the selected child and saves its parent. -/
theorem game_body_scan_child_eval (remaining stack : List ℕ) (deficit index acc : ℕ)
    (hindex : index < remaining.length) :
    gameBodyCode.eval (scanState remaining deficit index acc stack) =
      pure (1 :: enterState (remaining.eraseIdx index)
        (if remaining[index] < deficit then deficit - remaining[index]
          else remaining[index] - deficit)
        (parentStack remaining deficit (index + 1) acc
          (if remaining[index] < deficit then 0 else 1) stack)) := by
  let input := remaining.length :: deficit :: index :: acc :: (remaining ++ stack)
  have htest : scanHasMoveCode.eval input = pure [1] := by
    simp [scanHasMoveCode, input, registerCode, less_code_eval, hindex]
  change scanDispatchCode.eval input = _
  rw [scanDispatchCode, branch_zero_code_eval _ _ _ _ _ htest]
  simp only [Nat.one_ne_zero, ↓reduceIte]
  simp [input, call_child_code_eval remaining stack deficit index acc hindex,
    enterState, parentStack, List.length_eraseIdx_of_lt hindex, List.append_assoc]

/-- Returning from a child resumes the pending parent's scan with the adjusted result. -/
theorem game_body_return_parent_eval (remaining stack : List ℕ)
    (result negate deficit index acc : ℕ) (hnegate : negate < 2) :
    gameBodyCode.eval (returnState result
      (parentStack remaining deficit index acc negate stack)) =
        pure (1 :: scanState remaining deficit index
          (max acc (if negate = 0 then result else negateNumber result)) stack) := by
  let input := result :: negate :: remaining.length :: deficit :: index :: acc ::
    (remaining ++ stack)
  have htest : returnHasParentCode.eval input = pure [1] := by
    simp [returnHasParentCode, input, registerCode, less_code_eval, hnegate]
  change returnDispatchCode.eval input = _
  rw [returnDispatchCode, branch_zero_code_eval _ _ _ _ _ htest]
  simp [input, resume_parent_code_eval, scanState]

/-- The bottom sentinel is the sole halting branch on well-formed game states. -/
theorem game_body_return_root_eval (result : ℕ) :
    gameBodyCode.eval (returnState result [2]) = pure [0, result] := by
  simp [gameBodyCode, returnState, returnDispatchCode, branchZeroCode,
    returnHasParentCode, registerCode, less_code_eval]
  rfl

/-- A proved continuing dispatch step lifts membership in the actual Code.fix evaluation. -/
theorem game_loop_mem_of_step (state next result : List ℕ)
    (hstep : gameBodyCode.eval state = pure (1 :: next))
    (hnext : result ∈ gameLoopCode.eval next) : result ∈ gameLoopCode.eval state := by
  change result ∈ PFun.fix _ state
  apply PFun.mem_fix_iff.mpr
  exact Or.inr ⟨next, by simp [hstep], hnext⟩

/-- Root return is finite Code.fix evaluation, not a bounded observation. -/
theorem game_loop_root_eval (result : ℕ) :
    gameLoopCode.eval (returnState result [2]) = pure [result] := by
  apply Part.eq_some_iff.mpr
  change [result] ∈ PFun.fix _ _
  apply PFun.mem_fix_iff.mpr
  exact Or.inl (by simp [game_body_return_root_eval])

/-- One move's numeric result at a fixed recursion depth. -/
def moveNumber (fuel : ℕ) (remaining : List ℕ) (deficit picked : ℕ) : ℕ :=
  let child := evalFuel fuel (remaining.erase picked)
    (if picked < deficit then deficit - picked else picked - deficit)
  if picked < deficit then child else negateNumber child

/-- The exact remaining work of a partial minimax scan. -/
def scanNumber (fuel : ℕ) (remaining : List ℕ) (deficit index acc : ℕ) : ℕ :=
  ((remaining.drop index).map (moveNumber fuel remaining deficit)).foldl max acc

/-- The raw evaluator splits into the same terminal and scanning cases as the dispatcher. -/
theorem eval_fuel_terminal_or_scan (fuel : ℕ) (remaining : List ℕ) (deficit : ℕ) :
    evalFuel (fuel + 1) remaining deficit =
      if terminalNumber remaining deficit = 0 then scanNumber fuel remaining deficit 0 0
      else terminalNumber remaining deficit - 1 := by
  by_cases hempty : remaining = []
  · subst remaining
    by_cases hdeficit : deficit = 0 <;>
      simp [evalFuel, terminalNumber, hdeficit]
  · by_cases hsum : remaining.sum < deficit
    · simp [evalFuel, terminalNumber, hempty, hsum]
    · simp only [evalFuel, terminalNumber, hempty, hsum, ↓reduceIte, scanNumber, List.drop_zero]
      rfl

/-- Once the scan index reaches the list length, no minimax work remains. -/
theorem scan_number_done (fuel : ℕ) (remaining : List ℕ) (deficit index acc : ℕ)
    (hindex : remaining.length ≤ index) : scanNumber fuel remaining deficit index acc = acc := by
  simp [scanNumber, List.drop_eq_nil_of_le hindex]

/-- Scanning one legal counter updates the maximum before advancing its index. -/
theorem scan_number_step (fuel : ℕ) (remaining : List ℕ) (deficit index acc : ℕ)
    (hindex : index < remaining.length) :
    scanNumber fuel remaining deficit index acc =
      scanNumber fuel remaining deficit (index + 1)
        (max acc (moveNumber fuel remaining deficit remaining[index])) := by
  simp only [scanNumber, List.drop_eq_getElem_cons hindex, List.map_cons, List.foldl_cons]

/-- Entering a game frame has the same eventual result as returning its exact minimax value.
The theorem quantifies over arbitrary continuations and output lists, so its induction proves
finite evaluation of the actual dispatcher rather than relying on a bounded run. -/
theorem game_loop_enter_mem (fuel : ℕ) (remaining : List ℕ) (deficit : ℕ)
    (stack result : List ℕ) (hnodup : remaining.Nodup) (hfuel : remaining.length < fuel)
    (hreturn : result ∈ gameLoopCode.eval (returnState (evalFuel fuel remaining deficit) stack)) :
    result ∈ gameLoopCode.eval (enterState remaining deficit stack) := by
  induction fuel generalizing remaining deficit stack result with
  | zero => omega
  | succ fuel ih =>
      have hscan : ∀ count index acc, remaining.length - index = count →
          result ∈ gameLoopCode.eval
            (returnState (scanNumber fuel remaining deficit index acc) stack) →
          result ∈ gameLoopCode.eval (scanState remaining deficit index acc stack) := by
        intro count
        induction count with
        | zero =>
            intro index acc hcount hresult
            have hindex : remaining.length ≤ index := by omega
            apply game_loop_mem_of_step _ _ result
              (game_body_scan_done_eval remaining stack deficit index acc hindex)
            simpa only [scan_number_done fuel remaining deficit index acc hindex] using hresult
        | succ count ihscan =>
            intro index acc hcount hresult
            have hindex : index < remaining.length := by omega
            let picked := remaining[index]
            let childDeficit := if picked < deficit then deficit - picked else picked - deficit
            let childResult := evalFuel fuel (remaining.eraseIdx index) childDeficit
            let negate := if picked < deficit then 0 else 1
            let pending := parentStack remaining deficit (index + 1) acc negate stack
            have hnegate : negate < 2 := by dsimp [negate]; split_ifs <;> omega
            have hmove : (if negate = 0 then childResult else negateNumber childResult) =
                moveNumber fuel remaining deficit remaining[index] := by
              dsimp [negate, childResult, childDeficit, picked, moveNumber]
              rw [← hnodup.erase_getElem index hindex]
              by_cases hlt : remaining[index] < deficit <;> simp [hlt]
            have hnext : result ∈ gameLoopCode.eval
                (scanState remaining deficit (index + 1)
                  (max acc (moveNumber fuel remaining deficit remaining[index])) stack) := by
              apply ihscan (index + 1) _ (by omega)
              simpa only [scan_number_step fuel remaining deficit index acc hindex] using hresult
            have hchildReturn : result ∈ gameLoopCode.eval (returnState childResult pending) := by
              apply game_loop_mem_of_step _ _ result
                (game_body_return_parent_eval remaining stack childResult negate deficit
                  (index + 1) acc hnegate)
              simpa only [hmove] using hnext
            have hchildFuel : (remaining.eraseIdx index).length < fuel := by
              rw [List.length_eraseIdx_of_lt hindex]
              omega
            have hchildEnter : result ∈ gameLoopCode.eval
                (enterState (remaining.eraseIdx index) childDeficit pending) :=
              ih (remaining.eraseIdx index) childDeficit pending result
                (hnodup.eraseIdx index) hchildFuel hchildReturn
            exact game_loop_mem_of_step _ _ result
              (game_body_scan_child_eval remaining stack deficit index acc hindex) hchildEnter
      have hvalue := eval_fuel_terminal_or_scan fuel remaining deficit
      have hstep := game_body_enter_eval remaining stack deficit
      by_cases hterminal : terminalNumber remaining deficit = 0
      · rw [ite_eq_left hterminal] at hvalue hstep
        apply game_loop_mem_of_step _ _ result hstep
        apply hscan remaining.length 0 0 (by omega)
        simpa only [hvalue] using hreturn
      · rw [ite_eq_right hterminal] at hvalue hstep
        apply game_loop_mem_of_step _ _ result hstep
        simpa only [hvalue] using hreturn

/-- The complete concrete game loop terminates with the exact raw-list minimax result. -/
theorem game_loop_eval (remaining : List ℕ) (deficit : ℕ) (hnodup : remaining.Nodup) :
    gameLoopCode.eval (enterState remaining deficit [2]) =
      pure [evalFuel (remaining.length + 1) remaining deficit] := by
  apply Part.eq_some_iff.mpr
  apply game_loop_enter_mem (remaining.length + 1) remaining deficit [2] _ hnodup (by omega)
  rw [game_loop_root_eval]
  exact Part.mem_some_iff.mpr rfl

/-- Construct the ascending interval while retaining the following continuation data. -/
def rangeStateCode : Code :=
  .comp .tail (.comp (repeatCode rangeStepCode) (.cons .head .id))

/-- Range construction can leave the root sentinel immediately after its generated counters. -/
theorem range_state_code_eval (n : ℕ) (v : List ℕ) :
    rangeStateCode.eval (n :: v) = pure (List.range' 1 n ++ v) := by
  have hstep (w : List ℕ) :
      rangeStepCode.eval w = pure (w.headI.pred :: w) := by simp [rangeStepCode]
  simp only [rangeStateCode, Code.comp_eval, Code.cons_eval, Code.head_eval, Code.id_eval,
    Part.pure_eq_some, Bind.bind, Part.bind_some, List.headI_cons]
  rw [repeat_code_eval rangeStepCode _ hstep, iterate_range_state]
  simp

/-- Evaluate the exact Catch-Up interval game from its endpoint, using a real root sentinel. -/
def intervalValueCode : Code :=
  .comp gameLoopCode (prefixCode [literal 0, .head, .zero, .zero, .zero]
    (.comp rangeStateCode (.cons .head (literal 2))))

/-- This is a specific finite Code implementation of the previously uncompiled game recurrence. -/
theorem interval_value_code_eval (n : ℕ) (v : List ℕ) :
    intervalValueCode.eval (n :: v) = pure [evalFuel (n + 1) (List.range' 1 n) 0] := by
  have hgame := game_loop_eval (List.range' 1 n) 0 List.nodup_range'
  simp only [enterState, List.length_range'] at hgame
  simpa [intervalValueCode, prefixCode, range_state_code_eval, List.append_assoc] using hgame

/-- Return one exactly on the numeric draw outcome. -/
def drawTestCode : Code := .case .zero (.case (literal 1) .zero)

/-- Draw testing needs only the three numeric outcome tags. -/
theorem draw_test_code_eval (n : ℕ) (v : List ℕ) :
    drawTestCode.eval (n :: v) = pure [if n = 1 then 1 else 0] := by
  cases n with
  | zero => simp [drawTestCode]
  | succ n => cases n <;> simp [drawTestCode]

/-- The complete explicit zero-for-counterexample test: eligibility followed by exact minimax. -/
def counterexampleCode : Code :=
  branchZeroCode eligibilityCode (.comp drawTestCode intervalValueCode) (literal 1)

/-- The concrete predicate program implements the exact independently verified raw-list test. -/
theorem counterexample_code_eval (n : ℕ) (v : List ℕ) :
    counterexampleCode.eval (n :: v) = pure [intervalTest n] := by
  rw [counterexampleCode,
    branch_zero_code_eval _ _ _ _ _ (eligibility_code_eval n v)]
  by_cases heven : Even (n * (n + 1) / 2)
  · have hzero := (eligibility_zero_iff n).mpr heven
    simp [hzero, interval_value_code_eval, draw_test_code_eval, intervalTest, heven]
  · have hzero : (n * (n + 1) / 2) % 2 ≠ 0 :=
      fun h ↦ heven ((eligibility_zero_iff n).mp h)
    simp [hzero, intervalTest, heven]

/-- One explicit outer iteration: the test result followed by the next search integer. -/
def searchBody (test : Code) : Code := .cons test .succ

/-- Start the outer search at `1`; a zero test result exits the `fix` loop. -/
def search (test : Code) : Code := .comp (.fix (searchBody test)) .succ

/-- The exact interface between the finite-game test program and the outer search. -/
def TestsCounterexamples (test : Code) : Prop :=
  ∀ n, test.eval [n] = pure [if Search.isCounterexample n then 0 else 1]

/-- Explicit source loop correctness for an arbitrary total natural-number stop test. -/
theorem fix_search_body_dom_iff (test : Code) (stop : ℕ → Bool)
    (htest : ∀ n, test.eval [n] = pure [if stop n then 0 else 1]) (start : ℕ) :
    ((.fix (searchBody test) : Code).eval [start]).Dom ↔
      ∃ offset, stop (start + offset) = true := by
  let body : List ℕ → Part (List ℕ ⊕ List ℕ) := fun v ↦
    ((searchBody test).eval v).map fun w ↦
      if w.headI = 0 then Sum.inl w.tail else Sum.inr w.tail
  have hbody (n : ℕ) : body [n] = pure
      (if stop n then Sum.inl [n + 1] else Sum.inr [n + 1]) := by
    cases h : stop n <;> simp [body, searchBody, htest, h]
  change (PFun.fix body [start]).Dom ↔ _
  constructor
  · intro hdom
    obtain ⟨result, hresult⟩ := Part.dom_iff_mem.mp hdom
    have hforward : ∀ v, result ∈ PFun.fix body v →
        ∀ n, v = [n] → ∃ offset, stop (n + offset) = true := by
      intro v hv
      refine PFun.fixInduction hv fun v' hv' ih ↦ ?_
      intro n hn
      subst v'
      by_cases hstop : stop n = true
      · exact ⟨0, by simpa using hstop⟩
      · obtain hdone | ⟨next, hnext, _⟩ := PFun.mem_fix_iff.mp hv'
        · simp [hbody, hstop] at hdone
        · have hnxt : next = [n + 1] := by simpa [hbody, hstop] using hnext
          obtain ⟨offset, hoffset⟩ := ih next hnext (n + 1) hnxt
          exact ⟨offset + 1, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hoffset⟩
    exact hforward [start] hresult start rfl
  · rintro ⟨offset, hoffset⟩
    induction offset generalizing start with
    | zero =>
        apply Part.dom_iff_mem.mpr
        refine ⟨[start + 1], PFun.mem_fix_iff.mpr (Or.inl ?_)⟩
        simpa [hbody] using hoffset
    | succ offset ih =>
        by_cases hstop : stop start = true
        · apply Part.dom_iff_mem.mpr
          exact ⟨[start + 1], PFun.mem_fix_iff.mpr (Or.inl (by simp [hbody, hstop]))⟩
        · have hnext : stop (start + 1 + offset) = true := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hoffset
          obtain ⟨result, hresult⟩ := Part.dom_iff_mem.mp (ih (start + 1) hnext)
          apply Part.dom_iff_mem.mpr
          refine ⟨result, PFun.mem_fix_iff.mpr (Or.inr ⟨[start + 1], ?_, hresult⟩)⟩
          simp [hbody, hstop]

/-- Supplying the exact finite-game test yields the required high-level search semantics. -/
theorem search_dom_iff_halts (test : Code) (htest : TestsCounterexamples test) :
    (search test |>.eval []).Dom ↔ Search.Halts := by
  change (Part.some [1] >>= (Code.fix (searchBody test)).eval).Dom ↔ Search.Halts
  simp only [Bind.bind, Part.bind_some]
  rw [fix_search_body_dom_iff test Search.isCounterexample htest]
  constructor
  · rintro ⟨offset, hoffset⟩
    exact ⟨offset + 1, (Search.run_for_eq_none_iff 1 (offset + 1)).mpr
      ⟨offset, by omega, hoffset⟩⟩
  · rintro ⟨steps, hsteps⟩
    obtain ⟨offset, _, hoffset⟩ := (Search.run_for_eq_none_iff 1 steps).mp hsteps
    exact ⟨offset, hoffset⟩

/-- The explicit outer loop is ready for any subsequently constructed certified test program. -/
theorem search_dom_iff_not_conjecture (test : Code) (htest : TestsCounterexamples test) :
    (search test |>.eval []).Dom ↔ ¬ Search.Conjecture :=
  (search_dom_iff_halts test htest).trans Search.halts_iff_not_conjecture

/-- The concrete predicate program satisfies the outer search's exact executable contract. -/
theorem counterexample_code_tests : TestsCounterexamples counterexampleCode := by
  intro n
  simpa only [interval_test_eq] using counterexample_code_eval n []

/-- The complete concrete Catch-Up counterexample-search source program. -/
def program : Code := search counterexampleCode

/-- The specific source program halts precisely when the high-level search halts. -/
theorem program_dom_iff_halts : (program.eval []).Dom ↔ Search.Halts :=
  search_dom_iff_halts counterexampleCode counterexample_code_tests

/-- The specific finite source program halts exactly when the literal conjecture is false. -/
theorem program_dom_iff_not_conjecture : (program.eval []).Dom ↔ ¬ Search.Conjecture :=
  program_dom_iff_halts.trans Search.halts_iff_not_conjecture

end CatchUp.Machine.Program
