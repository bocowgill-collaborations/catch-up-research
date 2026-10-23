/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.Init

/-! # Flat array-indexed blank binary initialization

The first `n` states write the array to the right; the next `n` preserve and move left.
The body is a direct numeric state offset. No nested control wrappers are constructed.
-/

@[expose] public section
namespace ConjectureMachines.Compilation.FlatInit

open Turing StateTransition Relation

set_option backward.isDefEq.respectTransparency false

instance totalStates_neZero (bits : Array (Fin 2)) (body : BundledMachine 2) :
    NeZero (body.states + 2 * bits.size) := ⟨by have := NeZero.ne body.states; omega⟩

/-- Numeric embedding into the body block after all initializer states. -/
def bodyState (bits : Array (Fin 2)) (body : BundledMachine 2)
    (state : Fin body.states) : Fin (body.states + 2 * bits.size) :=
  ⟨2 * bits.size + state.val, by have := state.isLt; omega⟩

/-- A prefix index may include the final boundary, which is body state zero. -/
def prefixState (bits : Array (Fin 2)) (body : BundledMachine 2) (i : Nat)
    (bound : i ≤ 2 * bits.size) : Fin (body.states + 2 * bits.size) :=
  ⟨i, by have := NeZero.ne body.states; omega⟩

/-- One direct array read in the write block; preserve and move left in the return block. -/
def actionAt (bits : Array (Fin 2)) (i : Nat) : Init.Instruction :=
  if bound : i < bits.size then (some bits[i], .right) else (none, .left)

/-- Flat transition construction with two numeric ranges and an unchanged body dispatch. -/
def machine (bits : Array (Fin 2)) (body : BundledMachine 2) :
    Machine (body.states + 2 * bits.size) 2 where
  transition state bit :=
    if inPrefix : state.val < 2 * bits.size then
      let action := actionAt bits state.val
      some (action.1.getD bit, action.2,
        ⟨state.val + 1, by have := NeZero.ne body.states; omega⟩)
    else
      (body.toMachine.transition
        ⟨state.val - 2 * bits.size, by have := state.isLt; omega⟩ bit).map
          (fun (write, dir, next) ↦ (write, dir, bodyState bits body next))

/-- Constant-depth machine construction over the array and existing body transition function. -/
def initialise (bits : Array (Fin 2)) (body : BundledMachine 2) : BundledMachine 2 :=
  ⟨body.states + 2 * bits.size, machine bits body⟩

/-- Shift body states numerically without changing any tape cell. -/
def embed (bits : Array (Fin 2)) (body : BundledMachine 2)
    (cfg : Cfg body.states 2) : Cfg (body.states + 2 * bits.size) 2 :=
  ⟨bodyState bits body cfg.state, cfg.tape⟩

/-- A proof-only linear list of the same write block followed by the return block. -/
def actions (bits : Array (Fin 2)) : List Init.Instruction :=
  bits.toList.map (fun bit ↦ (some bit, .right)) ++ List.replicate bits.size (none, .left)

@[simp] theorem actions_length (bits : Array (Fin 2)) : (actions bits).length = 2 * bits.size := by
  simp [actions, Nat.two_mul]

/-- Every prefix instruction agrees with its direct numeric/array dispatch. -/
theorem actions_get (bits : Array (Fin 2)) (i : Nat) (bound : i < 2 * bits.size) :
    (actions bits)[i]? = some (actionAt bits i) := by
  by_cases write : i < bits.size
  · simp [actions, actionAt, write, List.getElem?_append_left]
  · rw [actions, List.getElem?_append_right (by simpa using Nat.le_of_not_gt write)]
    simp [actionAt, write, show i - bits.size < bits.size by omega]

theorem actions_getElem (bits : Array (Fin 2)) (i : Nat) (bound : i < 2 * bits.size) :
    (actions bits)[i]'(by simpa using bound) = actionAt bits i := by
  have read := actions_get bits i bound
  simpa only [List.getElem?_eq_getElem (l := actions bits) (i := i)
    (by simpa using bound), Option.some.injEq] using read

/-- The proof list equals the frozen writer sequence; execution never calls that writer. -/
theorem writer_eq_actions (bits : List (Fin 2)) :
    Init.writer bits = bits.map (fun bit ↦ (some bit, .right)) ++
      List.replicate bits.length (none, .left) := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
    simp only [Init.writer, ih, List.map_cons, List.length_cons, List.cons_append]
    rw [List.replicate_succ']
    simp only [List.append_assoc]

/-- Blank writing leaves the exact bit string at the original head, with any left tape unchanged. -/
theorem actions_correct (bits : Array (Fin 2)) (left : ListBlank (Fin 2)) :
    Init.executeList (actions bits) (Tape.mk' left (ListBlank.mk [])) =
      Tape.mk' left (ListBlank.mk bits.toList) := by
  have sequence : actions bits = Init.writer bits.toList := by
    simp only [writer_eq_actions, actions, Array.length_toList]
  rw [sequence]
  exact Init.writer_correct bits.toList left

@[simp] theorem prefixState_zero (bits : Array (Fin 2)) (body : BundledMachine 2) :
    prefixState bits body 0 (by omega) = 0 := rfl

@[simp] theorem prefixState_final (bits : Array (Fin 2)) (body : BundledMachine 2) :
    prefixState bits body (2 * bits.size) (by omega) = bodyState bits body 0 := by
  apply Fin.ext
  simp [prefixState, bodyState]

/-- Each prefix state always has an instruction, on either scanned bit. -/
theorem step_prefix (bits : Array (Fin 2)) (body : BundledMachine 2) (i : Nat)
    (bound : i < 2 * bits.size) (tape : Tape (Fin 2)) :
    step (machine bits body) ⟨prefixState bits body i (by omega), tape⟩ =
      some ⟨prefixState bits body (i + 1) (by omega), Init.execute (actionAt bits i) tape⟩ := by
  simp only [step, machine, prefixState, bound, ↓reduceDIte, Option.map_some, Init.execute]

/-- Ordinary finite execution, used to state the exact initializer step count. -/
def runFrom {q : Nat} (M : Machine q 2) : Nat → Cfg q 2 → Option (Cfg q 2)
  | 0, cfg => some cfg
  | count + 1, cfg => (step M cfg).bind (runFrom M count)

/-- The remaining prefix executes in exactly its remaining number of instructions. -/
theorem prefix_run (bits : Array (Fin 2)) (body : BundledMachine 2) (count : Nat) :
    ∀ (i : Nat) (total : i + count = 2 * bits.size) (tape : Tape (Fin 2)),
      runFrom (machine bits body) count ⟨prefixState bits body i (by omega), tape⟩ =
        some ⟨bodyState bits body 0, Init.executeList ((actions bits).drop i) tape⟩ := by
  induction count with
  | zero =>
    intro i total tape
    have equal : i = 2 * bits.size := by omega
    subst i
    have dropped : (actions bits).drop (2 * bits.size) = [] := by
      rw [← actions_length bits, List.drop_length]
    simp only [runFrom, dropped, Init.executeList, prefixState_final]
  | succ count ih =>
    intro i total tape
    have bound : i < 2 * bits.size := by omega
    have split := List.drop_eq_getElem_cons (l := actions bits)
      (show i < (actions bits).length by simpa using bound)
    rw [actions_getElem bits i bound] at split
    simp only [runFrom, step_prefix bits body i bound, Option.bind_some, split, Init.executeList]
    exact ih (i + 1) (by omega) (Init.execute (actionAt bits i) tape)

@[simp] theorem initialise_states (bits : Array (Fin 2)) (body : BundledMachine 2) :
    (initialise bits body).states = body.states + 2 * bits.size := rfl

/-- Every body step, including a missing transition, is preserved exactly by the numeric offset. -/
theorem step_embed (bits : Array (Fin 2)) (body : BundledMachine 2)
    (cfg : Cfg body.states 2) :
    step (machine bits body) (embed bits body cfg) =
      (step body.toMachine cfg).map (embed bits body) := by
  rcases cfg with ⟨state, tape⟩
  simp only [step, machine, embed, bodyState,
    show ¬2 * bits.size + state.val < 2 * bits.size by omega, ↓reduceDIte,
    Nat.add_sub_cancel_left]
  cases body.toMachine.transition state tape.head <;> rfl

/-- The flat body embedding preserves both successor steps and exact stopping. -/
theorem respects (bits : Array (Fin 2)) (body : BundledMachine 2) :
    Respects (step body.toMachine) (step (machine bits body))
      (fun first second ↦ embed bits body first = second) := by
  intro cfg target equal
  subst target
  rw [step_embed]
  cases move : step body.toMachine cfg with
  | none => rfl
  | some next => exact ⟨embed bits body next, rfl, .single (by rw [step_embed, move]; rfl)⟩

/-- Every finite direct execution gives ordinary reflexive reachability. -/
theorem runFrom_reaches {q : Nat} (M : Machine q 2) (count : Nat) :
    ∀ cfg out, runFrom M count cfg = some out → Reaches (step M) cfg out := by
  induction count with
  | zero => intro cfg out result; cases result; exact .refl
  | succ count ih =>
    intro cfg out result
    cases move : step M cfg with
    | none => simp [runFrom, move] at result
    | some next =>
      have rest : runFrom M count next = some out := by simpa [runFrom, move] using result
      have first : Reaches (step M) cfg next := .single move
      exact first.trans (ih next out rest)

/-- A positive direct execution gives positive reachability. -/
theorem runFrom_reaches_positive {q : Nat} (M : Machine q 2) (count : Nat) (positive : 0 < count)
    (cfg out : Cfg q 2) (result : runFrom M count cfg = some out) :
    Reaches₁ (step M) cfg out := by
  cases count with
  | zero => omega
  | succ count =>
    cases move : step M cfg with
    | none => simp [runFrom, move] at result
    | some next =>
      have rest : runFrom M count next = some out := by simpa [runFrom, move] using result
      exact Relation.TransGen.head' move (runFrom_reaches M count next out rest)

/-- Blank execution enters body state zero with exact input after exactly two steps per bit. -/
theorem initialise_run (bits : Array (Fin 2)) (body : BundledMachine 2) :
    runFrom (initialise bits body).toMachine (2 * bits.size) ConjectureMachines.init =
      some (embed bits body ⟨0, Tape.mk₁ bits.toList⟩) := by
  have result := prefix_run bits body (2 * bits.size) 0 (by omega) (Tape.mk₁ [])
  have written : Init.executeList (actions bits) (Tape.mk₁ []) = Tape.mk₁ bits.toList :=
    actions_correct bits (ListBlank.mk [])
  simpa only [prefixState_zero, List.drop_zero, written, initialise, embed,
    ConjectureMachines.init] using result

/-- The exact written input and restored head are reached even when there are zero input bits. -/
theorem initialise_reaches (bits : Array (Fin 2)) (body : BundledMachine 2) :
    Reaches (step (initialise bits body).toMachine) ConjectureMachines.init
      (embed bits body ⟨0, Tape.mk₁ bits.toList⟩) :=
  runFrom_reaches _ _ _ _ (initialise_run bits body)

/-- Nonempty input has an actual positive prefix path; there are no free write/return actions. -/
theorem initialise_reaches_positive (bits : Array (Fin 2)) (body : BundledMachine 2)
    (nonempty : 0 < bits.size) :
    Reaches₁ (step (initialise bits body).toMachine) ConjectureMachines.init
      (embed bits body ⟨0, Tape.mk₁ bits.toList⟩) :=
  runFrom_reaches_positive _ _ (by omega) _ _ (initialise_run bits body)

/-- Blank-tape halting is equivalent in both directions to the body's explicit input run. -/
theorem initialise_halts (bits : Array (Fin 2)) (body : BundledMachine 2) :
    (initialise bits body).Halts ↔ Init.HaltsOn body.toMachine (Tape.mk₁ bits.toList) := by
  have prefixRun := reaches_eval (initialise_reaches bits body)
  have bodyRun := tr_eval_dom (respects bits body)
    (show embed bits body (⟨0, Tape.mk₁ bits.toList⟩ : Cfg body.states 2) = _ from rfl)
  exact (Iff.of_eq (congrArg Part.Dom prefixRun)).trans bodyRun

/-- Direct write-block rows use exactly one array lookup and advance one state to the right. -/
theorem transition_write (bits : Array (Fin 2)) (body : BundledMachine 2) (i : Nat)
    (bound : i < bits.size) (bit : Fin 2) :
    (machine bits body).transition (prefixState bits body i (by omega)) bit =
      some (bits[i], .right, prefixState bits body (i + 1) (by omega)) := by
  simp [machine, prefixState, actionAt, bound, show i < 2 * bits.size by omega]

/-- Direct return-block rows preserve either scanned bit and advance one state to the left. -/
theorem transition_return (bits : Array (Fin 2)) (body : BundledMachine 2) (i : Nat)
    (bound : i < bits.size) (bit : Fin 2) :
    (machine bits body).transition (prefixState bits body (bits.size + i) (by omega)) bit =
      some (bit, .left, prefixState bits body (bits.size + i + 1) (by omega)) := by
  simp [machine, prefixState, actionAt, show bits.size + i < 2 * bits.size by omega,
    show ¬bits.size + i < bits.size by omega]

/-- Direct body rows preserve every missing transition and offset each existing destination. -/
theorem transition_body (bits : Array (Fin 2)) (body : BundledMachine 2)
    (state : Fin body.states) (bit : Fin 2) :
    (machine bits body).transition (bodyState bits body state) bit =
      (body.toMachine.transition state bit).map
        (fun (write, dir, next) ↦ (write, dir, bodyState bits body next)) := by
  simp only [machine, bodyState, show ¬2 * bits.size + state.val < 2 * bits.size by omega,
    ↓reduceDIte, Nat.add_sub_cancel_left]

@[simp] theorem embed_tape (bits : Array (Fin 2)) (body : BundledMachine 2)
    (cfg : Cfg body.states 2) : (embed bits body cfg).tape = cfg.tape := rfl

@[simp] theorem embed_state_val (bits : Array (Fin 2)) (body : BundledMachine 2)
    (cfg : Cfg body.states 2) :
    (embed bits body cfg).state.val = 2 * bits.size + cfg.state.val := rfl

@[simp] theorem initialise_empty_states (body : BundledMachine 2) :
    (initialise #[] body).states = body.states := rfl

end ConjectureMachines.Compilation.FlatInit
