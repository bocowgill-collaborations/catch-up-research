/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Mathlib.Tactic

/-!
# Self-initializing binary machines

An initializer is a finite sequence of writes and moves. Prepending it adds exactly one state
per instruction, has no missing transitions, and enters the original machine at state zero.
The binary input writer constructs its entire finite input from a blank tape and returns the
head to its starting cell. Neither the input nor the return trip is free in the state count.
-/

@[expose] public section
namespace ConjectureMachines.Compilation.Init
open Turing StateTransition

/-- `none` preserves the scanned bit; `some bit` writes that bit before moving. -/
abbrev Instruction := Option (Fin 2) × Dir

def execute (action : Instruction) (tape : Tape (Fin 2)) : Tape (Fin 2) :=
  (tape.write (action.1.getD tape.head)).move action.2

def executeList : List Instruction → Tape (Fin 2) → Tape (Fin 2)
  | [], tape => tape
  | action :: rest, tape => executeList rest (execute action tape)

variable {q : ℕ} [NeZero q]

/-- Constant-time numeric case split. `Fin.cases` computes through a recursive recursor. -/
def caseZero {α : Sort*} {n : ℕ} (zero : α) (succ : Fin n → α) (state : Fin (n + 1)) : α :=
  if h : state.val = 0 then zero else succ ⟨state.val - 1, by have := state.isLt; omega⟩

@[simp] theorem caseZero_zero {α : Sort*} {n : ℕ} (zero : α) (succ : Fin n → α) :
    caseZero zero succ 0 = zero := rfl

@[simp] theorem caseZero_succ {α : Sort*} {n : ℕ} (zero : α) (succ : Fin n → α)
    (state : Fin n) : caseZero zero succ state.succ = succ state := by
  simp [caseZero]

/-- Shift each original state by one, reserving zero for a total initializer instruction. -/
def prependMachine (action : Instruction) (machine : Machine q 2) : Machine (q + 1) 2 :=
  ⟨fun state bit ↦ caseZero
    (some (action.1.getD bit, action.2, (0 : Fin q).succ))
    (fun old ↦ (machine.transition old bit).map fun (write, dir, next) ↦
      (write, dir, next.succ)) state⟩

def embed (config : Cfg q 2) : Cfg (q + 1) 2 := ⟨config.state.succ, config.tape⟩

theorem step_embed (action : Instruction) (machine : Machine q 2) (config : Cfg q 2) :
    step (prependMachine action machine) (embed config) = (step machine config).map embed := by
  cases config with
  | mk state tape =>
      simp only [step, embed, prependMachine, caseZero_succ]
      cases machine.transition state tape.head <;> rfl

theorem prepend_respects (action : Instruction) (machine : Machine q 2) :
    Respects (step machine) (step (prependMachine action machine))
      (fun first second ↦ embed first = second) := by
  intro config target equal
  subst target
  rw [step_embed]
  cases h : step machine config with
  | none => rfl
  | some next => exact ⟨embed next, rfl, .single (by rw [step_embed, h]; rfl)⟩

/-- Exactly one initializer step, on either scanned symbol. -/
theorem prepend_first (action : Instruction) (machine : Machine q 2) (tape : Tape (Fin 2)) :
    step (prependMachine action machine) ⟨0, tape⟩ =
      some (embed (⟨0, execute action tape⟩ : Cfg q 2)) :=
  rfl

/-- Halting at state zero on an explicit tape, before blank initialization is composed. -/
def HaltsOn (machine : Machine q 2) (tape : Tape (Fin 2)) : Prop :=
  (eval (step machine) ⟨0, tape⟩).Dom

theorem prepend_haltsOn (action : Instruction) (machine : Machine q 2) (tape : Tape (Fin 2)) :
    HaltsOn (prependMachine action machine) tape ↔ HaltsOn machine (execute action tape) := by
  have prefixStep := reaches_eval (.single (prepend_first action machine tape))
  have simulated := tr_eval_dom (prepend_respects action machine)
    (show embed (⟨0, execute action tape⟩ : Cfg q 2) = _ from rfl)
  exact (Iff.of_eq (congrArg Part.Dom prefixStep)).trans simulated

theorem executeList_append (first second : List Instruction) (tape : Tape (Fin 2)) :
    executeList (first ++ second) tape = executeList second (executeList first tape) := by
  induction first generalizing tape with
  | nil => rfl
  | cons action rest ih => exact ih (execute action tape)

/-- One fresh state per prependAll instruction; the wrapped machine's states are all counted. -/
def prepend (action : Instruction) (machine : BundledMachine 2) : BundledMachine 2 :=
  ⟨machine.states + 1, prependMachine action machine.toMachine⟩

def prependAll : List Instruction → BundledMachine 2 → BundledMachine 2
  | [], machine => machine
  | action :: rest, machine => prepend action (prependAll rest machine)

theorem prefix_states (actions : List Instruction) (machine : BundledMachine 2) :
    (prependAll actions machine).states = machine.states + actions.length := by
  induction actions with
  | nil => rfl
  | cons action rest ih => simp only [prependAll, prepend, List.length_cons, ih, Nat.add_assoc]

theorem prefix_haltsOn (actions : List Instruction) (machine : BundledMachine 2)
    (tape : Tape (Fin 2)) :
    HaltsOn (prependAll actions machine).toMachine tape ↔
      HaltsOn machine.toMachine (executeList actions tape) := by
  induction actions generalizing tape with
  | nil => rfl
  | cons action rest ih =>
      exact (prepend_haltsOn action (prependAll rest machine).toMachine tape).trans
        (ih (execute action tape))

/-- Embed a body configuration after all prefix control states. -/
def embedAll (actions : List Instruction) (machine : BundledMachine 2)
    (config : Cfg machine.states 2) : Cfg (prependAll actions machine).states 2 :=
  match actions with
  | [] => config
  | _ :: rest => embed (embedAll rest machine config)

@[simp] theorem embedAll_tape (actions : List Instruction) (machine : BundledMachine 2)
    (config : Cfg machine.states 2) : (embedAll actions machine config).tape = config.tape := by
  induction actions with
  | nil => rfl
  | cons action rest ih => exact ih

theorem prefix_reaches (actions : List Instruction) (machine : BundledMachine 2)
    (tape : Tape (Fin 2)) :
    Reaches (step (prependAll actions machine).toMachine) ⟨0, tape⟩
      (embedAll actions machine ⟨0, executeList actions tape⟩) := by
  induction actions generalizing tape with
  | nil => exact .refl
  | cons action rest ih =>
      have lifted := tr_reaches (prepend_respects action (prependAll rest machine).toMachine)
        rfl (ih (execute action tape))
      obtain ⟨target, equal, path⟩ := lifted
      have first : Reaches (step (prependMachine action (prependAll rest machine).toMachine))
          ⟨0, tape⟩ (embed (⟨0, execute action tape⟩ : Cfg (prependAll rest machine).states 2)) :=
        .single (prepend_first action (prependAll rest machine).toMachine tape)
      rw [← equal] at path
      exact first.trans path

/-- Write the next bit and recurse to its right, then return one cell left. -/
def writer : List (Fin 2) → List Instruction
  | [] => []
  | bit :: rest => (some bit, .right) :: (writer rest ++ [(none, .left)])

theorem writer_length (bits : List (Fin 2)) : (writer bits).length = 2 * bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      simp only [writer, List.length_cons, List.length_append, ih, List.length_nil]
      omega

/-- The writer leaves every cell on its left unchanged and restores the original head. -/
theorem writer_correct (bits : List (Fin 2)) (left : ListBlank (Fin 2)) :
    executeList (writer bits) (Tape.mk' left (ListBlank.mk [])) =
      Tape.mk' left (ListBlank.mk bits) := by
  induction bits generalizing left with
  | nil => rfl
  | cons bit rest ih =>
      simp only [writer, executeList, executeList_append, execute, Option.getD_some,
        Option.getD_none, Tape.write_self, Tape.write_mk', Tape.move_right_mk']
      simp only [ListBlank.head_cons, ListBlank.tail_cons]
      simp only [ListBlank.tail_mk, List.tail_nil, ih, Tape.move_left_mk',
        ListBlank.tail_cons, ListBlank.head_cons, ListBlank.cons_mk]

/-- A complete blank-tape machine that constructs its input before entering the body. -/
def initialise (bits : List (Fin 2)) (machine : BundledMachine 2) : BundledMachine 2 :=
  prependAll (writer bits) machine

theorem initialise_states (bits : List (Fin 2)) (machine : BundledMachine 2) :
    (initialise bits machine).states = machine.states + 2 * bits.length := by
  rw [initialise, prefix_states, writer_length]

theorem initialise_halts (bits : List (Fin 2)) (machine : BundledMachine 2) :
    (initialise bits machine).Halts ↔ HaltsOn machine.toMachine (Tape.mk₁ bits) := by
  change HaltsOn (prependAll (writer bits) machine).toMachine (Tape.mk₁ []) ↔ _
  rw [prefix_haltsOn]
  change HaltsOn machine.toMachine (executeList (writer bits)
    (Tape.mk' (ListBlank.mk []) (ListBlank.mk []))) ↔ _
  rw [writer_correct]
  rfl

/-- The full initializer reaches the body with exactly the specified input and head position. -/
theorem initialise_reaches (bits : List (Fin 2)) (machine : BundledMachine 2) :
    Reaches (step (initialise bits machine).toMachine) ConjectureMachines.init
      (embedAll (writer bits) machine ⟨0, Tape.mk₁ bits⟩) := by
  have path := prefix_reaches (writer bits) machine (Tape.mk₁ [])
  have written : executeList (writer bits) (Tape.mk₁ []) = Tape.mk₁ bits :=
    writer_correct bits (ListBlank.mk [])
  rw [written] at path
  exact path

end ConjectureMachines.Compilation.Init
