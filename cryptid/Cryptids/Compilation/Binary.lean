/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines

/-!
# Binary Post-machine compilation

`Binary.compile` translates a finite Bool Post machine into the write-and-move semantics of
`ConjectureMachines.Machine`. A move takes one target step. A write takes two: write and move
right, then preserve the neighbouring cell and move left. The second block of states is used
only for this return trip. `Binary.compile_haltsFrom` covers every source configuration.
-/

@[expose] public section

namespace ConjectureMachines.Compilation.Binary

open Turing StateTransition

variable {q : ℕ} [NeZero q]

/-- Bool symbols as binary machine symbols; `false` is the blank `0`. -/
def encodeSymbol : PointedMap Bool (Fin 2) := ⟨finTwoEquiv.symm, rfl⟩

/-- Decode a binary machine symbol. -/
def decodeSymbol : Fin 2 → Bool := finTwoEquiv

@[simp] theorem decode_encode (b : Bool) : decodeSymbol (encodeSymbol b) = b :=
  finTwoEquiv.apply_symm_apply b

@[simp] theorem encode_decode (a : Fin 2) : encodeSymbol (decodeSymbol a) = a :=
  finTwoEquiv.symm_apply_apply a

/-- The unchanged tape geometry with Bool symbols encoded as `Fin 2`. -/
def encodeTape (T : Tape Bool) : Tape (Fin 2) := T.map encodeSymbol

/-- Main states occupy the first block, in source-state order. -/
def mainState (i : Fin q) : Fin (q + q) := i.castAdd q

/-- The second block records the destination of a write during its right/left bounce. -/
def bounceState (i : Fin q) : Fin (q + q) := Fin.natAdd q i

@[simp] theorem mainState_zero : mainState (0 : Fin q) = 0 := rfl

/-- Compile a Bool Post machine, with exactly `q + q` target states. -/
def compile (M : TM0.Machine Bool (Fin q)) : Machine (q + q) 2 where
  transition s a := Fin.addCases
    (fun i ↦ (M i (decodeSymbol a)).map fun ⟨j, cmd⟩ ↦ match cmd with
      | .move d => (a, d, mainState j)
      | .write b => (encodeSymbol b, .right, bounceState j))
    (fun i ↦ some (a, .left, mainState i)) s

/-- Match a source configuration at a macro-step boundary. -/
def trCfg (c : TM0.Cfg Bool (Fin q)) : Cfg (q + q) 2 :=
  ⟨mainState c.q, encodeTape c.Tape⟩

/-- Return states have a transition on both symbols, so they cannot halt. -/
@[simp] theorem compile_bounce (M : TM0.Machine Bool (Fin q)) (i : Fin q) (a : Fin 2) :
    (compile M).transition (bounceState i) a = some (a, .left, mainState i) := by
  simp only [compile, bounceState, Fin.addCases_right]

/-- Main states dispatch exactly the source instruction under the decoded symbol. -/
theorem compile_main (M : TM0.Machine Bool (Fin q)) (i : Fin q) (a : Fin 2) :
    (compile M).transition (mainState i) a =
      (M i (decodeSymbol a)).map (fun ⟨j, cmd⟩ ↦ match cmd with
        | .move d => (a, d, mainState j)
        | .write b => (encodeSymbol b, .right, bounceState j)) := by
  simp [compile, mainState]

/-- A return step preserves the current cell and moves left, for every tape. -/
@[simp] theorem compile_step_bounce (M : TM0.Machine Bool (Fin q)) (i : Fin q)
    (T : Tape (Fin 2)) :
    step (compile M) ⟨bounceState i, T⟩ = some ⟨mainState i, T.move .left⟩ := by
  simp [step, Tape.write_self]

/-- Main states halt precisely on the missing source transitions, on arbitrary target tapes. -/
theorem compile_step_main_eq_none_iff (M : TM0.Machine Bool (Fin q)) (i : Fin q)
    (T : Tape (Fin 2)) :
    step (compile M) ⟨mainState i, T⟩ = none ↔ M i (decodeSymbol T.head) = none := by
  simp [step, compile_main]

/-- A source move is exactly one target step, with no change to the tape symbols. -/
theorem compile_step_move (M : TM0.Machine Bool (Fin q)) (i j : Fin q) (T : Tape Bool)
    (d : Dir) (h : M i T.head = some (j, .move d)) :
    step (compile M) (trCfg ⟨i, T⟩) = some (trCfg ⟨j, T.move d⟩) := by
  simp [step, trCfg, compile_main, encodeTape, Tape.map_fst, h, Tape.map_move,
    ← Tape.map_write, Tape.write_self]

/-- The first half of a source write enters the return state one cell to the right. -/
theorem compile_step_write (M : TM0.Machine Bool (Fin q)) (i j : Fin q) (T : Tape Bool)
    (b : Bool) (h : M i T.head = some (j, .write b)) :
    step (compile M) (trCfg ⟨i, T⟩) =
      some ⟨bounceState j, ((encodeTape T).write (encodeSymbol b)).move .right⟩ := by
  simp [step, trCfg, compile_main, encodeTape, Tape.map_fst, h]

/-- The second half of a source write restores the head position and exact written tape. -/
theorem compile_write_return (M : TM0.Machine Bool (Fin q)) (j : Fin q) (T : Tape Bool)
    (b : Bool) :
    step (compile M)
        ⟨bounceState j, ((encodeTape T).write (encodeSymbol b)).move .right⟩ =
      some (trCfg ⟨j, T.write b⟩) := by
  simp [step, trCfg, encodeTape, Tape.map_write, Tape.write_self, Tape.move_right_left]

/-- Each source step is a nonempty target path, and source halts coincide with target halts. -/
theorem compile_respects (M : TM0.Machine Bool (Fin q)) :
    Respects (TM0.step M) (step (compile M)) (fun a b ↦ trCfg a = b) := by
  apply fun_respects.mpr
  intro ⟨i, T⟩
  cases h : M i T.head with
  | none =>
    simp [TM0.step, h, FRespects, step, trCfg, compile_main, encodeTape, Tape.map_fst]
  | some v =>
    rcases v with ⟨j, cmd⟩
    cases cmd with
    | move d =>
      simp only [TM0.step, h, Option.map_some, FRespects]
      exact Relation.TransGen.single (compile_step_move M i j T d h)
    | write b =>
      simp only [TM0.step, h, Option.map_some, FRespects]
      refine Relation.TransGen.head
        (b := ⟨bounceState j, ((encodeTape T).write (encodeSymbol b)).move .right⟩)
        ?_ (Relation.TransGen.single ?_)
      · exact compile_step_write M i j T b h
      · exact compile_write_return M j T b

omit [NeZero q] in
/-- The compiler has one main and one return state per source state. -/
theorem compile_state_count : Fintype.card (Fin (q + q)) = 2 * q := by
  simp [two_mul]

/-- The complete target result is the encoding of the complete source result. -/
theorem compile_eval (M : TM0.Machine Bool (Fin q)) (c : TM0.Cfg Bool (Fin q)) :
    StateTransition.eval (step (compile M)) (trCfg c) =
      trCfg <$> StateTransition.eval (TM0.step M) c :=
  StateTransition.tr_eval' _ _ _ (compile_respects M) c

/-- Forward and reverse halting equivalence from an arbitrary state and tape. -/
theorem compile_haltsFrom (M : TM0.Machine Bool (Fin q)) (c : TM0.Cfg Bool (Fin q)) :
    (StateTransition.eval (step (compile M)) (trCfg c)).Dom ↔
      (StateTransition.eval (TM0.step M) c).Dom :=
  StateTransition.tr_eval_dom (compile_respects M) rfl

/-- The source's default state is target state zero; input cells and head position agree. -/
@[simp] theorem trCfg_init (l : List Bool) :
    trCfg (TM0.init (Λ := Fin q) l) = ⟨0, Tape.mk₁ (l.map encodeSymbol)⟩ := by
  simp only [trCfg, TM0.init, encodeTape, Tape.map_mk₁]
  rfl

/-- With no input, the correspondence identifies the two all-blank initial configurations. -/
theorem trCfg_blank : trCfg (TM0.init (Λ := Fin q) []) = init := by
  simpa only [init, List.map_nil] using trCfg_init (q := q) []

/-- Halting equivalence on an arbitrary finite input, using raw configuration semantics. -/
theorem compile_halts_init (M : TM0.Machine Bool (Fin q)) (l : List Bool) :
    (StateTransition.eval (step (compile M)) ⟨0, Tape.mk₁ (l.map encodeSymbol)⟩).Dom ↔
      (StateTransition.eval (TM0.step M) (TM0.init l)).Dom := by
  simpa only [trCfg_init] using compile_haltsFrom M (TM0.init l)

/-- Halting equivalence on an arbitrary finite input, using Mathlib's `TM0.eval`. -/
theorem compile_halts_input (M : TM0.Machine Bool (Fin q)) (l : List Bool) :
    (StateTransition.eval (step (compile M)) ⟨0, Tape.mk₁ (l.map encodeSymbol)⟩).Dom ↔
      (TM0.eval M l).Dom := by
  exact compile_halts_init M l

/-- In particular, the blank target machine halts exactly when the blank source does. -/
theorem compile_halts_blank (M : TM0.Machine Bool (Fin q)) :
    ConjectureMachines.Halts (compile M) ↔ (TM0.eval M []).Dom := by
  simpa only [ConjectureMachines.Halts, init, List.map_nil] using compile_halts_input M []

end ConjectureMachines.Compilation.Binary
