import CatchUp.Machine.Literal
import CatchUp.Machine.ReusedRuntime

/-! The unchanged Catch-Up search, as data for the reused verified binary interpreter. -/
namespace CatchUp.Machine.ReusedCryptid
open ConjectureMachines Compilation

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def bits := ReusedRuntime.dagBits Literal.dag []
abbrev generated := FlatInit.initialise bits Chess.Compilation.Image.body

/-- The table shares exact syntax; this is not a semantic hash assumption. -/
theorem table_correct : Literal.dag.decode = Program.program := Literal.correct

/-- Complete finite table size, checked by kernel reduction. -/
theorem table_rows : Literal.dag.rows.size = 204 := Literal.row_count

/-- Every table, root and delimiter bit is included. There are no source input arguments. -/
theorem bits_size : bits.size = 34815 := by
  simp only [bits, ReusedRuntime.dagBits, List.size_toArray, List.length_map,
    ReusedRuntime.dagInput, Chess.Compilation.Templates.input,
    Chess.Compilation.Input.encoded_length, Literal.stack_length]
  rfl

theorem generated_halts : generated.Halts ↔ ¬ Search.Conjecture := by
  change (ReusedRuntime.dagBundle Literal.dag []).Halts ↔ ¬ Search.Conjecture
  have runtime := ReusedRuntime.dag_halts_iff Literal.dag Literal.valid []
  rw [table_correct] at runtime
  exact runtime.trans Program.program_dom_iff_not_conjecture

attribute [local irreducible] bits

theorem generated_states : generated.states = 389006102 := by
  rw [FlatInit.initialise_states, Chess.Compilation.Image.body_states, bits_size]

/-- Explicit finite-state transition function; state zero starts on the all-zero tape. -/
def M : Machine 389006102 2 :=
  Chess.Compilation.Image.castMachine generated_states generated.toMachine

/-- Both halting directions, with no assumption about the open conjecture. -/
theorem halts_iff_not_conjecture : Halts M ↔ ¬ Search.Conjecture := by
  apply (Chess.Compilation.Image.cast_halts generated_states generated.toMachine).trans
  exact generated_halts

/-- The exact paid prefix is 69,630 physical transitions from the blank initial tape. -/
theorem initializes :
    FlatInit.runFrom M 69630 ConjectureMachines.init =
      some (⟨⟨69630, by decide⟩, Turing.Tape.mk₁ bits.toList⟩ : Cfg 389006102 2) := by
  exact Chess.Compilation.Image.initialise_cast_paid_run bits
    Chess.Compilation.Image.body generated_states (by rw [bits_size]) (by decide)

end CatchUp.Machine.ReusedCryptid
