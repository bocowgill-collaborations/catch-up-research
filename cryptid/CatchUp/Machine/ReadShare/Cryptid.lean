import CatchUp.Machine.ReusedCryptid
import CatchUp.Machine.ReadShare.Simulation

namespace CatchUp.Machine.ReadShare
open Turing PartrecToTM2 ConjectureMachines Compilation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

abbrev body : BundledMachine 2 :=
  ⟨GraphPost.stateCount raw.count 5 + GraphPost.stateCount raw.count 5,
    Compilation.Binary.compile post⟩

theorem post_count : GraphPost.stateCount raw.count 5 = 194443791 := by
  rw [node_count]
  rfl

theorem body_states : body.states = 388887582 := by
  change _ + _ = _
  rw [post_count]

/-- Same complete program bits as the preserved baseline; no new tape/storage format. -/
abbrev bits := ReusedCryptid.bits
abbrev generated := FlatInit.initialise bits body

theorem generated_halts : generated.Halts ↔ ¬ Search.Conjecture := by
  apply (FlatInit.initialise_halts bits body).trans
  have lowering := Compilation.Binary.compile_halts_input post
    (ReusedRuntime.dagInput Literal.dag [])
  have interpreter := (post_halts_iff (ReusedRuntime.dagInput Literal.dag [])).trans
    ((Chess.Compilation.Templates.runtime_eval_dom K'.main (RuntimeWire.input Literal.dag [])).trans
      (RuntimeProof.tm2_halts Literal.dag Literal.valid []))
  rw [Literal.correct] at interpreter
  have result := (lowering.trans interpreter).trans Program.program_dom_iff_not_conjecture
  simpa only [Init.HaltsOn, ReusedCryptid.bits, ReusedRuntime.dagBits,
    List.toList_toArray] using result

attribute [local irreducible] ReusedCryptid.bits

theorem generated_states : generated.states = 388957212 := by
  rw [FlatInit.initialise_states, body_states, ReusedCryptid.bits_size]

def M : Machine 388957212 2 :=
  Chess.Compilation.Image.castMachine generated_states generated.toMachine

theorem halts_iff_not_conjecture : Halts M ↔ ¬ Search.Conjecture :=
  (Chess.Compilation.Image.cast_halts generated_states generated.toMachine).trans generated_halts

theorem initializes : FlatInit.runFrom M 69630 ConjectureMachines.init =
    some (⟨⟨69630, by decide⟩, Tape.mk₁ bits.toList⟩ : Cfg 388957212 2) :=
  Chess.Compilation.Image.initialise_cast_paid_run bits body generated_states
    (by rw [ReusedCryptid.bits_size]) (by decide)

theorem states_saved : 388957212 + 48890 = 389006102 := by decide +kernel

end CatchUp.Machine.ReadShare
