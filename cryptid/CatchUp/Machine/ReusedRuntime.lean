import Cryptids.Chess.Compilation.Image
import Cryptids.Compilation.RuntimeProof

/-! Reuse the existing fixed interpreter and shared graph, with arbitrary paid program data. -/
namespace CatchUp.Machine.ReusedRuntime
open Turing ToPartrec PartrecToTM2
open ConjectureMachines Compilation

def dagInput (dag : CodeDAG.DAG) (values : List Nat) : List Bool :=
  Chess.Compilation.Templates.input K'.main (RuntimeWire.input dag values)

def dagBits (dag : CodeDAG.DAG) (values : List Nat) : Array (Fin 2) :=
  ((dagInput dag values).map Compilation.Binary.encodeSymbol).toArray

abbrev dagBundle (dag : CodeDAG.DAG) (values : List Nat) : BundledMachine 2 :=
  FlatInit.initialise (dagBits dag values) Chess.Compilation.Image.body

/-- Literal-table reuse avoids reducing the untrusted compiler during certificate checking. -/
theorem dag_halts_iff (dag : CodeDAG.DAG) (valid : dag.Valid) (values : List Nat) :
    (dagBundle dag values).Halts ↔ (dag.decode.eval values).Dom := by
  apply (FlatInit.initialise_halts (dagBits dag values) Chess.Compilation.Image.body).trans
  have h := (Compilation.Binary.compile_halts_input Chess.Compilation.Image.post
    (dagInput dag values)).trans
    ((Chess.Compilation.Image.post_runtime_dom K'.main (RuntimeWire.input dag values)).trans
      (RuntimeProof.tm2_halts dag valid values))
  simpa only [Init.HaltsOn, dagBits, List.toList_toArray] using h

theorem dag_state_count (dag : CodeDAG.DAG) (values : List Nat) :
    (dagBundle dag values).states = 388936472 + 2 * (dagBits dag values).size := by
  rw [FlatInit.initialise_states, Chess.Compilation.Image.body_states]

/-- The Chess runtime accepts any source program; no chess data enter this input. -/
def input (code : Code) (values : List Nat) : List Bool :=
  Chess.Compilation.Templates.input K'.main (RuntimeWire.input (CodeDAG.compile code) values)

/-- Every source-program bit is created by the blank-tape initializer. -/
def bits (code : Code) (values : List Nat) : Array (Fin 2) :=
  ((input code values).map Compilation.Binary.encodeSymbol).toArray

abbrev bundle (code : Code) (values : List Nat) : BundledMachine 2 :=
  FlatInit.initialise (bits code values) Chess.Compilation.Image.body

/-- Generic reuse preserves both halting directions for every program and input. -/
theorem halts_iff (code : Code) (values : List Nat) :
    (bundle code values).Halts ↔ (code.eval values).Dom := by
  apply (FlatInit.initialise_halts (bits code values) Chess.Compilation.Image.body).trans
  have h := (Compilation.Binary.compile_halts_input Chess.Compilation.Image.post
    (input code values)).trans
    ((Chess.Compilation.Image.post_runtime_dom K'.main
      (RuntimeWire.input (CodeDAG.compile code) values)).trans
      (RuntimeProof.tm2_halts_compiled code values))
  simpa only [Init.HaltsOn,bits,List.toList_toArray] using h

/-- Exact complete state count; the prefix pays for the whole program and its input. -/
theorem state_count (code : Code) (values : List Nat) :
    (bundle code values).states = 388936472 + 2*(bits code values).size := by
  rw [FlatInit.initialise_states,Chess.Compilation.Image.body_states]

/-- Startup actually reaches the body, with the full bit stream and restored head. -/
theorem initializes (code : Code) (values : List Nat) :
    FlatInit.runFrom (bundle code values).toMachine (2*(bits code values).size)
      ConjectureMachines.init =
    some (FlatInit.embed (bits code values) Chess.Compilation.Image.body
      ⟨0,Tape.mk₁ (bits code values).toList⟩) :=
  FlatInit.initialise_run _ _

end CatchUp.Machine.ReusedRuntime
