/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.RuntimeData
public import Cryptids.Compilation.CodeVM

/-! # Concrete data wire and startup for the four-stack interpreter

Runtime frames contain only natural words and the saved-value delimiter. Startup moves the
literal root and table from the ordinary TM2 input stack and initializes the halt frame.
-/

@[expose] public section
namespace ConjectureMachines.Compilation.RuntimeWire

open Turing PartrecToTM2 K' StateTransition Relation Function
open CodeDAG (DAG Node)

set_option backward.isDefEq.respectTransparency false

/-- Runtime continuation tags and payloads, in the exact order read by the interpreter. -/
def frameWire : CodeVM.Frame → List Γ'
  | .halt => trList [0]
  | .cons1 right saved next =>
    trList [1] ++ trList saved ++ Γ'.consₗ :: (trList [right] ++ frameWire next)
  | .cons2 head next => trList [2, head] ++ frameWire next
  | .comp left next => trList [3, left] ++ frameWire next
  | .fix body next => trList [4, body] ++ frameWire next

/-- Every table row contributes exactly its three explicit runtime words. -/
def flatTriples (rows : Array Node) : List Nat := rows.toList.flatMap Node.words

/-- Stable interpreter boundaries: values on main, no reverse scratch, table on aux. -/
def configWire (rows : Array Node) (store : Option Γ') : CodeVM.Config → Cfg'
  | .eval pc frame values =>
    Runtime.dataCfg .evaluate store (pc :: values) (flatTriples rows) (frameWire frame)
  | .ret frame values =>
    Runtime.dataCfg .returned store values (flatTriples rows) (frameWire frame)
  | .halt values =>
    Runtime.dataCfg .halt store values (flatTriples rows) []

/-- The whole root, table, delimiter, and argument are literal TM2 input data. -/
def rawInput (root : Nat) (table values : List Nat) : List Γ' :=
  trList [root] ++ trList table ++ Γ'.consₗ :: trList values

/-- Input for a concrete shared program table. -/
def input (dag : DAG) (values : List Nat) : List Γ' :=
  rawInput dag.root (flatTriples dag.rows) values

/-- Actual startup state with all symbols on main and the three other stacks empty. -/
def initial (dag : DAG) (values : List Nat) : Cfg' :=
  ⟨some (Runtime.label .start), none, K'.elim (input dag values) [] [] []⟩

/-- The table delimiter is found after all encoded table words, including zero words. -/
theorem split_table (table values : List Nat) :
    splitAtPred Runtime.endFrame (trList table ++ Γ'.consₗ :: trList values) =
      (trList table, some Γ'.consₗ, trList values) := by
  apply splitAtPred_eq
  · intro symbol member
    exact Bool.decide_false (trList_ne_consₗ table symbol member)
  · exact ⟨rfl, rfl⟩

/-- Startup is an actual nonempty TM2 path, with no table validity or evaluation assumption. -/
theorem startup_reaches (root : Nat) (table values : List Nat) (store : Option Γ') :
    Reaches₁ (TM2.step Runtime.machine)
      ⟨some (Runtime.label .start), store, K'.elim (rawInput root table values) [] [] []⟩
      (Runtime.dataCfg .evaluate none (root :: values) table (frameWire .halt)) := by
  let restoreRoot := Runtime.moveWord stack main
    (Runtime.pushWord stack 0 (Runtime.label .evaluate))
  let clearMarker := Λ'.clear (fun _ ↦ true) main restoreRoot
  let moveTable := move₂ Runtime.endFrame main aux clearMarker
  have first := Runtime.moveWord_reaches main stack moveTable store
    (K'.elim (rawInput root table values) [] [] []) root
    (trList table ++ Γ'.consₗ :: trList values) (by decide) (by decide) (by decide) rfl
    (by simp [rawInput, trList, List.append_assoc])
  simp only [elim_update_main, elim_update_stack, elim_stack, List.append_nil] at first
  have second := RuntimeMacros.move₂_ok Runtime.agrees
    (p := Runtime.endFrame) (k₁ := main) (k₂ := aux) (q := clearMarker) (s := none)
    (S := K'.elim (trList table ++ Γ'.consₗ :: trList values) [] [] (trList [root]))
    (by decide) rfl (split_table table values)
  simp only [Option.elim, elim_update_main, elim_update_aux, elim_aux, List.append_nil] at second
  have third := RuntimeMacros.clear_ok Runtime.agrees
    (p := fun _ ↦ true) (k := main) (q := restoreRoot) (s := none)
    (S := K'.elim (Γ'.consₗ :: trList values) [] (trList table) (trList [root]))
    (L₁ := []) (o := some Γ'.consₗ) (L₂ := trList values) rfl
  simp only [elim_update_main] at third
  have fourth := Runtime.moveWord_reaches stack main
    (Runtime.pushWord stack 0 (Runtime.label .evaluate)) (some Γ'.consₗ)
    (K'.elim (trList values) [] (trList table) (trList [root])) root []
    (by decide) (by decide) (by decide) rfl (by simp [trList])
  simp only [elim_update_stack, elim_update_main, elim_main,
    ← Runtime.trList_append, List.singleton_append] at fourth
  have fifth := Runtime.pushWord_reaches stack 0 (Runtime.label .evaluate) none
    (K'.elim (trList (root :: values)) [] (trList table) [])
  simp only [elim_update_stack, elim_stack, List.append_nil] at fifth
  have launch := Runtime.phase_reaches .start store
    (K'.elim (rawInput root table values) [] [] []) (by decide)
  exact ((((launch.trans first).trans second).trans third).trans fourth).trans_left fifth

/-- Startup gives exactly the initial CodeVM evaluation wire, including its halt continuation. -/
theorem initial_reaches (dag : DAG) (values : List Nat) :
    Reaches₁ (TM2.step Runtime.machine) (initial dag values)
      (configWire dag.rows none (CodeVM.init dag values)) :=
  startup_reaches dag.root (flatTriples dag.rows) values none

/-- The explicit startup state is the ordinary TM2 initializer with default label start. -/
theorem initial_eq_TM2_init (dag : DAG) (values : List Nat) :
    letI : Inhabited Λ' := ⟨Runtime.label .start⟩
    initial dag values = TM2.init main (input dag values) := by
  dsimp only [initial, TM2.init]
  congr 1
  funext k
  cases k <;> rfl

/-- The ordinary TM2 initializer executes the complete concrete startup. -/
theorem tm2_init_reaches (dag : DAG) (values : List Nat) :
    letI : Inhabited Λ' := ⟨Runtime.label .start⟩
    Reaches₁ (TM2.step Runtime.machine) (TM2.init main (input dag values))
      (configWire dag.rows none (CodeVM.init dag values)) := by
  rw [← initial_eq_TM2_init]
  exact initial_reaches dag values

/-- Flattening preserves every row, including rows with zero-valued operands. -/
theorem flatTriples_length (rows : Array Node) : (flatTriples rows).length = 3 * rows.size := by
  have length (nodes : List Node) : (nodes.flatMap Node.words).length = 3 * nodes.length := by
    induction nodes with
    | nil => rfl
    | cons node nodes ih => simp [Node.words_length, ih, Nat.mul_add, Nat.add_comm]
  simpa only [flatTriples, Array.length_toList] using length rows.toList


@[simp] theorem frameWire_halt : frameWire .halt = trList [0] := rfl

@[simp] theorem frameWire_cons1 (right : Nat) (saved : List Nat) (next : CodeVM.Frame) :
    frameWire (.cons1 right saved next) =
      trList [1] ++ trList saved ++ Γ'.consₗ :: (trList [right] ++ frameWire next) := rfl

@[simp] theorem frameWire_cons2 (head : Nat) (next : CodeVM.Frame) :
    frameWire (.cons2 head next) = trList [2, head] ++ frameWire next := rfl

@[simp] theorem frameWire_comp (left : Nat) (next : CodeVM.Frame) :
    frameWire (.comp left next) = trList [3, left] ++ frameWire next := rfl

@[simp] theorem frameWire_fix (body : Nat) (next : CodeVM.Frame) :
    frameWire (.fix body next) = trList [4, body] ++ frameWire next := rfl

@[simp] theorem configWire_eval (rows : Array Node) (store : Option Γ')
    (pc : Nat) (frame : CodeVM.Frame) (values : List Nat) :
    configWire rows store (.eval pc frame values) =
      Runtime.dataCfg .evaluate store (pc :: values) (flatTriples rows) (frameWire frame) := rfl

@[simp] theorem configWire_ret (rows : Array Node) (store : Option Γ')
    (frame : CodeVM.Frame) (values : List Nat) :
    configWire rows store (.ret frame values) =
      Runtime.dataCfg .returned store values (flatTriples rows) (frameWire frame) := rfl

/-- Unlike a live halt continuation, a final VM configuration has consumed its halt tag. -/
@[simp] theorem configWire_halt (rows : Array Node) (store : Option Γ') (values : List Nat) :
    configWire rows store (.halt values) =
      Runtime.dataCfg .halt store values (flatTriples rows) [] := rfl

@[simp] theorem configWire_store (rows : Array Node) (store : Option Γ') (cfg : CodeVM.Config) :
    (configWire rows store cfg).var = store := by cases cfg <;> rfl

@[simp] theorem configWire_rev (rows : Array Node) (store : Option Γ') (cfg : CodeVM.Config) :
    (configWire rows store cfg).stk rev = [] := by cases cfg <;> rfl

@[simp] theorem configWire_aux (rows : Array Node) (store : Option Γ') (cfg : CodeVM.Config) :
    (configWire rows store cfg).stk aux = trList (flatTriples rows) := by cases cfg <;> rfl

@[simp] theorem configWire_eval_main (rows : Array Node) (store : Option Γ')
    (pc : Nat) (frame : CodeVM.Frame) (values : List Nat) :
    (configWire rows store (.eval pc frame values)).stk main = trList (pc :: values) := rfl

@[simp] theorem configWire_ret_main (rows : Array Node) (store : Option Γ')
    (frame : CodeVM.Frame) (values : List Nat) :
    (configWire rows store (.ret frame values)).stk main = trList values := rfl

@[simp] theorem configWire_eval_stack (rows : Array Node) (store : Option Γ')
    (pc : Nat) (frame : CodeVM.Frame) (values : List Nat) :
    (configWire rows store (.eval pc frame values)).stk stack = frameWire frame := rfl

@[simp] theorem configWire_ret_stack (rows : Array Node) (store : Option Γ')
    (frame : CodeVM.Frame) (values : List Nat) :
    (configWire rows store (.ret frame values)).stk stack = frameWire frame := rfl

@[simp] theorem configWire_halt_stack (rows : Array Node) (store : Option Γ') (values : List Nat) :
    (configWire rows store (.halt values)).stk stack = [] := rfl

@[simp] theorem initial_main (dag : DAG) (values : List Nat) :
    (initial dag values).stk main = input dag values := rfl

@[simp] theorem initial_rev (dag : DAG) (values : List Nat) :
    (initial dag values).stk rev = [] := rfl

@[simp] theorem initial_aux (dag : DAG) (values : List Nat) :
    (initial dag values).stk aux = [] := rfl

@[simp] theorem initial_stack (dag : DAG) (values : List Nat) :
    (initial dag values).stk stack = [] := rfl

end ConjectureMachines.Compilation.RuntimeWire
