/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.RuntimeWire
public import Cryptids.Compilation.RuntimeEval
public import Cryptids.Compilation.RuntimeReturn
public import Cryptids.Compilation.RuntimeDispatch
public import Cryptids.Compilation.RuntimeLookup

/-! # Composition of the fixed interpreter's concrete tape paths -/

@[expose] public section
namespace ConjectureMachines.Compilation.RuntimeProof
open Turing PartrecToTM2 K' StateTransition Relation
open _root_.ConjectureMachines.Compilation.Runtime RuntimeWire CodeVM

set_option backward.isDefEq.respectTransparency false

/-- A final source state is represented after the real TM2 halt instruction has executed. -/
def realize (rows : Array CodeDAG.Node) (store : Option Γ') : CodeVM.Config → Cfg'
  | .halt values => ⟨none, none, K'.elim (trList values) [] (trList (flatTriples rows)) []⟩
  | other => configWire rows store other

theorem halt_continuation (rows : Array CodeDAG.Node) (store : Option Γ') (values : List Nat) :
    Reaches₁ (TM2.step Runtime.machine)
      (realize rows store (.ret .halt values)) (realize rows none (.halt values)) := by
  obtain ⟨middle, first⟩ := return_dispatch_reaches 0 values (flatTriples rows) [] store (by decide)
  exact first.trans (halt_reaches middle values (flatTriples rows) [])

theorem cons1_continuation (rows : Array CodeDAG.Node) (store : Option Γ')
    (values saved : List Nat) (right : Nat) (frame : CodeVM.Frame) :
    ∃ resultStore, Reaches₁ (TM2.step Runtime.machine)
      (realize rows store (.ret (.cons1 right saved frame) values))
      (realize rows resultStore (.eval right (.cons2 values.headI frame) saved)) := by
  obtain ⟨middle, first⟩ := return_dispatch_reaches 1 values (flatTriples rows)
    (trList saved ++ Γ'.consₗ :: (trList [right] ++ frameWire frame)) store (by decide)
  refine ⟨none, ?_⟩
  simpa only [StateTransition.Reaches₁, realize, configWire, frameWire, returnPhase,
    List.append_assoc] using
    first.trans (cons1_reaches middle values saved (flatTriples rows) right (frameWire frame))

theorem cons2_continuation (rows : Array CodeDAG.Node) (store : Option Γ')
    (values : List Nat) (headValue : Nat) (frame : CodeVM.Frame) :
    ∃ resultStore, Reaches₁ (TM2.step Runtime.machine)
      (realize rows store (.ret (.cons2 headValue frame) values))
      (realize rows resultStore (.ret frame (headValue :: values))) := by
  obtain ⟨middle, first⟩ := return_dispatch_reaches 2 values (flatTriples rows)
    (trList [headValue] ++ frameWire frame) store (by decide)
  refine ⟨none, ?_⟩
  simpa only [StateTransition.Reaches₁, realize, configWire, frameWire, returnPhase,
    trList, List.append_assoc, List.nil_append, List.append_nil,
    List.cons_append, List.singleton_append] using
    first.trans (cons2_reaches middle values (flatTriples rows) headValue (frameWire frame))

theorem comp_continuation (rows : Array CodeDAG.Node) (store : Option Γ')
    (values : List Nat) (left : Nat) (frame : CodeVM.Frame) :
    ∃ resultStore, Reaches₁ (TM2.step Runtime.machine)
      (realize rows store (.ret (.comp left frame) values))
      (realize rows resultStore (.eval left frame values)) := by
  obtain ⟨middle, first⟩ := return_dispatch_reaches 3 values (flatTriples rows)
    (trList [left] ++ frameWire frame) store (by decide)
  refine ⟨none, ?_⟩
  simpa only [StateTransition.Reaches₁, realize, configWire, frameWire, returnPhase,
    trList, List.append_assoc, List.nil_append, List.append_nil,
    List.cons_append, List.singleton_append] using
    first.trans (comp1_reaches middle values (flatTriples rows) left (frameWire frame))

theorem fix_continuation (rows : Array CodeDAG.Node) (store : Option Γ')
    (values : List Nat) (body : Nat) (frame : CodeVM.Frame) :
    ∃ resultStore, Reaches₁ (TM2.step Runtime.machine)
      (realize rows store (.ret (.fix body frame) values))
      (realize rows resultStore
        (if values.headI = 0 then .ret frame values.tail
         else .eval body (.fix body frame) values.tail)) := by
  obtain ⟨middle, first⟩ := return_dispatch_reaches 4 values (flatTriples rows)
    (trList [body] ++ frameWire frame) store (by decide)
  by_cases zero : values.headI = 0
  · refine ⟨some Γ'.cons, ?_⟩
    simpa only [StateTransition.Reaches₁, realize, configWire, frameWire, returnPhase,
      trList, List.append_assoc, List.nil_append, List.append_nil,
      List.cons_append, List.singleton_append, zero, ite_true] using
      first.trans (fix1_zero_reaches middle values (flatTriples rows) body (frameWire frame) zero)
  · refine ⟨none, ?_⟩
    simpa only [StateTransition.Reaches₁, realize, configWire, frameWire, returnPhase,
      trList, List.append_assoc, List.nil_append, List.append_nil,
      List.cons_append, List.singleton_append, zero, ite_false] using
      first.trans (fix1_positive_reaches middle values (flatTriples rows) body
        (frameWire frame) zero)

def afterReturn (frame : CodeVM.Frame) (values : List Nat) : CodeVM.Config :=
  match frame with
  | .halt => .halt values
  | .cons1 right saved next => .eval right (.cons2 values.headI next) saved
  | .cons2 head next => .ret next (head :: values)
  | .comp left next => .eval left next values
  | .fix body next => if values.headI = 0 then .ret next values.tail
      else .eval body (.fix body next) values.tail

theorem step_return (rows : Array CodeDAG.Node) (frame : CodeVM.Frame) (values : List Nat) :
    CodeVM.step rows (.ret frame values) = some (afterReturn frame values) := by
  cases frame <;> rfl

theorem return_refines (rows : Array CodeDAG.Node) (store : Option Γ')
    (frame : CodeVM.Frame) (values : List Nat) :
    ∃ resultStore, Reaches₁ (TM2.step Runtime.machine)
      (realize rows store (.ret frame values))
      (realize rows resultStore (afterReturn frame values)) := by
  cases frame with
  | halt => exact ⟨none, halt_continuation rows store values⟩
  | cons1 right saved next => exact cons1_continuation rows store values saved right next
  | cons2 head next => exact cons2_continuation rows store values head next
  | comp left next => exact comp_continuation rows store values left next
  | fix body next => exact fix_continuation rows store values body next

theorem read_dispatch (rows : Array CodeDAG.Node) (pc : Nat) (node : CodeDAG.Node)
    (row : rows[pc]? = some node) (tag left right : Nat) (words : node.words = [tag, left, right])
    (bound : tag < 7) (store : Option Γ') (values : List Nat) (frame : CodeVM.Frame) :
    ∃ resultStore, Reaches₁ (TM2.step Runtime.machine)
      (realize rows store (.eval pc frame values))
      (dataCfg (opcodePhase tag) resultStore values (flatTriples rows)
        (trList [left, right] ++ frameWire frame)) := by
  have lookup := RuntimeLookup.lookup_node rows pc node row tag left right words store values
    (frameWire frame)
  obtain ⟨resultStore, dispatch⟩ := dispatch_reaches tag values (flatTriples rows)
    (trList [left, right] ++ frameWire frame) none bound
  exact ⟨resultStore, lookup.trans dispatch⟩

def afterEval (node : CodeDAG.Node) (frame : CodeVM.Frame) (values : List Nat) : CodeVM.Config :=
  match node with
  | .zero => .ret frame (0 :: values)
  | .succ => .ret frame [values.headI + 1]
  | .tail => .ret frame values.tail
  | .cons left right => .eval left (.cons1 right values frame) values
  | .comp left right => .eval right (.comp left frame) values
  | .branch left right => if values.headI = 0 then .eval left frame values.tail
      else .eval right frame ((values.headI - 1) :: values.tail)
  | .fix body => .eval body (.fix body frame) values

theorem step_eval (rows : Array CodeDAG.Node) (pc : Nat) (node : CodeDAG.Node)
    (row : rows[pc]? = some node) (frame : CodeVM.Frame) (values : List Nat) :
    CodeVM.step rows (.eval pc frame values) = some (afterEval node frame values) := by
  simp only [CodeVM.step, row, Bind.bind, Option.bind_some, afterEval, Option.pure_def]
  rfl

theorem cons_refines (rows : Array CodeDAG.Node) (pc left right : Nat)
    (row : rows[pc]? = some (.cons left right)) (store : Option Γ')
    (frame : CodeVM.Frame) (values : List Nat) :
    ∃ resultStore, Reaches₁ (TM2.step Runtime.machine)
      (realize rows store (.eval pc frame values))
      (realize rows resultStore (afterEval (.cons left right) frame values)) := by
  obtain ⟨middle, first⟩ := read_dispatch rows pc (.cons left right) row 3 left right rfl
    (by decide) store values frame
  obtain ⟨resultStore, second⟩ := cons_reaches middle values (flatTriples rows) left right
    (frameWire frame)
  refine ⟨resultStore, ?_⟩
  simpa only [StateTransition.Reaches₁, realize, configWire, frameWire, afterEval,
    opcodePhase, codePhase, List.append_assoc] using first.trans second

theorem eval_refines (rows : Array CodeDAG.Node) (pc : Nat) (node : CodeDAG.Node)
    (row : rows[pc]? = some node) (store : Option Γ') (frame : CodeVM.Frame)
    (values : List Nat) :
    ∃ resultStore, Reaches₁ (TM2.step Runtime.machine)
      (realize rows store (.eval pc frame values))
      (realize rows resultStore (afterEval node frame values)) := by
  cases node with
  | zero =>
    obtain ⟨middle, first⟩ := read_dispatch rows pc .zero row 0 0 0 rfl (by decide)
      store values frame
    obtain ⟨resultStore, second⟩ := zero_reaches middle values (flatTriples rows) 0 0
      (frameWire frame)
    exact ⟨resultStore, first.trans second⟩
  | succ =>
    obtain ⟨middle, first⟩ := read_dispatch rows pc .succ row 1 0 0 rfl (by decide)
      store values frame
    obtain ⟨resultStore, second⟩ := successor_reaches middle values (flatTriples rows) 0 0
      (frameWire frame)
    exact ⟨resultStore, first.trans second⟩
  | tail =>
    obtain ⟨middle, first⟩ := read_dispatch rows pc .tail row 2 0 0 rfl (by decide)
      store values frame
    obtain ⟨resultStore, second⟩ := tail_reaches middle values (flatTriples rows) 0 0
      (frameWire frame)
    exact ⟨resultStore, first.trans second⟩
  | cons left right => exact cons_refines rows pc left right row store frame values
  | comp left right =>
    obtain ⟨middle, first⟩ := read_dispatch rows pc (.comp left right) row 4 left right rfl
      (by decide) store values frame
    obtain ⟨resultStore, second⟩ := comp_reaches middle values (flatTriples rows) left right
      (frameWire frame)
    exact ⟨resultStore, first.trans second⟩
  | branch left right =>
    obtain ⟨middle, first⟩ := read_dispatch rows pc (.branch left right) row 5 left right rfl
      (by decide) store values frame
    by_cases zero : values.headI = 0
    · obtain ⟨resultStore, second⟩ := branch_zero_reaches middle values (flatTriples rows)
        left right (frameWire frame) zero
      refine ⟨resultStore, ?_⟩
      simpa only [StateTransition.Reaches₁, realize, configWire, afterEval, zero, ite_true] using
        first.trans second
    · obtain ⟨resultStore, second⟩ := branch_succ_reaches middle values (flatTriples rows)
        left right (frameWire frame) zero
      refine ⟨resultStore, ?_⟩
      simpa only [StateTransition.Reaches₁, realize, configWire, afterEval, zero, ite_false] using
        first.trans second
  | fix body =>
    obtain ⟨middle, first⟩ := read_dispatch rows pc (.fix body) row 6 body 0 rfl
      (by decide) store values frame
    obtain ⟨resultStore, second⟩ := fix_reaches middle values (flatTriples rows) body 0
      (frameWire frame)
    exact ⟨resultStore, first.trans second⟩

/-- Only source well-formedness and exact tape data are maintained; the local store is free. -/
def Related (rows : Array CodeDAG.Node) (source : CodeVM.Config) (target : Cfg') : Prop :=
  source.WF rows.size ∧ ∃ store, realize rows store source = target

/-- Every source step takes a positive number of concrete TM2 steps, including final halt. -/
theorem respects (rows : Array CodeDAG.Node) (topology : CodeVM.Topological rows) :
    StateTransition.Respects (CodeVM.step rows) (TM2.step Runtime.machine) (Related rows) := by
  intro source target related
  rcases related with ⟨wf, store, rfl⟩
  cases source with
  | halt values => rfl
  | ret frame values =>
    have move := step_return rows frame values
    rw [move]
    obtain ⟨resultStore, run⟩ := return_refines rows store frame values
    exact ⟨realize rows resultStore (afterReturn frame values),
      ⟨CodeVM.step_wf rows topology _ _ wf move, resultStore, rfl⟩, run⟩
  | eval pc frame values =>
    have bound : pc < rows.size := wf.1
    let node := rows[pc]'bound
    have row : rows[pc]? = some node := by simp [node, bound]
    have move := step_eval rows pc node row frame values
    rw [move]
    obtain ⟨resultStore, run⟩ := eval_refines rows pc node row store frame values
    exact ⟨realize rows resultStore (afterEval node frame values),
      ⟨CodeVM.step_wf rows topology _ _ wf move, resultStore, rfl⟩, run⟩

/-- Positive simulation establishes both halting directions, not just successful execution. -/
theorem realize_halts (rows : Array CodeDAG.Node) (topology : CodeVM.Topological rows)
    (source : CodeVM.Config) (wf : source.WF rows.size) (store : Option Γ') :
    (StateTransition.eval (TM2.step Runtime.machine) (realize rows store source)).Dom ↔
      (StateTransition.eval (CodeVM.step rows) source).Dom :=
  StateTransition.tr_eval_dom (respects rows topology) ⟨wf, store, rfl⟩

/-- The ordinary four-stack machine, including its real startup, executes the shared program. -/
theorem tm2_halts (dag : CodeDAG.DAG) (valid : dag.Valid) (values : List Nat) :
    letI : Inhabited Λ' := ⟨Runtime.label .start⟩
    (TM2.eval Runtime.machine main (RuntimeWire.input dag values)).Dom ↔
      (dag.decode.eval values).Dom := by
  let : Inhabited Λ' := ⟨Runtime.label .start⟩
  change (StateTransition.eval (TM2.step Runtime.machine)
    (TM2.init main (RuntimeWire.input dag values))).Dom ↔ _
  rw [StateTransition.reaches_eval (RuntimeWire.tm2_init_reaches dag values).to_reflTransGen]
  exact (realize_halts dag.rows valid.2 (CodeVM.init dag values)
    (CodeVM.init_wf dag valid values) none).trans (CodeVM.halts_iff dag valid values)

/-- Compiling any source Code to a shared table preserves termination in both directions. -/
theorem tm2_halts_compiled (code : Turing.ToPartrec.Code) (values : List Nat) :
    letI : Inhabited Λ' := ⟨Runtime.label .start⟩
    (TM2.eval Runtime.machine main (RuntimeWire.input (CodeDAG.compile code) values)).Dom ↔
      (code.eval values).Dom := by
  simpa only [CodeDAG.compile_correct] using
    tm2_halts (CodeDAG.compile code) (CodeDAG.compile_valid code) values

end ConjectureMachines.Compilation.RuntimeProof
