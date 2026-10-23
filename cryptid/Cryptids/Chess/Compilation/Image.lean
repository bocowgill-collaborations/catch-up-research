/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Compilation.Templates
public import Cryptids.Chess.Compilation.Input
public import Cryptids.Compilation.TemplateGraph
public import Cryptids.Compilation.Binary
public import Cryptids.Compilation.FlatInit

/-! # The fixed, fully paid blank-tape chess machine -/

@[expose] public section
namespace Chess.Compilation.Image
open Turing PartrecToTM2 K'
open ConjectureMachines ConjectureMachines.Compilation

set_option backward.isDefEq.respectTransparency false

-- Proof elaboration uses Input.bits_size; it must not unfold the serialized million-bit array.
attribute [local irreducible] Input.bits

/-- Numeric constructor partition; neither lookup consults a semantic certificate. -/
def classify (pc : Templates.SourceLabel) : TemplateGraph.Class 1734 1188 :=
  match Templates.readIndex pc with
  | some reader => .read reader
  | none => match Templates.moveIndex pc with
    | some mover => .move mover
    | none => .plain

/-- Only literal primitive rows, codec and finite site/index data enter graph construction. -/
def data : TemplateGraph.Data Templates.Symbol Templates.Store 4042 270 1250 5 1734 1188 11 where
  rows := Templates.primitiveMachine
  encode := CodeBackend.blockCode.encode
  decode := CodeBackend.blockCode.decode
  siteFor := Templates.writeIndex
  next := Templates.writeNext
  alphabet := Templates.alphabet
  stores := Templates.stores
  readPC := Templates.readPC
  movePC := Templates.movePC
  classify := classify

/-- Shape classification is a separate erased proof; it is never an input to construction. -/
theorem classified (pc : Templates.SourceLabel) :
    match classify pc with
    | .plain => TemplateGraph.PlainRow (Templates.primitiveMachine pc)
    | .read i => Templates.readPC i = pc ∧
      TemplateGraph.ReadRow (Templates.primitiveMachine pc)
    | .move i => Templates.movePC i = pc ∧
      TemplateGraph.MoveRow (Templates.primitiveMachine pc) := by
  unfold classify
  cases read : Templates.readIndex pc with
  | some i =>
    refine ⟨Templates.read_inverse pc i read, ?_⟩
    have member := Templates.read_member pc i read
    cases row : Templates.primitiveMachine pc <;>
      simp_all [TemplateGraph.ReadRow, Templates.IsRead]
  | none =>
    cases move : Templates.moveIndex pc with
    | some i =>
      refine ⟨Templates.move_inverse pc i move, ?_⟩
      have member := Templates.move_member pc i move
      cases row : Templates.primitiveMachine pc <;>
        simp_all [TemplateGraph.MoveRow, Templates.IsMove]
    | none =>
      have noRead : ¬Templates.IsRead (Templates.primitiveMachine pc) := by
        intro h
        obtain ⟨i, found⟩ := Templates.read_covers pc h
        rw [read] at found
        cases found
      have noMove : ¬Templates.IsMove (Templates.primitiveMachine pc) := by
        intro h
        obtain ⟨i, found⟩ := Templates.move_covers pc h
        rw [move] at found
        cases found
      cases row : Templates.primitiveMachine pc <;>
        simp_all [TemplateGraph.PlainRow, Templates.IsRead, Templates.IsMove]

/-- The generic template semantics apply to the independent literal data. -/
theorem valid : TemplateGraph.Valid CodeBackend.blockCode data Templates.writeSites where
  encode_eq := rfl
  decode_eq := rfl
  siteFor_eq := rfl
  next_eq := rfl
  primitive := Templates.onePrimitive
  classified pc := by
    cases row : classify pc <;> simpa only [data, row] using classified pc

/-- Construct the nominal getter layers once, then retain their direct node and entry closures. -/
def getter := TemplateGraph.lazyGraph data

/-- Exact paid node count; no graph or source control is enumerated by this proof. -/
theorem node_count : (TemplateGraph.build data).raw.count = 38893646 :=
  (TemplateGraph.build_count data).trans TemplateGraph.chess_inventory_count

/-- Direct numeric Post rows over the getter graph, retaining all halted stores. -/
def post := LazyGraph.machine getter

/-- Every numeric Post transition agrees with the complete formal graph backend. -/
theorem post_eq : post = GraphPost.machine (TemplateGraph.graph data) :=
  LazyGraph.machine_eq getter

/-- Exact source-statement correspondence for every normal and writer label. -/
theorem graph_machine_eq : BoolGraph.machine (TemplateGraph.graph data) data.stores =
    Templates.machine := by
  rw [TemplateGraph.machine_eq CodeBackend.blockCode data Templates.writeSites valid]
  exact Templates.machine_template.symm

/-- The direct numeric Post program has the original Runtime's domain on every stack input. -/
theorem post_runtime_dom (k : K') (values : List Γ') :
    letI : Inhabited Λ' := ⟨Runtime.label .start⟩
    (TM0.eval post (Templates.input k values)).Dom ↔
      (TM2.eval Runtime.machine k values).Dom := by
  have template := TemplateGraph.halts_iff CodeBackend.blockCode data Templates.writeSites valid
    Templates.stores_zero (Templates.input k values)
  change (TM0.eval post (Templates.input k values)).Dom ↔
    (TM1.eval (BinaryTemplates.machine CodeBackend.blockCode Templates.primitiveMachine
      Templates.writeSites Templates.alphabet) (Templates.input k values)).Dom at template
  rw [← Templates.machine_template] at template
  exact template.trans (Templates.runtime_eval_dom k values)

/-- The complete paid bit stream is exactly the template Runtime input. -/
theorem input_eq : Input.binary = Templates.input main Tape.input := rfl

/-- Unconditional non-draw domain for the actual full program and initial-game input. -/
theorem post_halts_input :
    (TM0.eval post Input.binary).Dom ↔ ¬(WhiteCanAvoidLoss ∧ BlackCanAvoidLoss) := by
  rw [input_eq]
  exact (post_runtime_dom main Tape.input).trans Tape.halts_iff

/-- Every optional node/store descriptor plus distinguished state zero remains paid. -/
theorem post_count : GraphPost.stateCount (TemplateGraph.build data).raw.count 5 =
    194468236 := by rw [node_count]; rfl

/-- One main and one return state per Post control, using the generic binary backend. -/
abbrev body : BundledMachine 2 :=
  ⟨GraphPost.stateCount (TemplateGraph.build data).raw.count 5 +
    GraphPost.stateCount (TemplateGraph.build data).raw.count 5, Compilation.Binary.compile post⟩

/-- The binary body has no omitted return or halted controls. -/
theorem body_states : body.states = 388936472 := by change _ + _ = _; rw [post_count]

/-- The real serialized program and initial game are written from blank tape. -/
abbrev generated : BundledMachine 2 := FlatInit.initialise Input.bits body

/-- Keep concrete initializer-state synthesis symbolic rather than computing array size. -/
instance generated_neZero : NeZero generated.states := generated.neZeroStates

/-- All input bits are paid for with exactly one write and one restoring move each. -/
theorem prefix_states : 2 * Input.bits.size = 3110360 := Input.paid_prefix

/-- The final paid machine count is an ordinary kernel-checked natural equality. -/
theorem generated_states : generated.states = 392046832 := by
  have count := Input.initialise_states body
  rw [body_states] at count
  exact count

/-- Explicit finite-index transport; record projection never reduces a count equality. -/
def castMachine {a b : Nat} (equal : a = b) (M : Machine a 2) : Machine b 2 where
  transition state bit :=
    (M.transition (Fin.cast equal.symm state) bit).map (fun (write, dir, next) ↦
      (write, dir, Fin.cast equal next))

@[simp] theorem castMachine_refl {a : Nat} (M : Machine a 2) :
    castMachine (rfl : a = a) M = M := by
  cases M
  simp [castMachine, Fin.cast]

/-- The fixed numerical binary machine. The equality transport erases during execution. -/
def machine : Machine 392046832 2 :=
  castMachine generated_states generated.toMachine

/-- The body halts on the complete binary input exactly when frozen chess is non-draw. -/
theorem body_halts_input : Init.HaltsOn body.toMachine (Turing.Tape.mk₁ Input.bits.toList) ↔
    ¬(WhiteCanAvoidLoss ∧ BlackCanAvoidLoss) := by
  rw [Input.bits_toList]
  exact (Compilation.Binary.compile_halts_input post Input.binary).trans post_halts_input

/-- Blank state zero halts precisely when the frozen draw proposition is false. -/
theorem generated_halts : generated.Halts ↔ ¬(WhiteCanAvoidLoss ∧ BlackCanAvoidLoss) :=
  (FlatInit.initialise_halts Input.bits body).trans body_halts_input

/-- State-count transport preserves numerical states and every tape cell. -/
def castCfg {a b : Nat} (equal : a = b) (cfg : Cfg a 2) : Cfg b 2 :=
  ⟨Fin.cast equal cfg.state, cfg.tape⟩

@[simp] theorem castCfg_refl {a : Nat} : castCfg (rfl : a = a) = id := by
  funext cfg
  cases cfg
  rfl

theorem castCfg_state {a b : Nat} (equal : a = b) (cfg : Cfg a 2) :
    (castCfg equal cfg).state.val = cfg.state.val := rfl

/-- Equality transport preserves every row, including missing transitions. -/
theorem cast_transition {a b : Nat} (equal : a = b) (M : Machine a 2)
    (state : Fin a) (bit : Fin 2) :
    (castMachine equal M).transition
        (Fin.cast equal state) bit =
      (M.transition state bit).map (fun (write, dir, next) ↦
        (write, dir, Fin.cast equal next)) := by
  cases equal
  simp [castMachine, Fin.cast]

/-- Equality transport preserves complete successor configurations and stopping. -/
theorem cast_step {a b : Nat} [NeZero a] [NeZero b] (equal : a = b)
    (M : Machine a 2) (cfg : Cfg a 2) :
    step (castMachine equal M) (castCfg equal cfg) =
      (step M cfg).map (castCfg equal) := by cases equal; simp

@[simp] theorem cast_init {a b : Nat} [NeZero a] [NeZero b] (equal : a = b) :
    castCfg equal (ConjectureMachines.init : Cfg a 2) = ConjectureMachines.init := by
  cases equal
  rfl

/-- Exact finite executions commute with the state-count transport. -/
theorem cast_run {a b : Nat} [NeZero a] [NeZero b] (equal : a = b)
    (M : Machine a 2) (count : Nat) (cfg : Cfg a 2) :
    FlatInit.runFrom (castMachine equal M)
        count (castCfg equal cfg) =
      (FlatInit.runFrom M count cfg).map (castCfg equal) := by cases equal; simp

/-- Both blank halting directions survive the fixed numerical state-count transport. -/
theorem cast_halts {a b : Nat} [NeZero a] [NeZero b] (equal : a = b) (M : Machine a 2) :
    Halts (castMachine equal M) ↔ Halts M := by
  cases equal
  simp

/-- Actual state-zero blank halting iff the frozen strategic draw proposition is false. -/
theorem halts_iff : Halts machine ↔ ¬(WhiteCanAvoidLoss ∧ BlackCanAvoidLoss) :=
  (cast_halts generated_states generated.toMachine).trans generated_halts

/-- Generic initialization transport keeps the input array abstract during elaboration. -/
theorem initialise_cast_run {b : Nat} [NeZero b] (bits : Array (Fin 2))
    (B : BundledMachine 2) (equal : (FlatInit.initialise bits B).states = b) :
    FlatInit.runFrom (castMachine equal
        (FlatInit.initialise bits B).toMachine) (2 * bits.size) ConjectureMachines.init =
      some (castCfg equal (FlatInit.embed bits B ⟨0, Turing.Tape.mk₁ bits.toList⟩)) := by
  rw [← cast_init equal, cast_run, FlatInit.initialise_run]
  rfl

/-- Generic body-step transport, including missing transitions. -/
theorem initialise_cast_step {b : Nat} [NeZero b] (bits : Array (Fin 2))
    (B : BundledMachine 2) (equal : (FlatInit.initialise bits B).states = b)
    (cfg : Cfg B.states 2) :
    step (castMachine equal
        (FlatInit.initialise bits B).toMachine) (castCfg equal (FlatInit.embed bits B cfg)) =
      (step B.toMachine cfg).map (fun next ↦ castCfg equal (FlatInit.embed bits B next)) := by
  rw [cast_step]
  change (step (FlatInit.machine bits B) (FlatInit.embed bits B cfg)).map _ = _
  rw [FlatInit.step_embed, Option.map_map]
  rfl

/-- Generic body-row transport at the actual numeric initializer offset. -/
theorem initialise_cast_row {b : Nat} (bits : Array (Fin 2)) (B : BundledMachine 2)
    (equal : (FlatInit.initialise bits B).states = b) (state : Fin B.states) (bit : Fin 2) :
    (castMachine equal
        (FlatInit.initialise bits B).toMachine).transition
        (Fin.cast equal (FlatInit.bodyState bits B state)) bit =
      (B.toMachine.transition state bit).map (fun (write, dir, next) ↦
        (write, dir, Fin.cast equal (FlatInit.bodyState bits B next))) := by
  rw [cast_transition]
  change ((FlatInit.machine bits B).transition _ bit).map _ = _
  rw [FlatInit.transition_body, Option.map_map]
  rfl

/-- Generic bounds avoid reducing the concrete million-bit array during elaboration. -/
theorem prefix_bounds {n i : Nat} (bound : i < n) :
    i ≤ 2 * n ∧ i + 1 ≤ 2 * n ∧ n + i ≤ 2 * n ∧ n + i + 1 ≤ 2 * n := by omega

/-- Generic write-row transport. -/
theorem initialise_cast_write {b : Nat} (bits : Array (Fin 2)) (B : BundledMachine 2)
    (equal : (FlatInit.initialise bits B).states = b) (i : Nat) (bound : i < bits.size)
    (bit : Fin 2) :
    (castMachine equal
        (FlatInit.initialise bits B).toMachine).transition
        (Fin.cast equal (FlatInit.prefixState bits B i (prefix_bounds bound).1)) bit =
      some (bits[i], .right,
        Fin.cast equal (FlatInit.prefixState bits B (i + 1) (prefix_bounds bound).2.1)) := by
  rw [cast_transition]
  change ((FlatInit.machine bits B).transition _ bit).map _ = _
  rw [FlatInit.transition_write bits B i bound bit]
  rfl

/-- Generic restoring-row transport. -/
theorem initialise_cast_return {b : Nat} (bits : Array (Fin 2)) (B : BundledMachine 2)
    (equal : (FlatInit.initialise bits B).states = b) (i : Nat) (bound : i < bits.size)
    (bit : Fin 2) :
    (castMachine equal
        (FlatInit.initialise bits B).toMachine).transition
        (Fin.cast equal (FlatInit.prefixState bits B (bits.size + i)
          (prefix_bounds bound).2.2.1)) bit =
      some (bit, .left, Fin.cast equal (FlatInit.prefixState bits B (bits.size + i + 1)
        (prefix_bounds bound).2.2.2)) := by
  rw [cast_transition]
  change ((FlatInit.machine bits B).transition _ bit).map _ = _
  rw [FlatInit.transition_return bits B i bound bit]
  rfl

/-- Exact numeric entry offset, proved while the serialized input remains abstract. -/
theorem cast_entry_state {b : Nat} (bits : Array (Fin 2)) (B : BundledMachine 2)
    (equal : (FlatInit.initialise bits B).states = b) :
    (castCfg equal (FlatInit.embed bits B ⟨0, Turing.Tape.mk₁ bits.toList⟩)).state.val =
      2 * bits.size := by
  change 2 * bits.size + 0 = _
  omega

/-- A tape-parametric final body entry avoids constructing the paid tape in module code. -/
def bodyEntry (tape : Turing.Tape (Fin 2)) : Cfg 392046832 2 := ⟨3110360, tape⟩

/-- Generic exact configuration transport at a certified prefix offset. -/
theorem cast_entry_eq {b offset : Nat} (bits : Array (Fin 2)) (B : BundledMachine 2)
    (equal : (FlatInit.initialise bits B).states = b) (paid : 2 * bits.size = offset)
    (bound : offset < b) (tape : Turing.Tape (Fin 2)) :
    castCfg equal (FlatInit.embed bits B ⟨0, tape⟩) = (⟨⟨offset, bound⟩, tape⟩ : Cfg b 2) := by
  apply congrArg (fun state ↦ (⟨state, tape⟩ : Cfg b 2))
  apply Fin.ext
  change 2 * bits.size + 0 = offset
  omega

/-- Paid finite execution, with the numerical prefix supplied as a proved parameter. -/
theorem initialise_cast_paid_run {b offset : Nat} [NeZero b] (bits : Array (Fin 2))
    (B : BundledMachine 2) (equal : (FlatInit.initialise bits B).states = b)
    (paid : 2 * bits.size = offset) (bound : offset < b) :
    FlatInit.runFrom (castMachine equal
        (FlatInit.initialise bits B).toMachine) offset ConjectureMachines.init =
      some (⟨⟨offset, bound⟩, Turing.Tape.mk₁ bits.toList⟩ : Cfg b 2) := by
  have result := initialise_cast_run bits B equal
  rw [paid] at result
  exact result.trans (congrArg some (cast_entry_eq bits B equal paid bound _))

/-- Exactly 3,110,360 ordinary steps initialize the final fixed machine from blank tape. -/
theorem initialises :
    FlatInit.runFrom machine 3110360 ConjectureMachines.init =
      some (bodyEntry (Turing.Tape.mk₁ Input.bits.toList)) :=
  initialise_cast_paid_run Input.bits body generated_states prefix_states (by decide)

theorem bodyEntry_state (tape : Turing.Tape (Fin 2)) : (bodyEntry tape).state.val = 3110360 := rfl

theorem bodyEntry_tape (tape : Turing.Tape (Fin 2)) : (bodyEntry tape).tape = tape := rfl

/-- The initialized body is reached by a genuine positive path, not an input assumption. -/
theorem initial_reaches : StateTransition.Reaches₁ (step machine) ConjectureMachines.init
    (bodyEntry (Turing.Tape.mk₁ Input.bits.toList)) :=
  FlatInit.runFrom_reaches_positive machine 3110360 (by decide) _ _ initialises

/-- Every final fixed-state row is exactly the generated paid row under numerical transport. -/
theorem rows (state : Fin generated.states) (bit : Fin 2) :
    machine.transition (Fin.cast generated_states state) bit =
      (generated.toMachine.transition state bit).map (fun (write, dir, next) ↦
        (write, dir, Fin.cast generated_states next)) :=
  cast_transition generated_states generated.toMachine state bit

/-- Full final-machine configurations correspond exactly, including missing transitions. -/
theorem step_eq (cfg : Cfg generated.states 2) :
    step machine (castCfg generated_states cfg) =
      (step generated.toMachine cfg).map (castCfg generated_states) :=
  cast_step generated_states generated.toMachine cfg

/-- Main binary-body states dispatch exactly the corresponding direct Post instruction. -/
theorem body_main (state : Fin (GraphPost.stateCount (TemplateGraph.build data).raw.count 5))
    (bit : Fin 2) :
    body.toMachine.transition (Compilation.Binary.mainState state) bit =
      (post state (Compilation.Binary.decodeSymbol bit)).map (fun (next, action) ↦ match action with
        | .move dir => (bit, dir, Compilation.Binary.mainState next)
        | .write value => (Compilation.Binary.encodeSymbol value, .right,
            Compilation.Binary.bounceState next)) :=
  Compilation.Binary.compile_main post state bit

/-- Every body return state preserves its scanned bit and restores the head left. -/
theorem body_bounce (state : Fin (GraphPost.stateCount (TemplateGraph.build data).raw.count 5))
    (bit : Fin 2) :
    body.toMachine.transition (Compilation.Binary.bounceState state) bit =
      some (bit, .left, Compilation.Binary.mainState state) :=
  Compilation.Binary.compile_bounce post state bit

end Chess.Compilation.Image
