/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Compilation.WithoutDead
public import Cryptids.Chess.Compilation.Program
public import Cryptids.Compilation.ListCode

/-!
# Explicit workstack control for chess backward induction

A continuation machine evaluates games without a runtime fuel register. Concrete Code
procedures implement its transitions under explicit refinement contracts for four actual
callee syntax trees. Instantiating those chess callees remains a separate obligation.
-/

@[expose] public section
namespace Chess.Compilation.Control
open Adjudication Evaluation
open Turing.ToPartrec
open ConjectureMachines.Compilation

set_option backward.isDefEq.respectTransparency false
attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some

/-- Accumulate a candidate value without introducing an empty-list fallback. -/
def improve (turn : Color) (best : Option Outcome) (value : Outcome) : Option Outcome :=
  match best with
  | none => some value
  | some old => some (Evaluator.better turn old value)

/-- A suspended action fold, retaining its game, unprocessed actions, value, and player. -/
structure Frame where
  game : Adjudication.Game
  actions : List Action
  best : Option Outcome
  turn : Color

/-- Three explicit modes; the continuation stack is ordinary data. -/
inductive State where
  | evaluate : Adjudication.Game → List Frame → State
  | actions : Frame → List Frame → State
  | returned : Outcome → List Frame → State

/-- One source transition. An invalid empty fold with no candidate repeats, never draws. -/
def step : State → Outcome ⊕ State
  | .evaluate game frames =>
    match WithoutDead.automaticWithoutDead game with
    | some value => .inr (.returned value frames)
    | none => .inr (.actions
        ⟨game, WithoutDead.legalActions game, none, game.current.turn⟩ frames)
  | .actions frame frames =>
    match frame.actions with
    | [] =>
      match frame.best with
      | none => .inr (.actions frame frames)
      | some value => .inr (.returned value frames)
    | .claimDraw :: rest => .inr (.actions
        { frame with actions := rest, best := improve frame.turn frame.best .draw } frames)
    | .play ply :: rest => .inr (.evaluate (frame.game.play ply)
        ({ frame with actions := rest } :: frames))
  | .returned value [] => .inl value
  | .returned value (frame :: frames) => .inr (.actions
      { frame with best := improve frame.turn frame.best value } frames)

/-- Finite execution of the independent continuation machine. -/
inductive Runs : State → Outcome → Prop
  | stop {state value} : step state = .inl value → Runs state value
  | next {state next value} : step state = .inr next → Runs next value → Runs state value

/-- The scalar maximizing operation is associative, including ties. -/
theorem better_assoc (turn : Color) (a b c : Outcome) :
    Evaluator.better turn (Evaluator.better turn a b) c =
      Evaluator.better turn a (Evaluator.better turn b c) := by
  rcases turn with _ | _ <;> rcases a with ⟨_ | _⟩ | _ <;>
    rcases b with ⟨_ | _⟩ | _ <;> rcases c with ⟨_ | _⟩ | _ <;> decide

def foldBest (turn : Color) (best : Option Outcome) (values : List Outcome) : Option Outcome :=
  values.foldl (improve turn) best

theorem foldValues_better (turn : Color) (a b : Outcome) (rest : List Outcome) :
    Evaluator.foldValues turn (Evaluator.better turn a b) rest =
      Evaluator.better turn a (Evaluator.foldValues turn b rest) := by
  cases rest <;> simp only [Evaluator.foldValues, better_assoc]

theorem foldBest_some (turn : Color) (first : Outcome) (rest : List Outcome) :
    foldBest turn (some first) rest = some (Evaluator.foldValues turn first rest) := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
    exact (ih (Evaluator.better turn first next)).trans
      (congrArg some (foldValues_better turn first next rest))

theorem foldBest_nonempty (turn : Color) (first : Outcome) (rest : List Outcome) :
    foldBest turn none (first :: rest) = some (Evaluator.foldValues turn first rest) := by
  exact foldBest_some turn first rest

/-- The deferred evaluator gives the same terminal value as M4. -/
theorem solve_terminal (game : Adjudication.Game) (value : Outcome)
    (terminal : WithoutDead.automaticWithoutDead game = some value) : solve game = value := by
  have positive := WithoutDead.evaluate_correct (WithoutDead.rankNoDead game + 2) game (by omega)
  simp only [WithoutDead.evaluate, terminal] at positive
  exact (Option.some.inj positive).symm

/-- M4's value satisfies the deferred evaluator's live Bellman equation. -/
theorem solve_live (game : Adjudication.Game)
    (live : WithoutDead.automaticWithoutDead game = none) (first : Action) (rest : List Action)
    (actions : WithoutDead.legalActions game = first :: rest) :
    foldBest game.current.turn none
      ((first :: rest).map (actionValue game)) = some (solve game) := by
  have children (ply : Ply) :
      WithoutDead.evaluate (WithoutDead.rankNoDead game + 1) (game.play ply) =
        some (solve (game.play ply)) :=
    WithoutDead.evaluate_correct _ _
      (by have lower := WithoutDead.rankNoDead_play_lt game ply live; omega)
  have result := WithoutDead.evaluate_correct (WithoutDead.rankNoDead game + 2) game (by omega)
  have folded := WithoutDead.evaluateActions_correct _ game children first rest
  simp only [WithoutDead.evaluate, live, actions] at result
  simpa only [List.map_cons, foldBest_nonempty] using folded.symm.trans result

/-- Evaluate an arbitrary finite action list, assuming each child game can resume its caller. -/
theorem actions_runs (game : Adjudication.Game)
    (children : ∀ ply frames value,
      Runs (.returned (solve (game.play ply)) frames) value →
      Runs (.evaluate (game.play ply) frames) value)
    (actions : List Action) (best : Option Outcome) (turn : Color) (frames : List Frame)
    (value finish : Outcome)
    (folded : foldBest turn best (actions.map (actionValue game)) = some value)
    (resume : Runs (.returned value frames) finish) :
    Runs (.actions ⟨game, actions, best, turn⟩ frames) finish := by
  induction actions generalizing best with
  | nil =>
    change best = some value at folded
    subst best
    exact .next rfl resume
  | cons action rest ih =>
    cases action with
    | claimDraw =>
      exact .next rfl (ih _ folded)
    | play ply =>
      exact .next rfl (children ply _ finish (.next rfl (ih _ folded)))

/-- Each complete game evaluation can resume any suspended caller; ranks are proof-only. -/
theorem evaluate_runs (game : Adjudication.Game) (frames : List Frame) (finish : Outcome)
    (resume : Runs (.returned (solve game) frames) finish) :
    Runs (.evaluate game frames) finish := by
  induction rankEq : WithoutDead.rankNoDead game using Nat.strong_induction_on
      generalizing game frames finish with
  | h rank ih =>
    cases terminal : WithoutDead.automaticWithoutDead game with
    | some value =>
      exact .next (next := .returned value frames) (by simp [step, terminal])
        (by simpa only [solve_terminal game value terminal] using resume)
    | none =>
      have children (ply : Ply) (stack : List Frame) (value : Outcome)
          (continuation : Runs (.returned (solve (game.play ply)) stack) value) :
          Runs (.evaluate (game.play ply) stack) value :=
        ih _ (by have lower := WithoutDead.rankNoDead_play_lt game ply terminal; omega)
          _ stack value continuation rfl
      obtain ⟨first, rest, actions⟩ := List.exists_cons_of_ne_nil
        (WithoutDead.actions_nonempty game terminal)
      refine .next (next := .actions
        ⟨game, WithoutDead.legalActions game, none, game.current.turn⟩ frames)
        (by simp [step, terminal]) ?_
      exact actions_runs game children _ none _ frames (solve game) finish
        (by rw [actions]; exact solve_live game terminal first rest actions) resume

/-- The workstack machine terminates with the unchanged M4 result on every raw game. -/
theorem initial_runs (game : Adjudication.Game) :
    Runs (.evaluate game []) (solve game) :=
  evaluate_runs game [] (solve game) (.stop rfl)

/-- Scalar game data preserves the complete, exact game codec. -/
def gameWord (game : Adjudication.Game) : Nat := ListCode.stack (Data.encodeGame game)

/-- File-major square order, matching the frozen candidate enumeration. -/
def squareWord (square : Square) : Nat := 8 * square.file.val + square.rank.val

def promotionWord : Option PieceKind → Nat
  | none => 0
  | some kind => 1 + Data.encodeKind kind

/-- Positive candidate-order ply codes reserve zero for the distinct draw claim. -/
def plyWord (ply : Ply) : Nat :=
  1 + 7 * (64 * squareWord ply.src + squareWord ply.dst) + promotionWord ply.promotion

theorem plyWord_pos (ply : Ply) : 0 < plyWord ply := by unfold plyWord; omega

def actionWord : Action → Nat
  | .claimDraw => 0
  | .play ply => plyWord ply

def actionsWord (actions : List Action) : Nat := ListCode.stack (actions.map actionWord)

def bestWord : Option Outcome → Nat
  | none => 0
  | some value => Program.encodeOutcome value + 1

def frameWords (frame : Frame) : List Nat :=
  [gameWord frame.game, actionsWord frame.actions, bestWord frame.best,
    Data.encodeColor frame.turn]

def frameWord (frame : Frame) : Nat := ListCode.stack (frameWords frame)

def framesWord (frames : List Frame) : Nat := ListCode.stack (frames.map frameWord)

/-- Seven registers: mode, game, actions, best, turn, returned value, and frame stack. -/
def encodeState : State → List Nat
  | .evaluate game frames => [0, gameWord game, 0, 0, 0, 0, framesWord frames]
  | .actions frame frames =>
    [1, gameWord frame.game, actionsWord frame.actions, bestWord frame.best,
      Data.encodeColor frame.turn, 0, framesWord frames]
  | .returned value frames => [2, 0, 0, 0, 0, Program.encodeOutcome value, framesWord frames]

def encodeStep : Outcome ⊕ State → List Nat
  | .inl value => [0, Program.encodeOutcome value]
  | .inr state => 1 :: encodeState state

/-- These fields contain actual finite syntax trees, not abstract function oracles. -/
structure Procedures where
  automatic : Code
  actions : Code
  play : Code
  turn : Code

/-- Exact callee contracts. A whole-chess compiler must instantiate all four proofs. -/
structure Correct (procedures : Procedures) : Prop where
  automatic (game : Adjudication.Game) :
    procedures.automatic.eval [gameWord game] =
      pure [bestWord (WithoutDead.automaticWithoutDead game)]
  actions (game : Adjudication.Game) :
    procedures.actions.eval [gameWord game] = pure [actionsWord (WithoutDead.legalActions game)]
  play (game : Adjudication.Game) (ply : Ply) :
    procedures.play.eval [gameWord game, plyWord ply] = pure [gameWord (game.play ply)]
  turn (game : Adjudication.Game) :
    procedures.turn.eval [gameWord game] = pure [Data.encodeColor game.current.turn]

/-- Build a scalar stack out of actual component procedures. -/
def stackCode : List Code → Code
  | [] => .zero
  | first :: rest => .comp ListCode.packCode (NatCode.tuple [first, stackCode rest])

theorem stackCode_eval (codes : List Code) (words : List Nat) (input : List Nat)
    (correct : List.Forall₂ (fun code word ↦ code.eval input = pure [word]) codes words) :
    (stackCode codes).eval input = pure [ListCode.stack words] := by
  induction correct with
  | nil => simp [stackCode, ListCode.stack]
  | cons first rest ih => simp [stackCode, NatCode.tuple, first, ih, ListCode.stack, Bind.bind]

/-- Unpack a fixed tuple, preserving the zero residual stack and all trailing words. -/
def unstackCode : Nat → Code
  | 0 => .id
  | n + 1 => .comp (.cons .head (.comp (unstackCode n) .tail)) ListCode.unpack

theorem unstackCode_eval (words suffix : List Nat) :
    (unstackCode words.length).eval (ListCode.stack words :: suffix) =
      pure (words ++ 0 :: suffix) := by
  induction words with
  | nil => simp [unstackCode, ListCode.stack]
  | cons word words ih => simp [unstackCode, ListCode.stack, ih, Bind.bind]

@[simp] theorem unstackCode_four (a b c d : Nat) (suffix : List Nat) :
    (unstackCode 4).eval (ListCode.stack [a, b, c, d] :: suffix) =
      pure (a :: b :: c :: d :: 0 :: suffix) :=
  unstackCode_eval [a, b, c, d] suffix

/-- Scalar outcome utility on valid color/outcome codes. -/
def utilityCode : Code :=
  NatCode.ifZero (NatCode.nth 1) (NatCode.literal 1)
    (NatCode.ifZero (.comp NatCode.eq
      (NatCode.tuple [NatCode.nth 1, .comp .succ (NatCode.nth 0)]))
      .zero (NatCode.literal 2))

/-- Update the optional best value: inputs are turn, optional best, and new value. -/
def improveCode : Code :=
  let new := .comp .succ (NatCode.nth 2)
  let oldUtility := .comp utilityCode (NatCode.tuple
    [NatCode.nth 0, .comp .pred (NatCode.nth 1)])
  let newUtility := .comp utilityCode (NatCode.tuple [NatCode.nth 0, NatCode.nth 2])
  NatCode.ifZero (NatCode.nth 1) new
    (NatCode.ifZero (.comp NatCode.le (NatCode.tuple [newUtility, oldUtility]))
      new (NatCode.nth 1))

theorem utilityCode_eval (color outcome : Nat) :
    utilityCode.eval [color, outcome] =
      pure [if outcome = 0 then 1 else if outcome = color + 1 then 2 else 0] := by
  rw [utilityCode, NatCode.ifZero_eval _ _ _ _ [outcome] (by simp)]
  by_cases zero : outcome = 0
  · simp [zero]
  · simp only [List.headI_cons, zero, ↓reduceIte]
    rw [NatCode.ifZero_eval _ _ _ _ [if outcome = color + 1 then 1 else 0]
      (by simp [NatCode.tuple, Bind.bind])]
    by_cases equal : outcome = color + 1 <;> simp [equal]

theorem utilityCode_outcome (color : Color) (outcome : Outcome) :
    utilityCode.eval [Data.encodeColor color, Program.encodeOutcome outcome] =
      pure [utility color outcome] := by
  rcases color with _ | _ <;> rcases outcome with ⟨_ | _⟩ | _ <;>
    simp [utilityCode_eval, Data.encodeColor, Program.encodeOutcome, utility]

theorem improveCode_eval (turn : Color) (best : Option Outcome) (value : Outcome) :
    improveCode.eval [Data.encodeColor turn, bestWord best, Program.encodeOutcome value] =
      pure [bestWord (improve turn best value)] := by
  cases best with
  | none =>
    rw [improveCode, NatCode.ifZero_eval _ _ _ _ [0] (by simp [bestWord])]
    simp [bestWord, improve, Bind.bind]
  | some old =>
    rw [improveCode, NatCode.ifZero_eval _ _ _ _ [Program.encodeOutcome old + 1]
      (by simp [bestWord])]
    simp only [List.headI_cons, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    rw [NatCode.ifZero_eval _ _ _ _ [if utility turn value ≤ utility turn old then 1 else 0]
      (by simp [NatCode.tuple, bestWord, utilityCode_outcome, Bind.bind])]
    by_cases better : utility turn value ≤ utility turn old <;>
      simp [better, bestWord, improve, Evaluator.better, Bind.bind]

theorem improveCode_draw (turn : Color) (best : Option Outcome) :
    improveCode.eval [Data.encodeColor turn, bestWord best, 0] =
      pure [bestWord (improve turn best .draw)] := improveCode_eval turn best .draw

/-- Evaluation-mode body, with an automatic-result word temporarily prefixed. -/
def evalMode (procedures : Procedures) : Code :=
  let live := NatCode.tuple [NatCode.literal 1, NatCode.literal 1, NatCode.nth 2,
    .comp procedures.actions (NatCode.tuple [NatCode.nth 2]), .zero,
    .comp procedures.turn (NatCode.tuple [NatCode.nth 2]), .zero, NatCode.nth 7]
  let terminal := NatCode.tuple [NatCode.literal 1, NatCode.literal 2, .zero, .zero,
    .zero, .zero, .pred, NatCode.nth 7]
  .comp (NatCode.ifZero .head live terminal)
    (.cons (.comp procedures.automatic (NatCode.tuple [NatCode.nth 1])) .id)

/-- Process a claim after unpacking the head action and residual action stack. -/
def claimMode : Code := NatCode.tuple
  [NatCode.literal 1, NatCode.literal 1, NatCode.nth 3, NatCode.nth 1,
    .comp improveCode (NatCode.tuple [NatCode.nth 6, NatCode.nth 5, .zero]),
    NatCode.nth 6, .zero, NatCode.nth 8]

/-- Suspend this fold in a packed frame and start the actual child-game procedure. -/
def playMode (procedures : Procedures) : Code :=
  let frame := stackCode [NatCode.nth 3, NatCode.nth 1, NatCode.nth 5, NatCode.nth 6]
  let frames := .comp ListCode.packCode (NatCode.tuple [frame, NatCode.nth 8])
  NatCode.tuple [NatCode.literal 1, .zero,
    .comp procedures.play (NatCode.tuple [NatCode.nth 3, NatCode.nth 0]),
    .zero, .zero, .zero, .zero, frames]

/-- Action-mode body. The impossible empty/no-best fold repeats without fabricating a value. -/
def actionsMode (procedures : Procedures) : Code :=
  let empty := NatCode.ifZero (NatCode.nth 3) (.cons (NatCode.literal 1) .id)
    (NatCode.tuple [NatCode.literal 1, NatCode.literal 2, .zero, .zero, .zero, .zero,
      .comp .pred (NatCode.nth 3), NatCode.nth 6])
  let nonempty := .comp (NatCode.ifZero .head claimMode (playMode procedures))
    (.comp ListCode.unpack (.cons (NatCode.nth 2) .id))
  NatCode.ifZero (NatCode.nth 2) empty nonempty

/-- Resume a caller after unpacking its four-word frame. -/
def resumeMode : Code := NatCode.tuple
  [NatCode.literal 1, NatCode.literal 1, NatCode.nth 0, NatCode.nth 1,
    .comp improveCode (NatCode.tuple [NatCode.nth 3, NatCode.nth 2, NatCode.nth 11]),
    NatCode.nth 3, .zero, NatCode.nth 5]

/-- Return to a caller, or emit a zero stop tag followed by the final outcome word. -/
def returnMode : Code :=
  NatCode.ifZero (NatCode.nth 6) (NatCode.tuple [.zero, NatCode.nth 5])
    (.comp resumeMode (.comp (unstackCode 4)
      (.comp ListCode.unpack (.cons (NatCode.nth 6) .id))))

/-- The finite concrete control transition program. -/
def stepCode (procedures : Procedures) : Code :=
  NatCode.ifZero (NatCode.nth 0) (evalMode procedures)
    (NatCode.ifZero (.comp .pred (NatCode.nth 0)) (actionsMode procedures) returnMode)

theorem evalMode_eval (procedures : Procedures) (correct : Correct procedures)
    (game : Adjudication.Game) (frames : List Frame) :
    (evalMode procedures).eval (encodeState (.evaluate game frames)) =
      pure (encodeStep (step (.evaluate game frames))) := by
  simp only [evalMode, Code.comp_eval]
  simp only [encodeState, NatCode.tuple, Code.cons_eval, Code.comp_eval, Code.id_eval,
    Code.nil_eval, NatCode.nth_eval, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.headI_cons, Bind.bind, Part.pure_eq_some, Part.bind_some,
    correct.automatic]
  rw [NatCode.ifZero_eval _ _ _ _ [bestWord (WithoutDead.automaticWithoutDead game)]
    (by simp)]
  cases terminal : WithoutDead.automaticWithoutDead game <;>
    simp [terminal, bestWord, step, encodeStep, encodeState,
      correct.actions, correct.turn, Bind.bind]

theorem actionsMode_eval (procedures : Procedures) (correct : Correct procedures)
    (frame : Frame) (frames : List Frame) :
    (actionsMode procedures).eval (encodeState (.actions frame frames)) =
      pure (encodeStep (step (.actions frame frames))) := by
  rcases frame with ⟨game, actions, best, turn⟩
  rw [actionsMode, NatCode.ifZero_eval _ _ _ _ [actionsWord actions] (by simp [encodeState])]
  cases actions with
  | nil =>
    simp only [actionsWord, List.map_nil, ListCode.stack, List.headI_cons, ↓reduceIte]
    rw [NatCode.ifZero_eval _ _ _ _ [bestWord best] (by simp [encodeState])]
    cases best <;> simp [encodeState, bestWord, step, encodeStep, NatCode.tuple, Bind.bind]
  | cons action rest =>
    have positive : actionsWord (action :: rest) ≠ 0 := Nat.ne_of_gt (ListCode.pack_pos _ _)
    simp only [List.headI_cons, positive, ↓reduceIte, Code.comp_eval]
    simp only [encodeState, actionsWord, List.map_cons, ListCode.stack, Code.cons_eval,
      Code.id_eval, NatCode.nth_eval, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, List.headI_cons, Bind.bind, Part.pure_eq_some, Part.bind_some,
      ListCode.unpack_eval]
    rw [NatCode.ifZero_eval _ _ _ _ [actionWord action] (by simp)]
    cases action with
    | claimDraw =>
      simp [actionWord, claimMode, NatCode.tuple, improveCode_draw, step, encodeStep,
        encodeState, actionsWord, Bind.bind]
    | play ply =>
      simp [actionWord, Nat.ne_of_gt (plyWord_pos ply), playMode, stackCode, NatCode.tuple,
        correct.play, step, encodeStep, encodeState, actionsWord, framesWord, frameWord,
        frameWords, ListCode.stack, Bind.bind]

theorem returnMode_eval (value : Outcome) (frames : List Frame) :
    returnMode.eval (encodeState (.returned value frames)) =
      pure (encodeStep (step (.returned value frames))) := by
  rw [returnMode, NatCode.ifZero_eval _ _ _ _ [framesWord frames] (by simp [encodeState])]
  cases frames with
  | nil =>
    simp [framesWord, ListCode.stack, encodeState, NatCode.tuple, step, encodeStep, Bind.bind]
  | cons frame frames =>
    have positive : framesWord (frame :: frames) ≠ 0 := Nat.ne_of_gt (ListCode.pack_pos _ _)
    simp only [List.headI_cons, positive, ↓reduceIte, Code.comp_eval]
    simp [encodeState, framesWord, ListCode.stack, Bind.bind]
    simp [frameWord, frameWords, unstackCode_four, resumeMode, NatCode.tuple,
      improveCode_eval, step, encodeStep, encodeState, framesWord, Bind.bind]

/-- Exact one-step refinement, for every encoded source state. -/
theorem stepCode_eval (procedures : Procedures) (correct : Correct procedures) (state : State) :
    (stepCode procedures).eval (encodeState state) = pure (encodeStep (step state)) := by
  cases state with
  | evaluate game frames =>
    rw [stepCode, NatCode.ifZero_eval _ _ _ _ [0] (by simp [encodeState])]
    simpa using evalMode_eval procedures correct game frames
  | actions frame frames =>
    rw [stepCode, NatCode.ifZero_eval _ _ _ _ [1] (by simp [encodeState])]
    simp only [List.headI_cons, one_ne_zero, ↓reduceIte]
    rw [NatCode.ifZero_eval _ _ _ _ [0] (by simp [encodeState, Bind.bind])]
    simpa using actionsMode_eval procedures correct frame frames
  | returned value frames =>
    rw [stepCode, NatCode.ifZero_eval _ _ _ _ [2] (by simp [encodeState])]
    simp only [List.headI_cons, Nat.reduceEqDiff, ↓reduceIte]
    rw [NatCode.ifZero_eval _ _ _ _ [1] (by simp [encodeState, Bind.bind])]
    simpa using returnMode_eval value frames

/-- Actual partial-recursive iteration; no runtime fuel is supplied. -/
def loopCode (procedures : Procedures) : Code := .fix (stepCode procedures)

/-- Every finite independent execution has exactly the same concrete fixpoint result. -/
theorem Runs.eval_eq (procedures : Procedures) (correct : Correct procedures)
    {state : State} {value : Outcome} (execution : Runs state value) :
    (loopCode procedures).eval (encodeState state) = pure [Program.encodeOutcome value] := by
  induction execution with
  | @stop state value edge =>
    exact ListCode.fix_stop (stepCode procedures) (encodeState state) _
      (by simpa only [edge, encodeStep] using stepCode_eval procedures correct state)
  | @next state next value edge rest ih =>
    rw [loopCode, ListCode.fix_next (stepCode procedures) (encodeState state) (encodeState next)
      (by simpa only [edge, encodeStep] using stepCode_eval procedures correct state)]
    exact ih

/-- Interpret the Code continuation tag, retaining exact finite list boundaries. -/
def interpretTag (words : List Nat) : List Nat ⊕ List Nat :=
  if words.headI = 0 then .inl words.tail else .inr words.tail

theorem stepCode_tag (procedures : Procedures) (correct : Correct procedures) (state : State) :
    ((stepCode procedures).eval (encodeState state)).map interpretTag =
      pure (match step state with
        | .inl value => .inl [Program.encodeOutcome value]
        | .inr next => .inr (encodeState next)) := by
  rw [stepCode_eval procedures correct]
  cases step state <;> simp [encodeStep, interpretTag]

/-- Every terminating concrete loop execution reconstructs a finite source execution. -/
theorem loop_complete (procedures : Procedures) (correct : Correct procedures)
    (state : State) (output : List Nat)
    (execution : output ∈ (loopCode procedures).eval (encodeState state)) :
    ∃ value, output = [Program.encodeOutcome value] ∧ Runs state value := by
  change output ∈ PFun.fix
    (fun words ↦ ((stepCode procedures).eval words).map interpretTag) (encodeState state)
    at execution
  refine PFun.fixInduction
    (C := fun words ↦ ∀ source, words = encodeState source →
      ∃ value, output = [Program.encodeOutcome value] ∧ Runs source value)
    execution ?_ state rfl
  intro words present ih source equal
  subst words
  cases edge : step source with
  | inl value =>
    have stop : Sum.inl [Program.encodeOutcome value] ∈
        ((stepCode procedures).eval (encodeState source)).map interpretTag := by
      simp [stepCode_tag procedures correct, edge]
    exact ⟨value, Part.mem_unique present (PFun.fix_stop stop), .stop edge⟩
  | inr next =>
    have forward : Sum.inr (encodeState next) ∈
        ((stepCode procedures).eval (encodeState source)).map interpretTag := by
      simp [stepCode_tag procedures correct, edge]
    obtain ⟨value, returned, rest⟩ := ih (encodeState next) forward next rfl
    exact ⟨value, returned, .next edge rest⟩

theorem encodeOutcome_injective : Function.Injective Program.encodeOutcome := by
  intro first second equal
  rcases first with ⟨_ | _⟩ | _ <;> rcases second with ⟨_ | _⟩ | _ <;>
    simp_all [Program.encodeOutcome]

/-- Exact finite-execution equivalence, in both directions, for every encoded state. -/
theorem runs_iff_eval (procedures : Procedures) (correct : Correct procedures)
    (state : State) (value : Outcome) :
    Runs state value ↔ [Program.encodeOutcome value] ∈
      (loopCode procedures).eval (encodeState state) := by
  constructor
  · intro execution
    exact Part.eq_some_iff.mp (execution.eval_eq procedures correct)
  · intro execution
    obtain ⟨actual, equal, execution⟩ := loop_complete procedures correct state _ execution
    have same := encodeOutcome_injective (List.singleton_inj.mp equal)
    subst actual
    exact execution

/-- The concrete loop returns M4's exact result on every raw game. -/
theorem loop_initial_eval (procedures : Procedures) (correct : Correct procedures)
    (game : Adjudication.Game) :
    (loopCode procedures).eval (encodeState (.evaluate game [])) =
      pure [Program.encodeOutcome (solve game)] :=
  (initial_runs game).eval_eq procedures correct

/-- Put a scalar encoded input game into the fixed seven-register initial state. -/
def initCode : Code := NatCode.tuple
  [.zero, NatCode.nth 0, .zero, .zero, .zero, .zero, .zero]

theorem initCode_eval (game : Adjudication.Game) :
    initCode.eval [gameWord game] = pure (encodeState (.evaluate game [])) := by
  simp [initCode, NatCode.tuple, encodeState, framesWord, ListCode.stack, Bind.bind]

/-- A concrete evaluator syntax tree, parameterized only by actual callee syntax trees. -/
def programCode (procedures : Procedures) : Code := .comp (loopCode procedures) initCode

/-- The complete control bridge. Concrete chess callee instantiation is still required. -/
theorem programCode_eval (procedures : Procedures) (correct : Correct procedures)
    (game : Adjudication.Game) :
    (programCode procedures).eval [gameWord game] =
      pure [Program.encodeOutcome (solve game)] := by
  simp only [programCode, Code.comp_eval, initCode_eval, Bind.bind, Part.pure_eq_some,
    Part.bind_some, loop_initial_eval procedures correct]

/-- Both terminal-value directions follow from the exact evaluation theorem. -/
theorem programCode_value_iff (procedures : Procedures) (correct : Correct procedures)
    (game : Adjudication.Game) (value : Outcome) :
    [Program.encodeOutcome value] ∈ (programCode procedures).eval [gameWord game] ↔
      value = solve game := by
  rw [programCode_eval procedures correct]
  simpa only [Part.pure_eq_some, Part.mem_some_iff, List.singleton_inj] using
    encodeOutcome_injective.eq_iff

/-- Stack cells have a unique head and tail, as witnessed by the actual unpack procedure. -/
theorem pack_injective {a b c d : Nat} (equal : ListCode.pack a b = ListCode.pack c d) :
    a = c ∧ b = d := by
  have left := ListCode.unpack_eval a b []
  have right := ListCode.unpack_eval c d []
  rw [equal] at left
  exact List.cons.inj (Part.some_injective (left.symm.trans right)) |>.imp_right
    (fun h ↦ List.singleton_inj.mp h)

theorem stack_injective : Function.Injective ListCode.stack := by
  intro first
  induction first with
  | nil =>
    intro second equal
    cases second with
    | nil => rfl
    | cons word rest =>
      exact ((Nat.ne_of_gt (ListCode.pack_pos word (ListCode.stack rest))) equal.symm).elim
  | cons word rest ih =>
    intro second equal
    cases second with
    | nil =>
      exact ((Nat.ne_of_gt (ListCode.pack_pos word (ListCode.stack rest))) equal).elim
    | cons next tail =>
      obtain ⟨head, tail⟩ := pack_injective equal
      exact congrArg₂ List.cons head (ih tail)

theorem gameWord_injective : Function.Injective gameWord :=
  stack_injective.comp Data.encodeGame_injective

theorem colorWord_injective : Function.Injective Data.encodeColor := by
  intro first second equal
  cases first <;> cases second <;> simp_all [Data.encodeColor]

theorem kindWord_injective : Function.Injective Data.encodeKind := by
  intro first second equal
  cases first <;> cases second <;> simp_all [Data.encodeKind]

theorem promotionWord_injective : Function.Injective promotionWord := by
  intro first second equal
  cases first <;> cases second <;>
    simp_all [promotionWord, kindWord_injective.eq_iff]
  omega

theorem squareWord_lt (square : Square) : squareWord square < 64 := by
  unfold squareWord
  omega

theorem squareWord_injective : Function.Injective squareWord := by
  intro first second equal
  cases first
  cases second
  simp only [squareWord] at equal
  simp only [Square.mk.injEq, Fin.ext_iff]
  omega

theorem promotionWord_lt (promotion : Option PieceKind) : promotionWord promotion < 7 := by
  cases promotion with
  | none => decide
  | some kind => cases kind <;> decide

theorem plyWord_injective : Function.Injective plyWord := by
  intro first second equal
  have sf := squareWord_lt first.src
  have ss := squareWord_lt second.src
  have df := squareWord_lt first.dst
  have ds := squareWord_lt second.dst
  have pf := promotionWord_lt first.promotion
  have ps := promotionWord_lt second.promotion
  have digits : squareWord first.src = squareWord second.src ∧
      squareWord first.dst = squareWord second.dst ∧
      promotionWord first.promotion = promotionWord second.promotion := by
    unfold plyWord at equal
    omega
  have source := squareWord_injective digits.1
  have destination := squareWord_injective digits.2.1
  have promotion := promotionWord_injective digits.2.2
  cases first
  cases second
  simp_all

theorem actionWord_injective : Function.Injective actionWord := by
  intro first second equal
  cases first with
  | claimDraw =>
    cases second with
    | claimDraw => rfl
    | play ply => exact (Nat.ne_of_gt (plyWord_pos ply) equal.symm).elim
  | play ply =>
    cases second with
    | claimDraw => exact (Nat.ne_of_gt (plyWord_pos ply) equal).elim
    | play next => exact congrArg Action.play (plyWord_injective equal)

theorem actionsWord_injective : Function.Injective actionsWord := by
  exact stack_injective.comp (List.map_injective_iff.mpr actionWord_injective)

theorem bestWord_injective : Function.Injective bestWord := by
  intro first second equal
  cases first <;> cases second <;> simp_all [bestWord, encodeOutcome_injective.eq_iff]

theorem frameWord_injective : Function.Injective frameWord := by
  intro first second equal
  have words := stack_injective equal
  cases first
  cases second
  simpa only [frameWords, List.cons.injEq, gameWord_injective.eq_iff,
    actionsWord_injective.eq_iff, bestWord_injective.eq_iff, colorWord_injective.eq_iff,
    and_true, Frame.mk.injEq] using words

theorem framesWord_injective : Function.Injective framesWord := by
  exact stack_injective.comp (List.map_injective_iff.mpr frameWord_injective)

/-- The control registers represent source states faithfully, including full frame stacks. -/
theorem encodeState_injective : Function.Injective encodeState := by
  intro first second equal
  cases first <;> cases second <;>
    simp_all only [encodeState, List.cons.injEq, gameWord_injective.eq_iff,
      actionsWord_injective.eq_iff, bestWord_injective.eq_iff, colorWord_injective.eq_iff,
      framesWord_injective.eq_iff, encodeOutcome_injective.eq_iff, Nat.reduceEqDiff,
      true_and, and_true, false_and]
  rename_i first frames second rest
  cases first
  cases second
  simp_all

end Chess.Compilation.Control
