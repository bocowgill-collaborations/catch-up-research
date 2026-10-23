/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Compilation.HistoryCode
public import Cryptids.Chess.Compilation.Legality
public import Cryptids.Chess.Compilation.Control
public import Cryptids.Chess.Evaluation.Correspondence

/-! # Complete concrete chess source program

All rule and evaluator callees are instantiated by finite `Code` syntax. The source
refinement is unconditional and does not assert the initial position's value.
-/

@[expose] public section
namespace Chess.Compilation.Source
open Turing.ToPartrec ConjectureMachines.Compilation

set_option backward.isDefEq.respectTransparency false

def check : Code := Scalar.compile (Geometry.inCheck (.literal 7) (.input 0))

theorem check_refines (position : Exec.Position) :
    check.eval (Data.encodePosition position) =
      pure [Geometry.truth (InCheck (Exec.decode position).board position.turn)] := by
  apply Geometry.compile_inCheck_eval
  · exact Geometry.BoardView_encodePosition position
  · rfl

def callees : HistoryCode.Callees where
  legal := Legality.code
  update := Updates.code
  check := check
  legal_refines := Legality.code_refines
  update_refines := Updates.code_refines
  check_refines := check_refines

theorem plyWord_eq (ply : Ply) : HistoryCode.plyWord ply = Control.plyWord ply := by
  unfold HistoryCode.plyWord HistoryCode.candidateIndex Control.plyWord Control.squareWord
  have hp : HistoryCode.promotionWord ply.promotion = Control.promotionWord ply.promotion := rfl
  rw [hp]
  omega

theorem actionWord_eq (action : Action) : HistoryCode.actionWord action =
    Control.actionWord action := by
  cases action with
  | claimDraw => rfl
  | play ply => exact plyWord_eq ply

def procedures : Control.Procedures where
  automatic := HistoryCode.automaticCode callees
  actions := HistoryCode.actionsCode callees
  play := HistoryCode.playCode callees
  turn := HistoryCode.turnCode

theorem procedures_correct : Control.Correct procedures where
  automatic game := HistoryCode.automaticCode_eval callees game
  actions game := by
    simpa only [procedures, Control.actionsWord, HistoryCode.gameWord, Control.gameWord,
      show HistoryCode.actionWord = Control.actionWord from funext actionWord_eq] using
      HistoryCode.actionsCode_eval callees game
  play game ply := by
    simpa only [procedures, plyWord_eq, HistoryCode.gameWord, Control.gameWord] using
      HistoryCode.playCode_eval callees game ply
  turn game := HistoryCode.turnCode_eval game

def evaluator : Code := Control.programCode procedures

theorem evaluator_eval (game : Adjudication.Game) :
    evaluator.eval [Control.gameWord game] =
      pure [Program.encodeOutcome (Evaluation.solve game)] :=
  Control.programCode_eval procedures procedures_correct game

/-- The compiled source returns exactly for a non-draw and diverges for a draw. -/
def program : Code := Program.finish evaluator

theorem program_eval (game : Adjudication.Game) :
    program.eval [Control.gameWord game] =
      if Evaluation.solve game = .draw then Part.none else pure [] :=
  Program.finish_eval evaluator _ _ (evaluator_eval game)

theorem program_dom (game : Adjudication.Game) :
    (program.eval [Control.gameWord game]).Dom ↔ Evaluation.solve game ≠ .draw :=
  Program.finish_dom evaluator _ _ (evaluator_eval game)

theorem program_initial_dom :
    (program.eval [Control.gameWord Adjudication.Game.initial]).Dom ↔
      ¬ (WhiteCanAvoidLoss ∧ BlackCanAvoidLoss) :=
  (program_dom _).trans (not_congr Evaluation.solve_initial_draw_iff)

end Chess.Compilation.Source
