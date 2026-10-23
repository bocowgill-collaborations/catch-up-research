/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Compilation.Control
public import Cryptids.Chess.Compilation.SourceCertificate
public import Cryptids.Compilation.RuntimeProof
public import Cryptids.Compilation.RuntimeSupport

/-! # Full chess on the fixed four-stack interpreter

The complete concrete program and initial game are finite tape data. The fixed machine
contains no rule oracle, source-dependent finite control, or assumed initial chess value.
The final binary machine additionally has to construct this finite input from blank tape.
-/

@[expose] public section
namespace Chess.Compilation.Tape
open Turing PartrecToTM2 K' ConjectureMachines.Compilation

def table : CodeDAG.DAG := SourceModel.dag

def argument : List Nat := [Control.gameWord Adjudication.Game.initial]

/-- Literal paid input; this is the initial game encoding, not a chess value. -/
def literalArgument : List Nat :=
  [0x200800801010080100100400200100080040020010008007fffffffc08102040810204410a4208eab]

theorem argument_eq : argument = literalArgument := by
  unfold argument Control.gameWord
  rw [Data.encode_initialGame]
  decide +kernel

def input : List Γ' := RuntimeWire.input table literalArgument

theorem table_valid : table.Valid := SourceCertificate.dag_valid

/-- The fixed four-stack chess program terminates exactly when the draw proposition is false. -/
theorem halts_iff :
    letI : Inhabited Λ' := ⟨Runtime.label .start⟩
    (TM2.eval Runtime.machine main input).Dom ↔ ¬ (WhiteCanAvoidLoss ∧ BlackCanAvoidLoss) := by
  refine (RuntimeProof.tm2_halts table table_valid literalArgument).trans ?_
  rw [table, SourceCertificate.program_decode, ← argument_eq]
  exact Source.program_initial_dom

end Chess.Compilation.Tape
