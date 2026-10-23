/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Compilation.Tape
public import Cryptids.Compilation.Code
public import Cryptids.Compilation.FlatInit
public meta import Lean

/-! # Exact finite input and its paid blank-tape prefix -/

@[expose] public section
namespace Chess.Compilation.Input
open Turing PartrecToTM2 K' ConjectureMachines ConjectureMachines.Compilation

set_option backward.isDefEq.respectTransparency false

/-- Complete table, root, separator and packed initial game, in their actual order. -/
def stack : List Γ' := Tape.input

/-- The fixed eleven-bit simultaneous-stack codec, including the initial bottom marker. -/
def binary : List Bool := blockInput CodeBackend.blockCode (TM2to1.trInit main stack)

/-- The actual finite symbols written by the blank binary initializer. -/
def bits : Array (Fin 2) := (binary.map Compilation.Binary.encodeSymbol).toArray

def rowSymbols (rows : List CodeDAG.Node) : Nat :=
  (trList (rows.flatMap CodeDAG.Node.words)).length

theorem rowSymbols_append (first second : List CodeDAG.Node) :
    rowSymbols (first ++ second) = rowSymbols first + rowSymbols second := by
  simp only [rowSymbols, List.flatMap_append, Runtime.trList_append, List.length_append]

theorem count_append (first second : List CodeDAG.Node) (left right : Nat)
    (firstCount : rowSymbols first = left) (secondCount : rowSymbols second = right) :
    rowSymbols (first ++ second) = left + right := by
  rw [rowSymbols_append, firstCount, secondCount]

theorem argument_symbols : (trList Tape.literalArgument).length = 323 := by
  decide +kernel

theorem root_symbols : (trList [SourceModel.dag.root]).length = 14 := by
  decide +kernel

end Chess.Compilation.Input

set_option Elab.async false
set_option maxRecDepth 32768

meta section
namespace Chess.Compilation.Input.Generator
open Lean Meta Elab Command
open Turing PartrecToTM2 ConjectureMachines.Compilation

def blockName (offset count : Nat) : Name :=
  Name.str `Chess.Compilation.SourceModel ("rowBlock" ++ toString offset ++ "_" ++ toString count)

/-- A proposed small numerical count. The resulting equality is independently kernel checked. -/
def wordCost (n : Nat) : Nat := if n = 0 then 1 else n.log2 + 2

def chunkCost (rows : Expr) : MetaM Nat := do
  let mut remaining := rows
  let mut total := 0
  for _ in [:32] do
    let list ← whnf remaining
    unless list.isAppOfArity ``List.cons 3 do throwError "Expected 32 literal rows"
    let args := list.getAppArgs
    let row ← whnf args[1]!
    let mut nums := #[]
    for arg in row.getAppArgs do
      let some n ← getNatValue? arg | throwError "Expected literal child index"
      nums := nums.push n
    total := total + match row.getAppFn.constName! with
      | ``CodeDAG.Node.zero => 3
      | ``CodeDAG.Node.succ => 4
      | ``CodeDAG.Node.tail => 5
      | ``CodeDAG.Node.cons =>
        wordCost 3 + wordCost nums[0]! + wordCost nums[1]!
      | ``CodeDAG.Node.comp =>
        wordCost 4 + wordCost nums[0]! + wordCost nums[1]!
      | ``CodeDAG.Node.branch =>
        wordCost 5 + wordCost nums[0]! + wordCost nums[1]!
      | ``CodeDAG.Node.fix => wordCost 6 + wordCost nums[0]! + 1
      | _ => 0
    remaining := args[2]!
  unless (← whnf remaining).isAppOfArity ``List.nil 1 do
    throwError "Unexpected extra rows in literal chunk"
  return total

def certify : Nat → Nat → Nat → MetaM (Nat × Expr)
  | 0, _, _ => throwError "Input count certificate depth limit"
  | fuel + 1, offset, chunks => do
    let count := chunks * 32
    let rows := mkConst (blockName offset count)
    let (cost, proof) ← if chunks = 1 then
      let cost ← chunkCost rows
      pure (cost, ← mkEqRefl (mkNatLit cost))
    else
      let left := chunks / 2
      let right := chunks - left
      let first ← certify fuel offset left
      let second ← certify fuel (offset + left * 32) right
      pure (first.1 + second.1, mkAppN (mkConst ``Input.count_append)
        #[mkConst (blockName offset (left * 32)),
          mkConst (blockName (offset + left * 32) (right * 32)),
          mkNatLit first.1, mkNatLit second.1, first.2, second.2])
    let type ← mkEq (mkApp (mkConst ``Input.rowSymbols) rows) (mkNatLit cost)
    let name := Name.str `Chess.Compilation.Input.CountProof
      ("block" ++ toString offset ++ "_" ++ toString count)
    addDecl (.thmDecl {name := name, levelParams := [], type := type, value := proof}) true
    return (cost, mkConst name)

elab "certify_chess_input_count" : command => do
  liftTermElabM do
    let (cost, proof) ← certify 32 0 186
    let type ← inferType proof
    addDecl (.thmDecl {
      name := `Chess.Compilation.Input.row_symbols
      levelParams := [], type := type, value := proof}) true
    logInfo m!"Checked 186 literal row chunks: {cost} stack symbols"

end Chess.Compilation.Input.Generator

set_option maxHeartbeats 4000000 in
-- Each literal chunk is counted by the kernel, then the shared append tree combines the results.
certify_chess_input_count

end

namespace Chess.Compilation.Input
open Turing PartrecToTM2 K' ConjectureMachines ConjectureMachines.Compilation

set_option backward.isDefEq.respectTransparency false

theorem stack_eq_raw : stack = trList [SourceModel.dag.root] ++
    trList (SourceModel.rowBlock0_5952.flatMap CodeDAG.Node.words) ++
      Γ'.consₗ :: trList Tape.literalArgument := rfl

/-- The counted packed argument is exactly the encoded standard initial game. -/
theorem stack_eq_game : stack = RuntimeWire.input SourceModel.dag
    [Control.gameWord Adjudication.Game.initial] := by
  change RuntimeWire.input SourceModel.dag Tape.literalArgument =
    RuntimeWire.input SourceModel.dag Tape.argument
  rw [Tape.argument_eq]

theorem table_symbols :
    (trList (RuntimeWire.flatTriples Tape.table.rows)).length = 141042 := row_symbols

theorem stack_length : stack.length = 141380 := by
  rw [stack_eq_raw]
  have table := row_symbols
  change (trList (SourceModel.rowBlock0_5952.flatMap CodeDAG.Node.words)).length = 141042
    at table
  simp only [List.length_append, List.length_cons, root_symbols, table, argument_symbols]

/-- The bottom marker occupies an existing cell for nonempty stack input. -/
theorem encoded_length (values : List Γ') :
    (blockInput CodeBackend.blockCode (TM2to1.trInit main values)).length =
      11 * max 1 values.length := by
  have blocks (symbols : List Adequacy.PartrecAlphabet) :
      (blockInput CodeBackend.blockCode symbols).length = 11 * symbols.length := by
    induction symbols with
    | nil => rfl
    | cons symbol rest ih =>
      simp only [blockInput, List.flatMap_cons, List.length_append,
        List.Vector.toList_length, CodeBackend.blockCode_width, List.length_cons] at *
      omega
  have initial : (TM2to1.trInit (Γ := fun _ : K' => Γ') main values).length =
      max 1 values.length := by
    simp only [TM2to1.trInit, List.length_cons, List.length_tail, List.length_map,
      List.length_reverse]
    omega
  rw [blocks, initial]

theorem binary_length : binary.length = 1555180 := by
  rw [binary, encoded_length, stack_length]
  decide

theorem block_roundtrip (symbol : Adequacy.PartrecAlphabet) :
    CodeBackend.blockCode.decode (CodeBackend.blockCode.encode symbol) = symbol :=
  CodeBackend.decode_encodeSymbol symbol

theorem bits_size : bits.size = 1555180 := by
  simp only [bits, List.size_toArray, List.length_map, binary_length]

theorem bits_toList : bits.toList = binary.map Compilation.Binary.encodeSymbol := by
  simp only [bits, List.toList_toArray]

/-- Decoding every written binary symbol recovers the complete encoded input bit list. -/
theorem decode_bits : bits.toList.map Compilation.Binary.decodeSymbol = binary := by
  simp only [bits_toList, List.map_map, Function.comp_def, Compilation.Binary.decode_encode,
    List.map_id_fun', id_eq]

/-- The complete binary-symbol array is determined by its decoded bit stream. -/
theorem bits_unique (other : Array (Fin 2))
    (decoded : other.toList.map Compilation.Binary.decodeSymbol = binary) : other = bits := by
  apply Array.ext'
  have encoded := congrArg (List.map Compilation.Binary.encodeSymbol) decoded
  simpa only [List.map_map, Function.comp_def, Compilation.Binary.encode_decode,
    List.map_id_fun', id_eq, bits_toList] using encoded

theorem paid_prefix : 2 * bits.size = 3110360 := by
  rw [bits_size]

theorem initialise_states (body : BundledMachine 2) :
    (FlatInit.initialise bits body).states = body.states + 3110360 := by
  change body.states + 2 * bits.size = _
  rw [paid_prefix]

/-- After the entire paid prefix, the original body starts with the exact input and head. -/
theorem initialise_run (body : BundledMachine 2) :
    FlatInit.runFrom (FlatInit.initialise bits body).toMachine 3110360 ConjectureMachines.init =
      some (FlatInit.embed bits body ⟨0, Turing.Tape.mk₁ bits.toList⟩) := by
  rw [← paid_prefix]
  exact FlatInit.initialise_run bits body

end Chess.Compilation.Input
