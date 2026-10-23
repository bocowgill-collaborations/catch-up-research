/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Compilation.SourceModel
public meta import Cryptids.Chess.Compilation.Source
public meta import Lean

/-! # Kernel certificates for the literal chess program table -/

@[expose] public section
namespace Chess.Compilation.SourceCertificate
open Turing.ToPartrec ConjectureMachines.Compilation

set_option maxRecDepth 32768
set_option Elab.async false

/-- Every literal row states its child bound and one exact shared model constructor. -/
def RowCertificate (rows : Array CodeDAG.Node) (model : Nat → Code) (i : Nat) : Prop :=
  ∃ node, rows[i]? = some node ∧ node.Below i ∧ model i = node.build model

/-- A constructor model determines the exact decoder, without expanding the model's trees. -/
theorem decode_of_model (rows : Array CodeDAG.Node) (model : Nat → Code)
    (certificates : ∀ i < rows.size, RowCertificate rows model i) :
    ∀ i < rows.size, CodeDAG.decode rows i = model i := by
  have topology : ∀ (i : Nat) (node : CodeDAG.Node), rows[i]? = some node → node.Below i := by
    intro i node found
    obtain ⟨other, row, below, _⟩ := certificates i (Array.getElem?_eq_some_iff.mp found).1
    have equal : other = node := Option.some.inj (row.symm.trans found)
    simpa only [equal] using below
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro bound
    obtain ⟨node, row, below, modelRow⟩ := certificates i bound
    rw [CodeDAG.decode_row rows topology i node row, modelRow]
    exact node.build_congr i below _ _ (fun j before => ih j before (before.trans bound))

/-- Structural alignment records one constructor equation per literal row. -/
def RowsCertificate (model : Nat → Code) : Nat → List CodeDAG.Node → Prop
  | _, [] => True
  | offset, node :: rest => node.Below offset ∧ model offset = node.build model ∧
      RowsCertificate model (offset + 1) rest

theorem rows_step (model : Nat → Code) (offset : Nat) (node : CodeDAG.Node)
    (rest : List CodeDAG.Node) (below : node.Below offset)
    (meaning : model offset = node.build model) (tail : RowsCertificate model (offset + 1) rest) :
    RowsCertificate model offset (node :: rest) := ⟨below, meaning, tail⟩

theorem rows_append (model : Nat → Code) (offset : Nat) (first second : List CodeDAG.Node)
    (left : RowsCertificate model offset first)
    (right : RowsCertificate model (offset + first.length) second) :
    RowsCertificate model offset (first ++ second) := by
  induction first generalizing offset with
  | nil => simpa only [List.length_nil, Nat.add_zero, List.nil_append] using right
  | cons node first ih =>
    obtain ⟨below, meaning, tail⟩ := left
    refine ⟨below, meaning, ih (offset + 1) tail ?_⟩
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using right

theorem rows_get (model : Nat → Code) (rows : List CodeDAG.Node) (offset : Nat)
    (certificate : RowsCertificate model offset rows) (i : Nat) (node : CodeDAG.Node)
    (found : rows[i]? = some node) :
    node.Below (offset + i) ∧ model (offset + i) = node.build model := by
  induction rows generalizing offset i with
  | nil => simp at found
  | cons first rest ih =>
    obtain ⟨below, meaning, tail⟩ := certificate
    cases i with
    | zero =>
      have equal : first = node := by simpa using found
      subst node
      simpa only [Nat.add_zero] using And.intro below meaning
    | succ i =>
      have later := ih (offset + 1) tail i (by simpa using found)
      simpa only [Nat.add_assoc, Nat.add_comm 1] using later

theorem indexed_of_structural (rows : Array CodeDAG.Node) (model : Nat → Code)
    (certificate : RowsCertificate model 0 rows.toList) :
    ∀ i < rows.size, RowCertificate rows model i := by
  intro i bound
  let node := rows[i]
  have found : rows[i]? = some node := Array.getElem?_eq_getElem bound
  have inList : rows.toList[i]? = some node := by simpa using found
  obtain ⟨below, meaning⟩ := rows_get model rows.toList 0 certificate i node inList
  exact ⟨node, found, by simpa only [Nat.zero_add] using below,
    by simpa only [Nat.zero_add] using meaning⟩

def model (i : Nat) : Code := SourceModel.codeTree.lookup i

end Chess.Compilation.SourceCertificate

set_option Elab.async false

meta section
namespace Chess.Compilation.SourceCertificate.Generator
open Lean Meta Elab Command
open Turing.ToPartrec ConjectureMachines.Compilation

structure CertState where
  cache : Std.HashMap (Expr × Name) Name := {}
  count : Nat := 0
  hits : Nat := 0

/-- Build ordinary named congruence proofs. Fuel bounds the generator, not program execution. -/
def certify : Nat → Expr → Name → StateRefT CertState MetaM Expr
  | 0, _, _ => throwError "Source certificate depth limit"
  | fuel + 1, source, target => do
    if let some name := (← get).cache[(source, target)]? then
      modify fun s => {s with hits := s.hits + 1}
      return mkConst name
    if (← get).count >= 50000 then throwError "Source certificate node limit"
    let sourceHead ← whnf source
    let targetHead ← whnf (mkConst target)
    unless sourceHead.getAppFn == targetHead.getAppFn do
      throwError "Source/model constructor mismatch at {target}"
    let sourceArgs := sourceHead.getAppArgs
    let targetArgs := targetHead.getAppArgs
    let proof ← match sourceArgs.size with
      | 0 => mkEqRefl sourceHead
      | 1 =>
        let child ← certify fuel sourceArgs[0]! targetArgs[0]!.constName!
        mkCongrArg sourceHead.getAppFn child
      | 2 =>
        let left ← certify fuel sourceArgs[0]! targetArgs[0]!.constName!
        let right ← certify fuel sourceArgs[1]! targetArgs[1]!.constName!
        mkAppM ``congrArg₂ #[sourceHead.getAppFn, left, right]
      | _ => throwError "Unexpected Code constructor arity"
    let name := Name.str `Chess.Compilation.SourceCertificate.Generated
      ("node" ++ toString (← get).count)
    let type ← mkEq source (mkConst target)
    addDecl (.thmDecl {name := name, levelParams := [], type := type, value := proof}) true
    modify fun s => {s with count := s.count + 1, cache := s.cache.insert (source, target) name}
    return mkConst name

elab "certify_chess_source" : command => do
  liftTermElabM do
    let source := mkConst ``Chess.Compilation.Source.program
    let target := mkConst ``SourceModel.code5951
    let (proof, state) ← (certify 32768 source ``SourceModel.code5951).run {}
    let type ← mkEq source target
    addDecl (.thmDecl {
      name := `Chess.Compilation.SourceCertificate.source_eq_model
      levelParams := [], type := type, value := proof}) true
    logInfo m!"Source certificate: {state.count} checked lemmas, {state.hits} cache hits"

def rowExpr (i : Nat) : MetaM Expr := do
  let code ← whnf (mkConst (Name.str `Chess.Compilation.SourceModel ("code" ++ toString i)))
  let args := code.getAppArgs
  let child (e : Expr) : MetaM Expr := do
    match e.constName! with
    | .str `Chess.Compilation.SourceModel name =>
      match (name.drop 4).toString.toNat? with
      | some n => return mkNatLit n
      | none => throwError "Malformed shared child constant"
    | _ => throwError "Child is not a shared model constant"
  match code.getAppFn.constName! with
  | ``Code.zero' => return mkConst ``CodeDAG.Node.zero
  | ``Code.succ => return mkConst ``CodeDAG.Node.succ
  | ``Code.tail => return mkConst ``CodeDAG.Node.tail
  | ``Code.cons =>
    return mkApp2 (mkConst ``CodeDAG.Node.cons) (← child args[0]!) (← child args[1]!)
  | ``Code.comp =>
    return mkApp2 (mkConst ``CodeDAG.Node.comp) (← child args[0]!) (← child args[1]!)
  | ``Code.case =>
    return mkApp2 (mkConst ``CodeDAG.Node.branch) (← child args[0]!) (← child args[1]!)
  | ``Code.fix => return mkApp (mkConst ``CodeDAG.Node.fix) (← child args[0]!)
  | _ => throwError "Unexpected shared model constructor"

def blockName (offset count : Nat) : Name :=
  Name.str `Chess.Compilation.SourceModel ("rowBlock" ++ toString offset ++ "_" ++ toString count)

def certifyChunk (offset count : Nat) : MetaM Expr := do
  let model := mkConst ``SourceCertificate.model
  let mut list := mkApp (mkConst ``List.nil [0]) (mkConst ``CodeDAG.Node)
  let mut proof := mkConst ``True.intro
  for j in (List.range count).reverse do
    let i := offset + j
    let row ← rowExpr i
    let belowProp := mkApp2 (mkConst ``CodeDAG.Node.Below) row (mkNatLit i)
    let below ← mkDecideProof belowProp
    let meaning ← mkEqRefl (mkConst (Name.str `Chess.Compilation.SourceModel
      ("code" ++ toString i)))
    proof := mkAppN (mkConst ``rows_step)
      #[model, mkNatLit i, row, list, below, meaning, proof]
    list := mkApp3 (mkConst ``List.cons [0]) (mkConst ``CodeDAG.Node) row list
  return proof

def certifyBlocks : Nat → Nat → Nat → MetaM Expr
  | 0, _, _ => throwError "Row certificate depth limit"
  | fuel + 1, offset, chunks => do
    let count := chunks * 32
    let model := mkConst ``SourceCertificate.model
    let rows := mkConst (blockName offset count)
    let proof ← if chunks = 1 then certifyChunk offset 32
      else
        let left := chunks / 2
        let right := chunks - left
        let first ← certifyBlocks fuel offset left
        let second ← certifyBlocks fuel (offset + left * 32) right
        pure <| mkAppN (mkConst ``rows_append)
          #[model, mkNatLit offset, mkConst (blockName offset (left * 32)),
            mkConst (blockName (offset + left * 32) (right * 32)), first, second]
    let type := mkApp3 (mkConst ``RowsCertificate) model (mkNatLit offset) rows
    let name := Name.str `Chess.Compilation.SourceCertificate.RowProof
      ("block" ++ toString offset ++ "_" ++ toString count)
    addDecl (.thmDecl {name := name, levelParams := [], type := type, value := proof}) true
    return mkConst name

elab "certify_chess_rows" : command => do
  liftTermElabM do
    let proof ← certifyBlocks 32 0 186
    let type := mkApp3 (mkConst ``RowsCertificate) (mkConst ``SourceCertificate.model)
      (mkNatLit 0) (mkConst (blockName 0 5952))
    addDecl (.thmDecl {
      name := `Chess.Compilation.SourceCertificate.structural_certificate
      levelParams := [], type := type, value := proof}) true
    logInfo m!"Literal row certificate: 5952 checked rows in 186 chunks"

end Chess.Compilation.SourceCertificate.Generator

set_option maxHeartbeats 4000000 in
-- The complete certificate emits several thousand separately checked shared lemmas.
certify_chess_source

set_option maxHeartbeats 4000000 in
-- Balanced blocks share the proof of all 5952 exact row equations.
certify_chess_rows

end

namespace Chess.Compilation.SourceCertificate
open Turing.ToPartrec ConjectureMachines.Compilation

set_option maxRecDepth 32768

theorem rows_size : SourceModel.rows.size = 5952 := rfl

theorem root_eq : SourceModel.dag.root = 5951 := rfl

theorem row_certificates : ∀ i < SourceModel.rows.size,
    RowCertificate SourceModel.rows model i :=
  indexed_of_structural SourceModel.rows model structural_certificate

theorem model_root : model 5951 = SourceModel.code5951 := rfl

/-- The explicit rows decode to precisely the complete proved chess source syntax. -/
theorem program_decode : SourceModel.dag.decode = Source.program := by
  change CodeDAG.decode SourceModel.rows 5951 = Source.program
  exact ((decode_of_model SourceModel.rows model row_certificates 5951
    (by rw [rows_size]; decide)).trans model_root).trans source_eq_model.symm

theorem dag_valid : SourceModel.dag.Valid := by
  constructor
  · change 5951 < SourceModel.rows.size
    rw [rows_size]
    decide
  · intro i node found
    obtain ⟨other, row, below, _⟩ :=
      row_certificates i (Array.getElem?_eq_some_iff.mp found).1
    have equal : other = node := Option.some.inj (row.symm.trans found)
    simpa only [equal] using below

theorem program_eval (input : List Nat) :
    SourceModel.dag.decode.eval input = Source.program.eval input := by
  rw [program_decode]

theorem serialized_length : (CodeDAG.serialize SourceModel.dag).length = 17858 := by
  rw [CodeDAG.serialize_length]
  change 2 + 3 * SourceModel.rows.size = 17858
  rw [rows_size]

theorem serialized_roundtrip :
    CodeDAG.deserialize (CodeDAG.serialize SourceModel.dag) = some SourceModel.dag :=
  CodeDAG.deserialize_serialize SourceModel.dag dag_valid

end Chess.Compilation.SourceCertificate
