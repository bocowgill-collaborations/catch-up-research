/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Mathlib.Data.List.GetD

/-! # Balanced literal transition tables

Cached left-subtree sizes support shallow literal-row lookup. The validity predicate checks every
cache, and lookup is proved equal to the ordinary flattened-list semantics.
-/

@[expose] public section

namespace ConjectureMachines.Compilation.Balanced

open Turing

/-- A literal row tree with a cached number of leaves in each left subtree. -/
inductive RowTree (α : Type*)
  | empty
  | leaf (row : α)
  | branch (leftCount : ℕ) (left right : RowTree α)

namespace RowTree

variable {α : Type*}

/-- The actual structural leaf count, independent of cached branch fields. -/
def count : RowTree α → ℕ
  | .empty => 0
  | .leaf _ => 1
  | .branch _ left right => left.count + right.count

/-- Left-to-right literal row order. -/
def flatten : RowTree α → List α
  | .empty => []
  | .leaf row => [row]
  | .branch _ left right => left.flatten ++ right.flatten

/-- Every cached left count is exact, recursively. No balance or row content is assumed. -/
def WellFormed : RowTree α → Prop
  | .empty => True
  | .leaf _ => True
  | .branch leftCount left right =>
      leftCount = left.count ∧ left.WellFormed ∧ right.WellFormed

instance decidableWellFormed (tree : RowTree α) : Decidable tree.WellFormed :=
  match tree with
  | .empty => isTrue trivial
  | .leaf _ => isTrue trivial
  | .branch leftCount left right =>
      letI := decidableWellFormed left
      letI := decidableWellFormed right
      inferInstanceAs (Decidable
        (leftCount = left.count ∧ left.WellFormed ∧ right.WellFormed))

/-- Read one literal row using cached branch counts, with a caller-supplied fallback. -/
def lookup : RowTree α → ℕ → α → α
  | .empty, _, fallback => fallback
  | .leaf row, index, fallback => if index = 0 then row else fallback
  | .branch leftCount left right, index, fallback =>
      if index < leftCount then left.lookup index fallback
      else right.lookup (index - leftCount) fallback

theorem count_eq_length (tree : RowTree α) : tree.count = tree.flatten.length := by
  induction tree <;> simp_all [count, flatten]

/-- Valid caches make lookup exactly ordinary list lookup, including out-of-range fallbacks. -/
theorem lookup_eq_getD (tree : RowTree α) (valid : tree.WellFormed)
    (index : ℕ) (fallback : α) : tree.lookup index fallback = tree.flatten.getD index fallback := by
  induction tree generalizing index with
  | empty => rfl
  | leaf row => cases index <;> simp [lookup, flatten, List.getD]
  | branch leftCount left right ihl ihr =>
      obtain ⟨rfl, validLeft, validRight⟩ := valid
      by_cases before : index < left.count
      · rw [lookup, ite_eq_left before, ihl validLeft]
        exact (List.getD_append left.flatten right.flatten fallback index
          (by simpa [count_eq_length] using before)).symm
      · rw [lookup, ite_eq_right before, ihr validRight, count_eq_length left]
        exact (List.getD_append_right left.flatten right.flatten fallback index
          (by simpa [count_eq_length] using Nat.le_of_not_gt before)).symm

/-- The maximum number of branch decisions on any path. -/
def height : RowTree α → ℕ
  | .empty => 0
  | .leaf _ => 0
  | .branch _ left right => max left.height right.height + 1

/-- The actual number of branch decisions made by a lookup. -/
def lookupDepth : RowTree α → ℕ → ℕ
  | .empty, _ => 0
  | .leaf _, _ => 0
  | .branch leftCount left right, index =>
      if index < leftCount then left.lookupDepth index + 1
      else right.lookupDepth (index - leftCount) + 1

theorem lookupDepth_le_height (tree : RowTree α) (index : ℕ) :
    tree.lookupDepth index ≤ tree.height := by
  induction tree generalizing index with
  | empty => exact le_rfl
  | leaf _ => exact le_rfl
  | branch leftCount left right ihl ihr =>
      by_cases before : index < leftCount
      · rw [lookupDepth, ite_eq_left before, height]
        exact Nat.add_le_add_right ((ihl index).trans (le_max_left _ _)) 1
      · rw [lookupDepth, ite_eq_right before, height]
        exact Nat.add_le_add_right ((ihr (index - leftCount)).trans (le_max_right _ _)) 1

end RowTree

/-- A literal transition machine that reads rows from a cached tree and symbols from each row. -/
def ofTree {q symbols : ℕ}
    (tree : RowTree (List (Option (Fin symbols × Dir × Fin q)))) : Machine q symbols :=
  ⟨fun state symbol ↦ (tree.lookup state.val []).getD symbol.val none⟩

/-- Exact identity with the ordinary row-list machine, independent of every compiler. -/
theorem ofTree_eq_ofRows {q symbols : ℕ}
    (tree : RowTree (List (Option (Fin symbols × Dir × Fin q)))) (valid : tree.WellFormed) :
    ofTree tree = Machine.ofRows tree.flatten := by
  unfold ofTree Machine.ofRows
  congr 1
  funext state symbol
  exact congrArg (fun row ↦ row.getD symbol.val none)
    (tree.lookup_eq_getD valid state.val [])

end ConjectureMachines.Compilation.Balanced

meta section

namespace ConjectureMachines.TableSyntax

open Lean Elab Term Meta

/-- Construct bounded finite data directly. The ordinary kernel still checks each proof,
including the computation of `value < bound`; no tactic task is created for each table cell. -/
public def boundedFinExpr (bound : Expr) (value : ℕ) : Expr :=
  let n := mkNatLit value
  let proposition := mkApp2 (Lean.mkConst ``Nat.lt) n bound
  let decision := mkApp2 (Lean.mkConst ``Nat.decLt) n bound
  let reflexivity := mkApp2 (Lean.mkConst ``Eq.refl [Level.one])
    (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.true)
  let proof := mkApp3 (Lean.mkConst ``of_decide_eq_true) proposition decision reflexivity
  mkApp3 (Lean.mkConst ``Fin.mk) bound n proof

/-- Read a binary transition cell and construct only ordinary typed data expressions. -/
public def balancedCellExpr (symbolBound stateBound pairType : Expr) (cell : String) :
    TermElabM Expr := do
  if cell == "---" then return mkApp (Lean.mkConst ``Option.none [Level.zero]) pairType
  else
    match cell.toList with
    | writeChar :: directionChar :: stateChars =>
        let write ← match writeChar with
          | '0' => pure 0
          | '1' => pure 1
          | _ => throwError "Invalid binary write symbol in transition cell: {cell}"
        let direction ← match directionChar with
          | 'L' => pure (Lean.mkConst ``Turing.Dir.left)
          | 'R' => pure (Lean.mkConst ``Turing.Dir.right)
          | _ => throwError "Invalid direction in transition cell: {cell}"
        let state ← match (String.ofList stateChars).toNat? with
          | some state => pure state
          | none => throwError "Invalid destination state in transition cell: {cell}"
        let finSymbol := mkApp (Lean.mkConst ``Fin) symbolBound
        let finState := mkApp (Lean.mkConst ``Fin) stateBound
        let dirState := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero])
          (Lean.mkConst ``Turing.Dir) finState
        let tail := mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero])
          (Lean.mkConst ``Turing.Dir) finState direction (boundedFinExpr stateBound state)
        let pair := mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero])
          finSymbol dirState (boundedFinExpr symbolBound write) tail
        return mkApp2 (Lean.mkConst ``Option.some [Level.zero]) pairType pair
    | _ => throwError "Malformed transition cell: {cell}"

/-- Build a midpoint tree of ordinary expressions, with explicit type arguments throughout. -/
public def balancedRowsExpr (rowType : Expr) (rows : Array Expr) (start length : ℕ) :
    TermElabM Expr := do
  match length with
  | 0 => return mkApp (Lean.mkConst ``Compilation.Balanced.RowTree.empty [Level.zero]) rowType
  | 1 =>
      match rows[start]? with
      | some row =>
          return mkApp2 (Lean.mkConst ``Compilation.Balanced.RowTree.leaf [Level.zero]) rowType row
      | none => throwError "Balanced row generator index out of range"
  | n + 2 =>
      let leftCount := (n + 2) / 2
      let left ← balancedRowsExpr rowType rows start leftCount
      let right ← balancedRowsExpr rowType rows (start + leftCount) (n + 2 - leftCount)
      return mkApp4 (Lean.mkConst ``Compilation.Balanced.RowTree.branch [Level.zero])
        rowType (mkNatLit leftCount) left right
termination_by length
decreasing_by all_goals omega

/-- Load two-column binary rows as a balanced literal constructor term. Direct expression
construction avoids hundreds of thousands of independent tactic and type-inference tasks.
The kernel checks the resulting term, finite bounds and all later cache-validity proofs. -/
elab "load_balanced_rows% " path:str : term <= expectedType? => do
  let expectedType ← instantiateMVars expectedType?
  unless expectedType.isAppOfArity ``Compilation.Balanced.RowTree 1 do
    throwError "Expected a balanced row tree type"
  let rowType := expectedType.getAppArgs[0]!
  unless rowType.isAppOfArity ``List 1 do throwError "Expected list rows"
  let optionType := rowType.getAppArgs[0]!
  unless optionType.isAppOfArity ``Option 1 do throwError "Expected optional transitions"
  let pairType := optionType.getAppArgs[0]!
  unless pairType.isAppOfArity ``Prod 2 do throwError "Expected transition triples"
  let symbolType := pairType.getAppArgs[0]!
  let tailType := pairType.getAppArgs[1]!
  unless symbolType.isAppOfArity ``Fin 1 && tailType.isAppOfArity ``Prod 2 do
    throwError "Expected finite symbols and direction/state pairs"
  let stateType := tailType.getAppArgs[1]!
  unless stateType.isAppOfArity ``Fin 1 do throwError "Expected finite state type"
  let symbolBound := symbolType.getAppArgs[0]!
  let stateBound := stateType.getAppArgs[0]!
  let contents ← liftM (m := IO) (IO.FS.readFile path.getString)
  let mut rows : Array Expr := #[]
  for rawLine in contents.splitOn "\n" do
    let line := ((rawLine.splitOn "#").headD "").trimAscii.toString
    if !line.isEmpty then
      match (line.splitOn " ").filter (fun cell ↦ !cell.isEmpty) with
      | [first, second] =>
          let a ← balancedCellExpr symbolBound stateBound pairType first
          let b ← balancedCellExpr symbolBound stateBound pairType second
          let nil := mkApp (Lean.mkConst ``List.nil [Level.zero]) optionType
          let cons := mkApp (Lean.mkConst ``List.cons [Level.zero]) optionType
          rows := rows.push (mkApp2 cons a (mkApp2 cons b nil))
      | _ => throwError "Expected 2 columns in transition table line: {rawLine}"
  balancedRowsExpr rowType rows 0 rows.size

end ConjectureMachines.TableSyntax

end
