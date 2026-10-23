/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Compilation.Encoding
public import Cryptids.Compilation.ListCode

/-! # Concrete procedures on the frozen chess data representation

These are `ToPartrec.Code` procedures with proofs about their actual partial semantics.
The board procedure reads all 64 raw cells, without reachability assumptions.
-/

@[expose] public section

namespace Chess.Compilation.Rules

open Turing.ToPartrec
open ConjectureMachines.Compilation

/-- Rank-major, file-fast square index. -/
def squareIndex (square : Square) : Nat := square.file.val + 8 * square.rank.val

theorem squareIndex_lt (square : Square) : squareIndex square < 64 := by
  unfold squareIndex
  omega

/-- Read one board cell from `squareIndex :: positionWords`. -/
def boardGet : Code :=
  .comp ListCode.get
    (.cons (.comp NatCode.add (NatCode.tuple [.head, NatCode.literal 7])) .tail)

set_option backward.isDefEq.respectTransparency false

attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some

/-- Exact behavior on arbitrary words, including malformed and short lists. -/
theorem boardGet_eval (index : Nat) (words : List Nat) :
    boardGet.eval (index :: words) = pure [words[index + 7]?.getD 0] := by
  simp [boardGet, NatCode.tuple, Bind.bind, Part.bind_some, ListCode.get_eval]

/-- The encoded board read equals the concrete board cell at every raw square. -/
theorem position_board_lookup (position : Exec.Position) (square : Square) :
    (Data.encodePosition position)[squareIndex square + 7]?.getD 0 =
      Data.encodeCell (Exec.decodeBoard position.board square) := by
  have shifted : (Data.encodePosition position)[squareIndex square + 7]? =
      ((Data.encodePosition position).drop 7)[squareIndex square]? := by
    rw [List.getElem?_drop]
    congr 1
    omega
  rw [shifted]
  have dropped : (Data.encodePosition position).drop 7 = Data.encodeBoard position.board := by
    simp [Data.encodePosition]
  rw [dropped]
  simp only [Data.encodeBoard, List.getElem?_ofFn, squareIndex_lt, ↓reduceDIte,
    Option.getD_some]
  have row : squareIndex square / 8 = square.rank.val := by unfold squareIndex; omega
  have column : squareIndex square % 8 = square.file.val := by unfold squareIndex; omega
  simp only [row, column, Exec.decodeBoard]

/-- Actual Code semantics refine the frozen board through the M2 data representation. -/
theorem boardGet_refines (position : Exec.Position) (square : Square) :
    boardGet.eval (squareIndex square :: Data.encodePosition position) =
      pure [Data.encodeCell ((Exec.decode position).board square)] := by
  rw [boardGet_eval, position_board_lookup]
  rfl

end Chess.Compilation.Rules
