import CatchUp.TwoBufferMandatory
import Lean

/-!
Export the actual Lean policy table for comparison with the preserved absolute-score
replay. This executable is a cross-language regression check, not a proof premise.
-/

open Lean

private def stateJson (p : CatchUp.GamePosition) : Lean.Json :=
  Lean.Json.mkObj [
    ("remaining", toJson (p.remaining.sort (· ≤ ·))),
    ("deficit", toJson p.deficit),
    ("mover", toJson (if p.toMove = .p1 then (0 : Nat) else 1))]

private def actionJson (a : CatchUp.TwoBuffer.Action) : String × Lean.Json :=
  match a with
  | .actualPick x => ("actualPick", toJson x)
  | .actualOpponent => ("actualOpponent", .null)
  | .shadowPick x => ("shadowPick", toJson x)
  | .shadowStrategy => ("shadowStrategy", .null)

def main : IO Unit := do
  let rows := CatchUp.TwoBuffer.policyEntries.map fun ((u, v), a) =>
    let (name, pick) := actionJson a
    Lean.Json.mkObj [("U", stateJson u), ("V", stateJson v),
      ("action", toJson name), ("pick", pick)]
  IO.println (toJson rows).compress
