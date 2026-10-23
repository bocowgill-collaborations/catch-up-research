import CatchUp
import Lean.Util.CollectAxioms

/-! Check every public Catch-Up theorem currently in the imported environment. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if (match info with | .thmInfo _ => true | _ => false) &&
        (name.toString.startsWith "CatchUp." || name.toString.startsWith "CatchUpSearch.") then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Forbidden axiom {ax} in {name}"
      count := count + 1
  if count == 0 then throwError "No Catch-Up theorems found"
  logInfo m!"Full theorem audit passed: {count} public Catch-Up theorems"
