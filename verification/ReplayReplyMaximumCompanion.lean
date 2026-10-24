import CatchUp.Earlier.ReplyDigraphReduction
import Lean

/-!
Replay the retained module's declarations, not its imported environment. Every
declaration is added with kernel checking enabled against the current library.
This diagnostic is separate from the readable source proof and default build.
-/

open Lean Elab Command in
run_cmd do
  let (data, _) ← readModuleData
    "archive/recovered/reply-maximum-companion/ReplyMaximumCompanion.olean"
  unless data.constants.size == 10 do
    throwError "Expected exactly ten cached declarations"
  let bad : Declaration := .thmDecl {
    name := `RecoveryInvalidControl, levelParams := [],
    type := mkConst ``False, value := mkConst ``True.intro }
  if ((← getEnv).addDeclCore 0 bad none true).isOk then
    throwError "Kernel accepted the invalid-proof control"
  logInfo "Invalid-proof control rejected"
  let mut pending := data.constants
  for _ in [:data.constants.size + 1] do
    let mut next := #[]
    for c in pending do
      let deps := c.type.getUsedConstants ++ (c.value?.map Expr.getUsedConstants |>.getD #[])
      let env ← getEnv
      if deps.all env.contains then
        unless !env.contains c.name do
          throwError "Cached declaration already exists: {c.name}"
        let decl ← match c with
          | .thmInfo t => pure (.thmDecl t)
          | .defnInfo d => pure (.defnDecl d)
          | _ => throwError "Unexpected constant kind: {c.name}"
        match (← getEnv).addDeclCore 0 decl none true with
        | .ok env =>
          setEnv env
          logInfo m!"KERNEL_REPLAYED {c.name}"
        | .error e => throwError "Kernel rejected {c.name}: {e.toMessageData (← getOptions)}"
      else
        next := next.push c
    pending := next
  unless pending.isEmpty do
    throwError "Unresolved cached dependencies"
  for c in data.constants do
    for ax in ← collectAxioms c.name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Forbidden axiom {ax} in {c.name}"
  logInfo m!"KERNEL_REPLAY_COMPLETE {data.constants.size} declarations"

#print axioms CatchUp.reply_edge_from_max_has_companion
#print axioms CatchUp.reply_edge_from_max_not_unique
