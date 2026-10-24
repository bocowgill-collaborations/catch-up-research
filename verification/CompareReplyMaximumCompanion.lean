import CatchUp.ReplyMaximumCompanion
import Lean

/-! Compare all four public signatures and both definition bodies with the cache.
The source proofs have already been compiled; no cached declaration is installed.
-/

open Lean Elab Command Meta in
run_cmd do
  let (data, _) ← readModuleData
    "archive/recovered/reply-maximum-companion/ReplyMaximumCompanion.olean"
  let names := #[``CatchUp.commonMaximumPairPosition, ``CatchUp.CommonMaximumPairCatchable,
    ``CatchUp.reply_edge_from_max_has_companion, ``CatchUp.reply_edge_from_max_not_unique]
  for name in names do
    let some old := data.constants.find? (·.name == name)
      | throwError "Missing cached declaration: {name}"
    let current ← getConstInfo name
    unless old.levelParams == current.levelParams do
      throwError "Universe parameters changed: {name}"
    liftTermElabM do
      unless ← isDefEq old.type current.type do
        throwError "Recovered signature changed: {name}"
      if ← isDefEq old.type (mkConst ``False) then
        throwError "Signature-mutation control accepted: {name}"
      match old, current with
      | .defnInfo a, .defnInfo b =>
        unless ← isDefEq a.value b.value do
          throwError "Recovered definition changed: {name}"
      | .thmInfo _, .thmInfo _ => pure ()
      | _, _ => throwError "Declaration kind changed: {name}"
    logInfo m!"SOURCE_SIGNATURE_MATCH {name}"
  logInfo "SOURCE_COMPARISON_COMPLETE 4 signatures and 2 definition bodies"
