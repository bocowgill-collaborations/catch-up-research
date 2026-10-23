import CatchUp.Machine.ReadShare.Graph

namespace CatchUp.Machine.ReadShare
open Turing PartrecToTM2 ConjectureMachines Compilation TemplateGraph
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

theorem reader_main : data.readPC 54 = 285 := by decide +kernel
theorem reader_rev : data.readPC 63 = 302 := by decide +kernel

theorem read_main (old top : Option Γ') :
    SharedModel.readFn RuntimeModel.s004 old top = top := by
  rcases old with _ | (_ | _ | _ | _) <;>
    rcases top with _ | (_ | _ | _ | _) <;> rfl

theorem read_rev (old top : Option Γ') :
    SharedModel.readFn RuntimeModel.s011 old top = top := by
  rcases old with _ | (_ | _ | _ | _) <;>
    rcases top with _ | (_ | _ | _ | _) <;> rfl

/-- Every glyph and every old store: these exact loads kill the old value. -/
theorem main_row : data.rows 285 =
    .load (fun a _ => a.2 .main) (.goto fun _ _ => 284) := by
  change SharedModel.row0285 = _
  unfold SharedModel.row0285
  congr 1
  funext a v
  exact read_main v (a.2 .main)

theorem rev_row : data.rows 302 =
    .load (fun a _ => a.2 .rev) (.goto fun _ _ => 301) := by
  change SharedModel.row0302 = _
  unfold SharedModel.row0302
  congr 1
  funext a v
  exact read_rev v (a.2 .rev)

theorem main_payload (glyph : Chess.Compilation.Templates.Symbol) :
    payloadStmt data (data.readPC 54) glyph =
      .load (fun _ _ => glyph.2 .main)
        (.goto fun _ _ => BinaryTemplates.normal 270 1250 (284 : Fin 4042)) := by
  rw [reader_main]
  simp only [payloadStmt, main_row, tailStmt, jump]

theorem rev_payload (glyph : Chess.Compilation.Templates.Symbol) :
    payloadStmt data (data.readPC 63) glyph =
      .load (fun _ _ => glyph.2 .rev)
        (.goto fun _ _ => BinaryTemplates.normal 270 1250 (301 : Fin 4042)) := by
  rw [reader_rev]
  simp only [payloadStmt, rev_row, tailStmt, jump]

end CatchUp.Machine.ReadShare
