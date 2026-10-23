import CatchUp.Machine.RestoreShare.Proof

namespace CatchUp.Machine.RestoreShare
open Turing ConjectureMachines Compilation TemplateGraph
open ReadShare (original original_eq original_normal original_writer main_payload rev_payload old_new read_returns)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

def source := BoolGraph.machine (LazyGraph.asGraph getter) stores

theorem source_row (label : Fin 341542) :
    source label = raw.decode rawValid stores (entry label) := by
  change BoolGraph.decode (LazyGraph.asGraph getter) stores
    ((LazyGraph.asGraph getter).entries.get label) = _
  rw [LazyGraph.asGraph_entry]
  exact (ReadShare.decode_getter raw rawValid entry stores (entry label)).symm

theorem caller_statement (tag : Fin 2) :
    raw.decode rawValid stores (Fin.natAdd written.raw.count tag) =
      .load (fun _ _ => stores (if tag.val = 1 then 1 else 0))
        (BinaryTemplates.read data.decode (payload 54)) := by
  apply (Raw.decode_extend_new written.raw writerValid 2 callerNode stores tag).trans
  simp only [callerNode, buildNode, tableOf_read, written_reader, leaf]
  rfl

/-- The tag survives the shared restoring moves, and is consumed only after the
head is back at the payload. Both old loads replace it with their original result. -/
theorem caller_correct (tag : Fin 2) (v : Chess.Compilation.Templates.Store) (T : Tape Bool) :
    TM1.stepAux (raw.decode rawValid stores (Fin.natAdd written.raw.count tag)) v T =
      TM1.stepAux (BinaryTemplates.read data.decode
        (payloadStmt data (data.readPC (if tag.val = 1 then 63 else 54)))) v T := by
  rw [caller_statement]
  simp only [TM1.stepAux]
  rw [read_returns, read_returns]
  fin_cases tag
  · change TM1.stepAux (payload 54 (data.decode (ReadShare.window 11 T))) (stores 0) T =
      TM1.stepAux (payloadStmt data (data.readPC 54) (data.decode (ReadShare.window 11 T))) v T
    simp only [payload, ↓reduceIte, TM1.stepAux]
    change TM1.stepAux (payloadStmt data (data.readPC 54) (data.decode (ReadShare.window 11 T)))
      (stores 0) T = _
    rw [main_payload]
    rfl
  · change TM1.stepAux (payload 54 (data.decode (ReadShare.window 11 T))) (stores 1) T =
      TM1.stepAux (payloadStmt data (data.readPC 63) (data.decode (ReadShare.window 11 T))) v T
    simp only [payload, ↓reduceIte, TM1.stepAux]
    change TM1.stepAux (payloadStmt data (data.readPC 63) (data.decode (ReadShare.window 11 T)))
      (stores 1) T = _
    rw [rev_payload]
    rfl

theorem unchanged_reader (i : Fin 1734) (h54 : i ≠ 54) (h63 : i ≠ 63) :
    raw.decode rawValid stores ((written.root (.reader (newReader i))).castAdd 2) =
      BinaryTemplates.read data.decode (payloadStmt data (data.readPC i)) := by
  apply (Raw.decode_extend_old written.raw writerValid 2 callerNode stores _).trans
  rw [written_reader]
  have inverse : oldReader (newReader i) = i := ReadShare.old_new i h63
  have hnew : newReader i ≠ 54 := by
    intro h
    have same := congrArg oldReader h
    rw [inverse] at same
    exact h54 same
  simp only [leaf, payload, hnew, ↓reduceIte, inverse]
  rfl

theorem source_stepAux (label : Fin 341542) (v : Chess.Compilation.Templates.Store)
    (T : Tape Bool) : TM1.stepAux (source label) v T = TM1.stepAux (original label) v T := by
  rw [source_row]
  obtain ⟨label, rfl⟩ := (BinaryTemplates.labelEquiv 4042 270 1250).surjective label
  cases label with
  | inl pc =>
    change TM1.stepAux (raw.decode rawValid stores (entry (BinaryTemplates.normal 270 1250 pc))) v T = _
    simp only [entry, BinaryTemplates.normal, Equiv.symm_apply_apply]
    rw [original_normal]
    have classified := Chess.Compilation.Image.valid.classified pc
    cases kind : data.classify pc with
    | plain =>
      simp only [kind] at classified ⊢
      rw [show raw.decode rawValid stores ((written.root (.tail pc false)).castAdd 2) =
          tailStmt data pc false from
        (Raw.decode_extend_old written.raw writerValid 2 callerNode stores _).trans (written_tail pc false)]
      cases row : data.rows pc <;> simp only [row, PlainRow] at classified
      all_goals simp [tailStmt, jump, row, BinaryTemplates.normalRow]
    | read i =>
      simp only [kind] at classified ⊢
      have normal := normal_read CodeBackend.blockCode data
        Chess.Compilation.Templates.writeSites Chess.Compilation.Image.valid pc classified.2
      rw [normal, ← classified.1]
      by_cases h54 : i = 54
      · subst i
        rw [ite_eq_left rfl]
        exact caller_correct 0 v T
      · rw [ite_eq_right h54]
        by_cases h63 : i = 63
        · subst i
          rw [ite_eq_left rfl]
          exact caller_correct 1 v T
        · rw [ite_eq_right h63, unchanged_reader i h54 h63]
    | move i =>
      simp only [kind] at classified ⊢
      rw [show raw.decode rawValid stores ((written.root (.mover i)).castAdd 2) =
          BinaryTemplates.move 11 (moverDir data i) (tailStmt data (data.movePC i) false) from
        (Raw.decode_extend_old written.raw writerValid 2 callerNode stores _).trans (written_mover i)]
      have owner := classified.1
      have shape := classified.2
      have primitive := Chess.Compilation.Image.valid.primitive pc
      cases row : data.rows pc <;> simp only [row, MoveRow] at shape
      case move dir tail =>
        rw [row] at primitive
        cases tail <;> simp only [TM1Normalize.OnePrimitive] at primitive
        simp [moverDir, owner, row, tailStmt, jump, BinaryTemplates.normalRow,
          CodeBackend.blockCode_width]
  | inr pair =>
    rcases pair with ⟨site, glyph⟩
    simp only [entry, Equiv.symm_apply_apply]
    rw [show raw.decode rawValid stores ((written.root (.writer site glyph)).castAdd 2) =
        BinaryTemplates.write (data.encode (data.alphabet glyph)).toList
          (BinaryTemplates.move 11 .left (.goto fun _ v =>
            BinaryTemplates.normal 270 1250 (data.next site default v))) from
      (Raw.decode_extend_old written.raw writerValid 2 callerNode stores _).trans (written_writer site glyph)]
    rw [original_writer]

theorem step_eq : TM1.step source = TM1.step original :=
  ReadShare.step_eq_of_aux source original source_stepAux

theorem post_halts_iff (input : List Bool) :
    (TM0.eval post input).Dom ↔ (TM1.eval Chess.Compilation.Templates.machine input).Dom := by
  rw [LazyGraph.eval_eq getter stores Chess.Compilation.Templates.stores_zero input]
  change (StateTransition.eval (TM1.step source) (TM1.init input)).Dom ↔ _
  rw [step_eq, original_eq]
  rfl

end CatchUp.Machine.RestoreShare
