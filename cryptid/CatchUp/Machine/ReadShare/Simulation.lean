import CatchUp.Machine.ReadShare.Proof
import CatchUp.Machine.ReadShare.Sites
import CatchUp.Machine.ReadShare.ReaderSemantics

namespace CatchUp.Machine.ReadShare
open Turing ConjectureMachines Compilation TemplateGraph
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

theorem decode_getter {k labels : Nat} {S : Type} (r : Raw k labels)
    (valid : r.Valid) (entry : Fin labels → Fin r.count) (store : Fin k ≃ S)
    (i : Fin r.count) :
    r.decode valid store i = BoolGraph.decode
      (LazyGraph.asGraph ⟨r.node, entry, valid⟩) store i := by
  rw [Raw.decode, BoolGraph.decode,
    show (LazyGraph.asGraph ⟨r.node, entry, valid⟩).nodes.get i = r.node i from
      LazyGraph.asGraph_node _ i]
  cases row : r.node i <;> simp only []
  case move dir child => exact congrArg (TM1.Stmt.move dir) (decode_getter r valid entry store child)
  case write table child => exact congrArg (TM1.Stmt.write _) (decode_getter r valid entry store child)
  case load table child => exact congrArg (TM1.Stmt.load _) (decode_getter r valid entry store child)
  case branch table left right =>
    exact congrArg₂ (TM1.Stmt.branch _) (decode_getter r valid entry store left)
      (decode_getter r valid entry store right)
termination_by i.val
decreasing_by all_goals exact valid i _ (by simp [row, BoolGraph.Node.children])

def source := BoolGraph.machine (LazyGraph.asGraph getter) stores

theorem source_row (label : Fin 341542) :
    source label = raw.decode rawValid stores (entry label) := by
  change BoolGraph.decode (LazyGraph.asGraph getter) stores
    ((LazyGraph.asGraph getter).entries.get label) = _
  rw [LazyGraph.asGraph_entry]
  exact (decode_getter raw rawValid entry stores (entry label)).symm

abbrev original := BinaryTemplates.machine CodeBackend.blockCode data.rows
  Chess.Compilation.Templates.writeSites data.alphabet

theorem original_eq : original = Chess.Compilation.Templates.machine :=
  Chess.Compilation.Templates.machine_template.symm

theorem original_normal (pc : Fin 4042) :
    original ((BinaryTemplates.labelEquiv 4042 270 1250) (.inl pc)) =
      BinaryTemplates.normalRow CodeBackend.blockCode data.rows
        Chess.Compilation.Templates.writeSites data.alphabet pc :=
  BinaryTemplates.machine_normal _ _ _ _ pc

theorem original_writer (site : Fin 270) (glyph : Fin 1250) :
    original ((BinaryTemplates.labelEquiv 4042 270 1250) (.inr (site, glyph))) =
      BinaryTemplates.write (data.encode (data.alphabet glyph)).toList
        (BinaryTemplates.move 11 .left (.goto fun _ v =>
          BinaryTemplates.normal 270 1250 (data.next site default v))) :=
  BinaryTemplates.machine_writer _ _ _ _ site glyph

theorem caller_statement (tag : Fin 2) :
    raw.decode rawValid stores (Fin.natAdd written.raw.count tag) =
      .load (fun _ _ => stores (if tag.val = 1 then 1 else 0))
        (BinaryTemplates.readAux 11 (fun bits => leaf 54 (data.decode bits))) := by
  apply (Raw.decode_extend_new written.raw writerValid 2 callerNode stores tag).trans
  simp only [callerNode, buildNode, tableOf_read, written_reader]

theorem caller_correct (tag : Fin 2) (v : Chess.Compilation.Templates.Store) (T : Tape Bool) :
    TM1.stepAux (raw.decode rawValid stores (Fin.natAdd written.raw.count tag)) v T =
      TM1.stepAux (BinaryTemplates.read data.decode
        (payloadStmt data (data.readPC (if tag.val = 1 then 63 else 54)))) v T := by
  rw [caller_statement]
  simp only [TM1.stepAux, leaf, ↓reduceIte]
  rw [readAux_select]
  fin_cases tag
  · change TM1.stepAux (BinaryTemplates.read data.decode
        (payloadStmt data (data.readPC 54))) (stores 0) T =
      TM1.stepAux (BinaryTemplates.read data.decode
        (payloadStmt data (data.readPC 54))) v T
    rw [read_returns, read_returns, main_payload]
    rfl
  · change TM1.stepAux (BinaryTemplates.read data.decode
        (payloadStmt data (data.readPC 63))) (stores 1) T =
      TM1.stepAux (BinaryTemplates.read data.decode
        (payloadStmt data (data.readPC 63))) v T
    rw [read_returns, read_returns, rev_payload]
    rfl

theorem unchanged_reader (i : Fin 1734) (h54 : i ≠ 54) (h63 : i ≠ 63) :
    raw.decode rawValid stores ((written.root (.reader (newReader i))).castAdd 2) =
      BinaryTemplates.read data.decode (payloadStmt data (data.readPC i)) := by
  apply (Raw.decode_extend_old written.raw writerValid 2 callerNode stores _).trans
  rw [written_reader]
  have hnew : newReader i ≠ 54 := by
    intro h
    have same := congrArg oldReader h
    rw [old_new i h63] at same
    exact h54 same
  simp only [leaf, hnew, ↓reduceIte, old_new i h63]
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

theorem step_eq_of_aux {G L S : Type} [Inhabited G]
    (A B : L → TM1.Stmt G L S)
    (h : ∀ l v T, TM1.stepAux (A l) v T = TM1.stepAux (B l) v T) :
    TM1.step A = TM1.step B := by
  funext cfg
  rcases cfg with ⟨label, v, T⟩
  cases label with
  | none => rfl
  | some label => exact congrArg some (h label v T)

theorem step_eq : TM1.step source = TM1.step original :=
  step_eq_of_aux source original source_stepAux

theorem post_halts_iff (input : List Bool) :
    (TM0.eval post input).Dom ↔ (TM1.eval Chess.Compilation.Templates.machine input).Dom := by
  rw [LazyGraph.eval_eq getter stores Chess.Compilation.Templates.stores_zero input]
  change (StateTransition.eval (TM1.step source) (TM1.init input)).Dom ↔ _
  rw [step_eq, original_eq]
  rfl

end CatchUp.Machine.ReadShare
