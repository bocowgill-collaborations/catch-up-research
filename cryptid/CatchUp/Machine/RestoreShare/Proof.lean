import CatchUp.Machine.RestoreShare.Graph

namespace CatchUp.Machine.RestoreShare
open Turing ConjectureMachines Compilation TemplateGraph
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

abbrev tagTest := ReadShare.tagTest

def payload (i : Fin 1733) (glyph : Chess.Compilation.Templates.Symbol) :
    TM1.Stmt Bool (Fin 341542) Chess.Compilation.Templates.Store :=
  if i = 54 then
    .branch (fun _ v => tagTest v)
      (payloadStmt data (data.readPC 63) glyph)
      (payloadStmt data (data.readPC 54) glyph)
  else payloadStmt data (data.readPC (oldReader i)) glyph

def leaf (i : Fin 1733) (glyph : Chess.Compilation.Templates.Symbol) :=
  BinaryTemplates.move 11 .left (payload i glyph)

theorem original_payload (i : Fin 1734) (glyph : Fin 1250) :
    payloadBase.raw.decode payloadValid stores (payloadBase.root (.readLeaf i glyph)) =
      payloadStmt data (data.readPC i) (data.alphabet glyph) :=
  payloads_leaf data (base data) (base_valid data) (base_tail data) i glyph

theorem seed_leaf (i : Fin 1733) (glyph : Fin 1250) :
    seed.raw.decode dispatchValid stores (seed.root (.readLeaf i glyph)) =
      payload i (data.alphabet glyph) := by
  change dispatchRaw.decode dispatchValid stores _ = _
  simp only [seed]
  split_ifs with hi
  · apply (Raw.decode_extend_new payloadBase.raw payloadValid 1250 dispatchNode stores glyph).trans
    simp only [dispatchNode, buildNode, tableOf_read, original_payload,
      payload, hi, ↓reduceIte, tagTest, ReadShare.tagTest]
  · apply (Raw.decode_extend_old payloadBase.raw payloadValid 1250 dispatchNode stores
      (payloadBase.root (.readLeaf (oldReader i) glyph))).trans
    simp only [payload, hi, ↓reduceIte]
    exact original_payload (oldReader i) glyph

theorem seed_tail (pc : Fin 4042) (side : Bool) :
    seed.raw.decode dispatchValid stores (seed.root (.tail pc side)) = tailStmt data pc side := by
  exact (Raw.decode_extend_old payloadBase.raw payloadValid 1250 dispatchNode stores
    (payloadBase.root (.tail pc side))).trans (payloads_tail data pc side)

theorem seed_writerTail (site : Fin 270) :
    seed.raw.decode dispatchValid stores (seed.root (.writerTail site)) =
      .goto (fun _ v => BinaryTemplates.normal 270 1250 (data.next site default v)) := by
  apply (Raw.decode_extend_old payloadBase.raw payloadValid 1250 dispatchNode stores
    (payloadBase.root (.writerTail site))).trans
  exact (Bundle.decode_add_old (base data) (base_valid data) (1734 * 1250)
    (payloadNode data (base data)) payloadPick stores
    (.writerTail site) rfl).trans (base_writerTail data site)

theorem seed_mover (i : Fin 1188) :
    seed.raw.decode dispatchValid stores (seed.root (.mover i)) =
      tailStmt data (data.movePC i) false := by
  exact (Raw.decode_extend_old payloadBase.raw payloadValid 1250 dispatchNode stores
    (payloadBase.root (.mover i))).trans (payloads_tail data (data.movePC i) false)

theorem prepared_leaf (reader : Fin 1733) (glyph : Fin 1250) :
    prepared.raw.decode preparedValid stores (prepared.root (.readLeaf reader glyph)) =
      leaf reader (data.alphabet glyph) := by
  let i : Fin chainCount := ((finProdFinEquiv (reader, glyph)).castAdd 270).castAdd 1188
  have ref : chainRef (n := 4042) i = .readLeaf reader glyph := by
    simpa only [i, chainRef, Fin.addCases_left] using
      congrArg (fun pair : Fin 1733 × Fin 1250 => Ref.readLeaf (n := 4042) (w := 270)
        (u := 1188) pair.1 pair.2) (finProdFinEquiv.symm_apply_apply (reader, glyph))
  have direction : chainDir readerData i = .left := by simp [chainDir, ref]
  have equal := moveLayers_at chainCount chainRef chainPick (chainDir readerData) 11 seed
    dispatchValid stores i (chainPick_ref i)
  rw [ref, direction] at equal
  exact equal.trans (congrArg (BinaryTemplates.move 11 .left) (seed_leaf reader glyph))

theorem prepared_tail (pc : Fin 4042) (side : Bool) :
    prepared.raw.decode preparedValid stores (prepared.root (.tail pc side)) = tailStmt data pc side :=
  (moveLayers_keep chainCount chainRef chainPick (chainDir readerData) 11 seed
    dispatchValid stores (.tail pc side) rfl).trans (seed_tail pc side)

theorem prepared_writerTail (site : Fin 270) :
    prepared.raw.decode preparedValid stores (prepared.root (.writerTail site)) =
      BinaryTemplates.move 11 .left
        (.goto fun _ v => BinaryTemplates.normal 270 1250 (data.next site default v)) := by
  let i : Fin chainCount := (Fin.natAdd (1733 * 1250) site).castAdd 1188
  have ref : chainRef (n := 4042) i = .writerTail site := by simp [i, chainRef]
  have direction : chainDir readerData i = .left := by simp [chainDir, ref]
  have equal := moveLayers_at chainCount chainRef chainPick (chainDir readerData) 11 seed
    dispatchValid stores i (chainPick_ref i)
  rw [ref, direction] at equal
  exact equal.trans (congrArg (BinaryTemplates.move 11 .left) (seed_writerTail site))

theorem prepared_mover (mover : Fin 1188) :
    prepared.raw.decode preparedValid stores (prepared.root (.mover mover)) =
      BinaryTemplates.move 11 (moverDir data mover) (tailStmt data (data.movePC mover) false) := by
  let i : Fin chainCount := Fin.natAdd (1733 * 1250 + 270) mover
  have ref : chainRef (n := 4042) i = .mover mover := by simp [i, chainRef]
  have direction : chainDir readerData i = moverDir data mover := by simp [chainDir, ref, moverDir]
  have equal := moveLayers_at chainCount chainRef chainPick (chainDir readerData) 11 seed
    dispatchValid stores i (chainPick_ref i)
  rw [ref, direction] at equal
  exact equal.trans (congrArg (BinaryTemplates.move 11 (moverDir data mover)) (seed_mover mover))

theorem front_root (i : Fin 1733) :
    front.state.raw.decode frontValid stores (front.root i List.Vector.nil) =
      BinaryTemplates.readAux 11 (fun suffix => prepared.raw.decode preparedValid stores
        (prepared.root (.readLeaf i (data.alphabet.symm (data.decode suffix))))) :=
  readers_root readerData 11 0 (by decide) prepared preparedValid i List.Vector.nil

theorem front_keep (ref : Ref 4042 270 1733 1188 1250) :
    front.state.raw.decode frontValid stores (front.state.root ref) =
      prepared.raw.decode preparedValid stores (prepared.root ref) :=
  readers_keep readerData 11 0 (by decide) prepared preparedValid ref

theorem written_reader (i : Fin 1733) :
    written.raw.decode writerValid stores (written.root (.reader i)) =
      BinaryTemplates.readAux 11 (fun bits => leaf i (data.decode bits)) := by
  change writerFront.state.raw.decode writerValid stores
    (writerFront.state.root (.reader i)) = _
  rw [writers_keep]
  change front.state.raw.decode frontValid stores (front.root i List.Vector.nil) = _
  rw [front_root]
  apply congrArg (BinaryTemplates.readAux 11)
  funext bits
  rw [prepared_leaf]
  rw [Equiv.apply_symm_apply]

theorem written_tail (pc : Fin 4042) (side : Bool) :
    written.raw.decode writerValid stores (written.root (.tail pc side)) = tailStmt data pc side := by
  change writerFront.state.raw.decode writerValid stores (writerFront.state.root _) = _
  rw [writers_keep]
  change front.state.raw.decode frontValid stores (front.state.root _) = _
  rw [front_keep, prepared_tail]

theorem written_mover (i : Fin 1188) :
    written.raw.decode writerValid stores (written.root (.mover i)) =
      BinaryTemplates.move 11 (moverDir data i) (tailStmt data (data.movePC i) false) := by
  change writerFront.state.raw.decode writerValid stores (writerFront.state.root _) = _
  rw [writers_keep]
  change front.state.raw.decode frontValid stores (front.state.root _) = _
  rw [front_keep, prepared_mover]

theorem written_writer (site : Fin 270) (glyph : Fin 1250) :
    written.raw.decode writerValid stores (written.root (.writer site glyph)) =
      BinaryTemplates.write (data.encode (data.alphabet glyph)).toList
        (BinaryTemplates.move 11 .left
          (.goto fun _ v => BinaryTemplates.normal 270 1250 (data.next site default v))) := by
  change writerFront.state.raw.decode writerValid stores (writerFront.root site _) = _
  rw [writers_root]
  apply congrArg (BinaryTemplates.write _)
  change front.state.raw.decode frontValid stores (front.state.root (.writerTail site)) = _
  rw [front_keep, prepared_writerTail]

end CatchUp.Machine.RestoreShare
