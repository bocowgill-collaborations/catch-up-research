import CatchUp.Machine.ReadShare.Graph

namespace CatchUp.Machine.ReadShare
open Turing ConjectureMachines Compilation TemplateGraph
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

def tagTest (v : Chess.Compilation.Templates.Store) : Bool := stores.symm v = 1

def leaf (i : Fin 1733) (glyph : Chess.Compilation.Templates.Symbol) :
    TM1.Stmt Bool (Fin 341542) Chess.Compilation.Templates.Store :=
  if i = 54 then
    .branch (fun _ v => tagTest v)
      (BinaryTemplates.move 11 .left (payloadStmt data (data.readPC 63) glyph))
      (BinaryTemplates.move 11 .left (payloadStmt data (data.readPC 54) glyph))
  else BinaryTemplates.move 11 .left (payloadStmt data (data.readPC (oldReader i)) glyph)

theorem original_leaf (i : Fin 1734) (glyph : Fin 1250) :
    prepared.raw.decode preparedValid stores (prepared.root (.readLeaf i glyph)) =
      BinaryTemplates.move 11 .left
        (payloadStmt data (data.readPC i) (data.alphabet glyph)) :=
  TemplateGraph.prepared_leaf data i glyph

theorem front_root (i : Fin 1733) :
    front.state.raw.decode frontValid stores (front.root i List.Vector.nil) =
      BinaryTemplates.readAux 11 (fun suffix => seed.raw.decode dispatchValid stores
        (seed.root (.readLeaf i (data.alphabet.symm (data.decode suffix))))) :=
  readers_root readerData 11 0 (by decide) seed dispatchValid i List.Vector.nil

theorem front_keep (ref : Ref 4042 270 1733 1188 1250) :
    front.state.raw.decode frontValid stores (front.state.root ref) =
      seed.raw.decode dispatchValid stores (seed.root ref) :=
  readers_keep readerData 11 0 (by decide) seed dispatchValid ref

theorem seed_leaf (i : Fin 1733) (glyph : Fin 1250) :
    seed.raw.decode dispatchValid stores (seed.root (.readLeaf i glyph)) =
      leaf i (data.alphabet glyph) := by
  change dispatchRaw.decode dispatchValid stores _ = _
  simp only [seed]
  split_ifs with hi
  · have h := Raw.decode_extend_new prepared.raw preparedValid 1250 dispatchNode stores glyph
    apply h.trans
    simp only [dispatchNode, buildNode, tableOf_read, original_leaf,
      leaf, hi, ↓reduceIte, tagTest]
  · exact (Raw.decode_extend_old prepared.raw preparedValid 1250 dispatchNode stores
      (prepared.root (.readLeaf (oldReader i) glyph))).trans (by
        simp only [leaf, hi, ↓reduceIte]
        exact original_leaf (oldReader i) glyph)

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
  rw [seed_leaf]
  rw [Equiv.apply_symm_apply]

theorem seed_tail (pc : Fin 4042) (side : Bool) :
    seed.raw.decode dispatchValid stores (seed.root (.tail pc side)) = tailStmt data pc side := by
  change dispatchRaw.decode dispatchValid stores
    ((prepared.root (.tail pc side)).castAdd 1250) = _
  exact (Raw.decode_extend_old prepared.raw preparedValid 1250 dispatchNode stores
    (prepared.root (.tail pc side))).trans (TemplateGraph.prepared_tail data pc side)

theorem seed_writerTail (site : Fin 270) :
    seed.raw.decode dispatchValid stores (seed.root (.writerTail site)) =
      BinaryTemplates.move 11 .left
        (.goto fun _ v => BinaryTemplates.normal 270 1250 (data.next site default v)) := by
  change dispatchRaw.decode dispatchValid stores
    ((prepared.root (.writerTail site)).castAdd 1250) = _
  exact (Raw.decode_extend_old prepared.raw preparedValid 1250 dispatchNode stores
    (prepared.root (.writerTail site))).trans (TemplateGraph.prepared_writerTail data site)

theorem seed_mover (i : Fin 1188) :
    seed.raw.decode dispatchValid stores (seed.root (.mover i)) =
      BinaryTemplates.move 11 (moverDir data i) (tailStmt data (data.movePC i) false) := by
  change dispatchRaw.decode dispatchValid stores
    ((prepared.root (.mover i)).castAdd 1250) = _
  exact (Raw.decode_extend_old prepared.raw preparedValid 1250 dispatchNode stores
    (prepared.root (.mover i))).trans (TemplateGraph.prepared_mover data i)

theorem written_tail (pc : Fin 4042) (side : Bool) :
    written.raw.decode writerValid stores (written.root (.tail pc side)) = tailStmt data pc side := by
  change writerFront.state.raw.decode writerValid stores (writerFront.state.root _) = _
  rw [writers_keep]
  change front.state.raw.decode frontValid stores (front.state.root _) = _
  rw [front_keep, seed_tail]

theorem written_mover (i : Fin 1188) :
    written.raw.decode writerValid stores (written.root (.mover i)) =
      BinaryTemplates.move 11 (moverDir data i) (tailStmt data (data.movePC i) false) := by
  change writerFront.state.raw.decode writerValid stores (writerFront.state.root _) = _
  rw [writers_keep]
  change front.state.raw.decode frontValid stores (front.state.root _) = _
  rw [front_keep, seed_mover]

theorem written_writer (site : Fin 270) (glyph : Fin 1250) :
    written.raw.decode writerValid stores (written.root (.writer site glyph)) =
      BinaryTemplates.write (data.encode (data.alphabet glyph)).toList
        (BinaryTemplates.move 11 .left
          (.goto fun _ v => BinaryTemplates.normal 270 1250 (data.next site default v))) := by
  change writerFront.state.raw.decode writerValid stores (writerFront.root site _) = _
  rw [writers_root]
  apply congrArg (BinaryTemplates.write _)
  change front.state.raw.decode frontValid stores (front.state.root (.writerTail site)) = _
  rw [front_keep, seed_writerTail]

end CatchUp.Machine.ReadShare
