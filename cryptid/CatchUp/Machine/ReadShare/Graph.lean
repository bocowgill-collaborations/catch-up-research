import Cryptids.Chess.Compilation.Image

/-! Share the binary reader at actual primitive PCs285 and302. The old scratch
register is dead at these two loads. All other source/codec/store data are unchanged. -/
namespace CatchUp.Machine.ReadShare
open Turing ConjectureMachines Compilation TemplateGraph

set_option backward.isDefEq.respectTransparency false

abbrev data := Chess.Compilation.Image.data
abbrev stores := Chess.Compilation.Templates.stores

def oldReader (i : Fin 1733) : Fin 1734 :=
  ⟨if i.val < 63 then i.val else i.val + 1, by split <;> omega⟩

def newReader (i : Fin 1734) : Fin 1733 :=
  ⟨if i.val < 63 then i.val else i.val - 1, by split <;> omega⟩

theorem old_new (i : Fin 1734) (ne : i ≠ 63) : oldReader (newReader i) = i := by
  apply Fin.ext
  have hn : i.val ≠ 63 := fun h => ne (Fin.ext h)
  simp only [oldReader, newReader]
  split_ifs <;> omega

/-- Only decoder/alphabet/store fields of this auxiliary data are used by `readers`.
Source entry classification continues to use the original proved data. -/
abbrev readerData : Data Chess.Compilation.Templates.Symbol Chess.Compilation.Templates.Store
    4042 270 1250 5 1733 1188 11 :=
  { data with readPC := fun i => data.readPC (oldReader i), classify := fun _ => .plain }

abbrev prepared := TemplateGraph.prepared data
abbrev preparedValid := TemplateGraph.prepared_valid data

def dispatchNode (glyph : Fin 1250) : BoolGraph.Node prepared.raw.count 5 341542 :=
  .branch (tableOf fun _ value => value = 1)
    (prepared.root (.readLeaf 63 glyph)) (prepared.root (.readLeaf 54 glyph))

def dispatchRaw := prepared.raw.extend 1250 dispatchNode

theorem dispatchValid : dispatchRaw.Valid := prepared.raw.extend_valid preparedValid _ _

/-- Full old restoration/payload families stay paid. One extra branch per glyph
selects the original payload from the caller tag held in the existing store. -/
def seed : Bundle 4042 270 1733 1188 1250 5 where
  raw := dispatchRaw
  root ref := match ref with
    | .readLeaf i glyph =>
      if i = 54 then Fin.natAdd prepared.raw.count glyph
      else (prepared.root (.readLeaf (oldReader i) glyph)).castAdd 1250
    | .tail pc side => (prepared.root (.tail pc side)).castAdd 1250
    | .writerTail site => (prepared.root (.writerTail site)).castAdd 1250
    | .reader _ => (prepared.root (.tail 0 false)).castAdd 1250
    | .writer _ _ => (prepared.root (.tail 0 false)).castAdd 1250
    | .mover i => (prepared.root (.mover i)).castAdd 1250

abbrev front := readers readerData 11 0 (by decide) seed
abbrev frontValid := readers_valid readerData 11 0 (by decide) seed dispatchValid

def readState : Bundle 4042 270 1733 1188 1250 5 where
  raw := front.state.raw
  root ref := match ref with
    | .reader i => front.root i List.Vector.nil
    | _ => front.state.root ref

abbrev writerFront := writers 11 readState
abbrev writerValid := writers_valid 11 readState frontValid

def written : Bundle 4042 270 1733 1188 1250 5 where
  raw := writerFront.state.raw
  root ref := match ref with
    | .writer site glyph => writerFront.root site (data.encode (data.alphabet glyph))
    | _ => writerFront.state.root ref

/-- Both tag assignments are finite load nodes; no new store values or tape cells. -/
def callerNode (tag : Fin 2) : BoolGraph.Node written.raw.count 5 341542 :=
  .load (tableOf fun _ _ => if tag.val = 1 then 1 else 0) (written.root (.reader 54))

abbrev raw := written.raw.extend 2 callerNode

theorem rawValid : raw.Valid := written.raw.extend_valid writerValid _ _

def entry (label : Fin 341542) : Fin raw.count :=
  match (BinaryTemplates.labelEquiv 4042 270 1250).symm label with
  | .inl pc => match data.classify pc with
    | .plain => (written.root (.tail pc false)).castAdd 2
    | .read i =>
      if i = 54 then Fin.natAdd written.raw.count 0
      else if i = 63 then Fin.natAdd written.raw.count 1
      else (written.root (.reader (newReader i))).castAdd 2
    | .move i => (written.root (.mover i)).castAdd 2
  | .inr (site, glyph) => (written.root (.writer site glyph)).castAdd 2

def getter : LazyGraph.Graph raw.count 5 341542 := ⟨raw.node, entry, rawValid⟩

abbrev post := LazyGraph.machine getter

theorem node_count : raw.count = 38888757 := by
  change writerFront.state.raw.count + 2 = _
  rw [writers_count]
  change front.state.raw.count + writerCost 270 11 + 2 = _
  rw [readers_count]
  change prepared.raw.count + 1250 + readerCost 1733 11 0 + writerCost 270 11 + 2 = _
  simp only [TemplateGraph.prepared, moveLayers_count, initialMoves,
    payloads, Bundle.add, Raw.extend, base]
  decide +kernel

end CatchUp.Machine.ReadShare
