import CatchUp.Machine.ReadShare.Cryptid

/-! The shared reader now restores the head before dispatch, so its two caller
families also share their identical eleven-left-step restoration per glyph. -/
namespace CatchUp.Machine.RestoreShare
open Turing ConjectureMachines Compilation TemplateGraph

set_option backward.isDefEq.respectTransparency false

abbrev data := Chess.Compilation.Image.data
abbrev stores := Chess.Compilation.Templates.stores

abbrev oldReader := ReadShare.oldReader
abbrev newReader := ReadShare.newReader
abbrev readerData := ReadShare.readerData

/-- Both old payloads are kept; no head-restoration moves have been added yet. -/
abbrev payloadBase := initialMoves data (payloads data (base data))
abbrev payloadValid := payloads_valid data (base data) (base_valid data)

def dispatchNode (glyph : Fin 1250) : BoolGraph.Node payloadBase.raw.count 5 341542 :=
  .branch (tableOf fun _ value => value = 1)
    (payloadBase.root (.readLeaf 63 glyph)) (payloadBase.root (.readLeaf 54 glyph))

def dispatchRaw := payloadBase.raw.extend 1250 dispatchNode

theorem dispatchValid : dispatchRaw.Valid := payloadBase.raw.extend_valid payloadValid _ _

/-- Dispatch after restoration: keep both original load payloads but select
only one restoration family for the two callers. -/
def seed : Bundle 4042 270 1733 1188 1250 5 where
  raw := dispatchRaw
  root ref := match ref with
    | .readLeaf i glyph =>
      if i = 54 then Fin.natAdd payloadBase.raw.count glyph
      else (payloadBase.root (.readLeaf (oldReader i) glyph)).castAdd 1250
    | .tail pc side => (payloadBase.root (.tail pc side)).castAdd 1250
    | .writerTail site => (payloadBase.root (.writerTail site)).castAdd 1250
    | .reader _ => (payloadBase.root (.tail 0 false)).castAdd 1250
    | .writer _ _ => (payloadBase.root (.tail 0 false)).castAdd 1250
    | .mover i => (payloadBase.root (.mover i)).castAdd 1250

abbrev chainCount := 1733 * 1250 + 270 + 1188
abbrev prepared := moveLayers chainCount chainRef chainPick (chainDir readerData) 11 seed
abbrev preparedValid := moveLayers_valid chainCount chainRef chainPick
  (chainDir readerData) 11 seed dispatchValid

abbrev front := readers readerData 11 0 (by decide) prepared
abbrev frontValid := readers_valid readerData 11 0 (by decide) prepared preparedValid

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

theorem node_count : raw.count = 38875007 := by
  change writerFront.state.raw.count + 2 = _
  rw [writers_count]
  change front.state.raw.count + writerCost 270 11 + 2 = _
  rw [readers_count]
  rw [moveLayers_count]
  change payloadBase.raw.count + 1250 + 11 * chainCount +
    readerCost 1733 11 0 + writerCost 270 11 + 2 = _
  simp only [payloadBase, initialMoves, payloads, Bundle.add, Raw.extend, base]
  decide +kernel

end CatchUp.Machine.RestoreShare
