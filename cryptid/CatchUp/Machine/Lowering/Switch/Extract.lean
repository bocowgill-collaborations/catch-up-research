import CatchUp.Machine.Lowering.Switch.ExtractBoundary

/-! The actual switch prefix-extraction contract. The retained head is a
bottom word, and all later input words and earlier caller frames are preserved. -/
namespace CatchUp.Machine.Lowering.Switch.Extract
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem extract_raw (head : Nat) (flag : Bit) (tail frames : List Bit) :
    ∃ steps, run switchBody steps
      (1395,H (wire (word head)++flag::0::wire tail) frames)=
      some (15384,H (flag::0::wire tail) (frames++word head)) := by
  obtain ⟨copied,hcopied⟩ := copy_head head (flag::0::wire tail) frames
  obtain ⟨marked,hmarked⟩ := mark_boundary flag (word head) tail (frames++word head)
  obtain ⟨shifted,hshifted⟩ := shift_prefix flag (word head) tail (frames++word head)
  exact ⟨_,run_chain switchBody (run_chain switchBody hcopied hmarked) hshifted⟩

theorem H_pad (raw frames : List Bit) : H (raw++[0,0]) frames=H raw frames := by
  change mirror (Tape.mk' (ListBlank.mk (0::wire frames))
      (ListBlank.mk ((0::0::raw)++[0,0])))=
    mirror (Tape.mk' (ListBlank.mk (0::wire frames)) (ListBlank.mk (0::0::raw)))
  rw [blank_pad]

theorem H_zero (frames : List Bit) : H [0,0] frames=H [] frames := H_pad [] frames

theorem H_wire (data frames : List Bit) : H (wire data) frames=banks data frames := by
  simp [H,banks,home,view,mirror,Tape.mk₂,Tape.mk']

/-- The actual extraction routine moves the arbitrary retained bottom word to
the caller-frame bank. Empty input uses flag0; nonempty input uses flag1. -/
theorem extract_prefix (head : Nat) (data frames : List Nat) :
    ∃ steps, run switchBody steps (1395,natBanks (head::data) frames)=
      some (15384,natBanks data (frames++[head])) := by
  cases data with
  | nil =>
    obtain ⟨steps,h⟩ := extract_raw head 0 [] (encode frames)
    simp only [wire_nil] at h
    rw [H_pad,H_zero] at h
    exact ⟨steps,by simpa [natBanks,←H_wire,encode,List.flatMap_append] using h⟩
  | cons n data =>
    obtain ⟨steps,h⟩ := extract_raw head 1 (List.replicate n 1++0::encode data) (encode frames)
    exact ⟨steps,by simpa [natBanks,←H_wire,encode,word,wire_append,
      List.flatMap_append,List.append_assoc] using h⟩

theorem exit_cells (a : Bit) :
    switchBody.cell 15384 a=some (a,.right,15385) ∧
    switchBody.cell 15385 a=some (a,.left,-1) := by
  fin_cases a <;> exact ⟨rfl,rfl⟩

theorem exit_correct (T : Tape Bit) : run switchBody 2 (15384,T)=some (-1,T) := by
  have first (a : Bit) := (exit_cells a).1
  have last (a : Bit) := (exit_cells a).2
  simp [run,Switch.step,first,last]

theorem extract_return (head : Nat) (data frames : List Nat) :
    ∃ steps, run switchBody steps (1395,natBanks (head::data) frames)=
      some (-1,natBanks data (frames++[head])) := by
  obtain ⟨steps,h⟩ := extract_prefix head data frames
  exact ⟨_,run_chain switchBody h (exit_correct (natBanks data (frames++[head])))⟩

/-- The restored original input and retained head reach the real external
return port, with the original caller frames followed by exactly that head. -/
theorem restore_then_extract (head : Nat) (data frames : List Nat) :
    ∃ steps, run switchBody steps
      (6742,natBanks [head] (frames++savedFrames data))=
      some (-1,natBanks data (frames++[head])) := by
  obtain ⟨restored,hr⟩ := restore_retained_head data frames head
  obtain ⟨extracted,he⟩ := extract_return head data frames
  exact ⟨_,run_chain switchBody hr he⟩

theorem binary_extract (head : Nat) (data frames : List Nat) :
    ∃ steps, FlatInit.runFrom (binary switchBody) steps
      ⟨⟨1395,by decide +kernel⟩,natBanks (head::data) frames⟩=
      some ⟨⟨switchBody.size,by omega⟩,natBanks data (frames++[head])⟩ := by
  change ∃ steps, FlatInit.runFrom (binary switchBody) steps
    (embed switchBody (1395,natBanks (head::data) frames))=
    some (embed switchBody (-1,natBanks data (frames++[head])))
  obtain ⟨steps,h⟩ := extract_return head data frames
  refine ⟨steps,?_⟩
  rw [binary_run,h]
  rfl

theorem binary_restore_extract (head : Nat) (data frames : List Nat) :
    ∃ steps, FlatInit.runFrom (binary switchBody) steps
      ⟨⟨6742,by decide +kernel⟩,natBanks [head] (frames++savedFrames data)⟩=
      some ⟨⟨switchBody.size,by omega⟩,natBanks data (frames++[head])⟩ := by
  change ∃ steps, FlatInit.runFrom (binary switchBody) steps
    (embed switchBody (6742,natBanks [head] (frames++savedFrames data)))=
    some (embed switchBody (-1,natBanks data (frames++[head])))
  obtain ⟨steps,h⟩ := restore_then_extract head data frames
  refine ⟨steps,?_⟩
  rw [binary_run,h]
  rfl

end CatchUp.Machine.Lowering.Switch.Extract
