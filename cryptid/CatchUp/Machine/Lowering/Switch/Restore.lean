import CatchUp.Machine.Lowering.Switch.Run

/-! The unbounded tagged-input restore loop in the actual switchBody table.
State 6742 is its loop boundary; state 1395 begins bottom-word extraction. -/
namespace CatchUp.Machine.Lowering.Switch
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem restore_word_cell (q : Fin 3851) (a : Bit) :
    switchBody.cell (1504+q.val) a=(Segment.word 3850 1503).cell 1504 q.val a := by
  exact cell_in switchBody (switchBody.segments.take 127) (switchBody.segments.drop 128)
    (.word 3850 1503) (by rfl) q.val q.isLt a

theorem restore_transfer_prefix (u v : List Bit) (n : Nat) :
    run switchBody (transferCost u v n) (3641,home true (u++word n) v)=
      some (5354,home true u (v++word n)) := by
  have h := run_present Words.machine switchBody 1504
    (word_present switchBody 1504 1503 restore_word_cell) _ _ _ (word_transfer true u v n)
  exact h

theorem closer_cell (q : Fin 460) (a : Bit) :
    switchBody.cell (6282+q.val) a=(Segment.bit 6281 6280 (some 6280)).cell 6282 q.val a := by
  exact cell_in switchBody (switchBody.segments.take 137) (switchBody.segments.drop 138)
    (.bit 6281 6280 (some 6280)) (by rfl) q.val q.isLt a

theorem payload_cell (q : Fin 460) (a : Bit) :
    switchBody.cell (5820+q.val) a=(Segment.bit 5818 5819 (some 5817)).cell 5820 q.val a := by
  exact cell_in switchBody (switchBody.segments.take 134) (switchBody.segments.drop 135)
    (.bit 5818 5819 (some 5817)) (by rfl) q.val q.isLt a

theorem opener_cell (q : Fin 460) (a : Bit) :
    switchBody.cell (5357+q.val) a=(Segment.bit 5356 5355 (some 5355)).cell 5357 q.val a := by
  exact cell_in switchBody (switchBody.segments.take 130) (switchBody.segments.drop 131)
    (.bit 5356 5355 (some 5355)) (by rfl) q.val q.isLt a

theorem restore_rows (a : Bit) :
    switchBody.cell 6742 a=some (a,.right,6743) ∧
    switchBody.cell 6743 a=some (a,.left,6492) ∧
    switchBody.cell 6692 a=some (a,.right,6281) ∧
    switchBody.cell 6281 a=some (a,.left,6030) ∧
    switchBody.cell 6230 a=some (a,.right,5818) ∧
    switchBody.cell 5818 a=some (a,.left,1395) ∧
    switchBody.cell 6235 a=some (a,.right,5819) ∧
    switchBody.cell 5819 a=some (a,.left,5567) ∧
    switchBody.cell 5767 a=some (a,.right,5356) ∧
    switchBody.cell 5356 a=some (a,.left,3641) ∧
    switchBody.cell 5354 a=some (a,.right,1503) ∧
    switchBody.cell 1503 a=some (a,.left,6742) := by
  fin_cases a <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem pop_copy (offset z o : Nat) (empty : Option Nat)
    (hc : ∀ (q : Fin 460) (a : Bit), switchBody.cell (offset+q.val) a=
      (Segment.bit z o empty).cell offset q.val a) (u v : List Bit) (b : Bit) :
    run switchBody (4*u.length+12)
      (Int.ofNat (offset+210),home true (u++[b]) v)=
      some (Int.ofNat (offset+(410+5*b.val)),home true u v) := by
  have h := run_present Separate.machine switchBody offset
    (bit_present switchBody offset z o empty hc) _ _ _ (pop_correct true u v b 0 0)
  fin_cases b <;> exact h

theorem loop_entry (T : Tape Bit) : run switchBody 2 (6742,T)=some (6492,T) :=
  bounce switchBody 6742 6743 6492 (fun a ↦ (restore_rows a).1)
    (fun a ↦ (restore_rows a).2.1) T

theorem closer_exit (T : Tape Bit) : run switchBody 2 (6692,T)=some (6030,T) :=
  bounce switchBody 6692 6281 6030 (fun a ↦ (restore_rows a).2.2.1)
    (fun a ↦ (restore_rows a).2.2.2.1) T

theorem sentinel_exit (T : Tape Bit) : run switchBody 2 (6230,T)=some (1395,T) :=
  bounce switchBody 6230 5818 1395 (fun a ↦ (restore_rows a).2.2.2.2.1)
    (fun a ↦ (restore_rows a).2.2.2.2.2.1) T

theorem tag_one_exit (T : Tape Bit) : run switchBody 2 (6235,T)=some (5567,T) :=
  bounce switchBody 6235 5819 5567 (fun a ↦ (restore_rows a).2.2.2.2.2.2.1)
    (fun a ↦ (restore_rows a).2.2.2.2.2.2.2.1) T

theorem opener_exit (T : Tape Bit) : run switchBody 2 (5767,T)=some (3641,T) :=
  bounce switchBody 5767 5356 3641 (fun a ↦ (restore_rows a).2.2.2.2.2.2.2.2.1)
    (fun a ↦ (restore_rows a).2.2.2.2.2.2.2.2.2.1) T

theorem word_exit (T : Tape Bit) : run switchBody 2 (5354,T)=some (6742,T) :=
  bounce switchBody 5354 1503 6742 (fun a ↦ (restore_rows a).2.2.2.2.2.2.2.2.2.2.1)
    (fun a ↦ (restore_rows a).2.2.2.2.2.2.2.2.2.2.2) T

/-- One tagged word is consumed, including all three tag bits. Both surrounding
bit banks are arbitrary; in particular the earlier frame payload is preserved. -/
theorem restore_tagged_word (pre data : List Bit) (n : Nat) :
    ∃ steps, run switchBody steps (6742,banks data (pre++word n++word 1))=
      some (6742,banks (data++word n) pre) := by
  let u := pre++word n
  have close : run switchBody (4*(u++[0,1]).length+12)
      (6492,home true (u++[0,1,0]) data)=some (6692,home true (u++[0,1]) data) := by
    have h := pop_copy 6282 6281 6280 (some 6280) closer_cell (u++[0,1]) data 0
    rw [show (u++[0,1])++[0]=u++[0,1,0] by simp only [List.append_assoc];rfl] at h
    exact h
  have payload : run switchBody (4*(u++[0]).length+12)
      (6030,home true (u++[0,1]) data)=some (6235,home true (u++[0]) data) := by
    have h := pop_copy 5820 5818 5819 (some 5817) payload_cell (u++[0]) data 1
    rw [show (u++[0])++[1]=u++[0,1] by simp only [List.append_assoc];rfl] at h
    exact h
  have opening : run switchBody (4*u.length+12)
      (5567,home true (u++[0]) data)=some (5767,home true u data) :=
    pop_copy 5357 5356 5355 (some 5355) opener_cell u data 0
  have path := run_chain switchBody
    (run_chain switchBody
      (run_chain switchBody
        (run_chain switchBody
          (run_chain switchBody
            (run_chain switchBody
              (run_chain switchBody (loop_entry (home true (u++[0,1,0]) data)) close)
              (closer_exit (home true (u++[0,1]) data))) payload)
          (tag_one_exit (home true (u++[0]) data))) opening)
      (opener_exit (home true u data))) (restore_transfer_prefix pre data n)
  exact ⟨_,run_chain switchBody path (word_exit (home true pre (data++word n)))⟩

/-- The two-bit sentinel stops restoration, without consuming any bit of the
arbitrary earlier frame bank. The preserved data bank may also be arbitrary. -/
theorem restore_sentinel (pre data : List Bit) :
    ∃ steps, run switchBody steps (6742,banks data (pre++word 0))=
      some (1395,banks data pre) := by
  have close : run switchBody (4*(pre++[0]).length+12)
      (6492,home true (pre++[0,0]) data)=some (6692,home true (pre++[0]) data) := by
    have h := pop_copy 6282 6281 6280 (some 6280) closer_cell (pre++[0]) data 0
    rw [show (pre++[0])++[0]=pre++[0,0] by simp only [List.append_assoc];rfl] at h
    exact h
  have payload : run switchBody (4*pre.length+12)
      (6030,home true (pre++[0]) data)=some (6230,home true pre data) :=
    pop_copy 5820 5818 5819 (some 5817) payload_cell pre data 0
  exact ⟨_,run_chain switchBody
    (run_chain switchBody
      (run_chain switchBody
        (run_chain switchBody (loop_entry (home true (pre++[0,0]) data)) close)
        (closer_exit (home true (pre++[0]) data))) payload)
    (sentinel_exit (home true pre data))⟩

/-- The exact saved-input format used by the actual lowered cons instruction. -/
def savedFrames (data : List Nat) : List Nat :=
  [0]++data.reverse.flatMap (fun n ↦ [n,1])

def savedPayload (data : List Nat) : List Bit := encode (savedFrames data)

theorem savedFrames_cons (n : Nat) (data : List Nat) :
    savedFrames (n::data)=savedFrames data++[n,1] := by
  simp [savedFrames,List.reverse_cons,List.flatMap_append]

theorem savedPayload_cons (n : Nat) (data : List Nat) :
    savedPayload (n::data)=savedPayload data++word n++word 1 := by
  simp [savedPayload,savedFrames_cons,encode,List.flatMap_append,List.append_assoc]

/-- The actual restore loop terminates for every saved input length, restores
all words in their original order, and preserves both arbitrary surrounding
bit banks. In particular it does not pop a pending caller continuation. -/
theorem restore_input (original : List Nat) (data frames : List Bit) :
    ∃ steps, run switchBody steps (6742,banks data (frames++savedPayload original))=
      some (1395,banks (data++encode original) frames) := by
  induction original generalizing data with
  | nil => simpa [savedPayload,savedFrames,encode] using restore_sentinel frames data
  | cons n original ih =>
    obtain ⟨first,hfirst⟩ := restore_tagged_word (frames++savedPayload original) data n
    obtain ⟨rest,hrest⟩ := ih (data++word n)
    have combined := run_chain switchBody hfirst hrest
    refine ⟨first+rest,?_⟩
    simpa only [savedPayload_cons,encode,List.flatMap_cons,List.append_assoc] using combined

/-- Specialized to cons's natural-number data and frame banks: the retained
head remains below the restored input. Bottom-word extraction starts next. -/
theorem restore_retained_head (original frames : List Nat) (retained : Nat) :
    ∃ steps, run switchBody steps
      (6742,natBanks [retained] (frames++savedFrames original))=
      some (1395,natBanks (retained::original) frames) := by
  simpa only [natBanks,savedPayload,encode,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,List.append_assoc] using
    restore_input original (encode [retained]) (encode frames)

end CatchUp.Machine.Lowering.Switch
