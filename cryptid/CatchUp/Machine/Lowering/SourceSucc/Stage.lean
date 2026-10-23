import CatchUp.Machine.Lowering.SourceSucc.Clear

namespace CatchUp.Machine.Lowering.SourceSucc
open Turing ConjectureMachines Compilation Separate Words Switch Switch.Entrance
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem capture_present (q out : Fin 3851) (a w : Bit) (d : Dir) (hq : q.val≠1926)
    (h : Words.machine.transition q a=some (w,d,out)) :
    sourceSuccBody.cell (3862+q.val) a=some (w,d,Int.ofNat (3862+out.val)) := by
  rw [capture_cell]
  simp only [Segment.cell,hq,q.isLt,↓reduceIte,↓reduceDIte,h,Option.map_some]

/-- The existing first-left-return proof applies to the actual capture copy. -/
theorem capture_prefix (data frames : List Bit) (n : Nat) :
    Switch.run sourceSuccBody (transferCost data frames n)
      (4065,home false (data++word n) frames)=
      some (5788,home false data (frames++word n)) := by
  have result := left_prefix_present sourceSuccBody 3862 capture_present _ _ _
    (word_transfer false data frames n)
  exact result

theorem capture_exit (T : Tape Bit) :
    Switch.run sourceSuccBody 2 (5788,T)=some (3852,T) :=
  bounce sourceSuccBody 5788 3861 3852 (fun a ↦ (bridge_rows a).1)
    (fun a ↦ (bridge_rows a).2.1) T

theorem headback_prefix (frames data : List Bit) (n : Nat) :
    Switch.run sourceSuccBody (transferCost frames data n)
      (2138,home true (frames++word n) data)=
      some (3851,home true frames (data++word n)) := by
  have result := run_present Words.machine sourceSuccBody 1
    (word_present sourceSuccBody 1 0 headback_cell) _ _ _ (word_transfer true frames data n)
  exact result

theorem headback_exit (T : Tape Bit) :
    Switch.run sourceSuccBody 2 (3851,T)=some (8640,T) :=
  bounce sourceSuccBody 3851 0 8640 (fun a ↦ (bridge_rows a).2.2.1)
    (fun a ↦ (bridge_rows a).2.2.2.1) T

theorem default_first (data frames : List Bit) :
    Switch.run sourceSuccBody (4*data.length+8) (8215,banks data frames)=
      some (8575,banks (data++[0]) frames) := by
  have result := run_present Separate.machine sourceSuccBody 8175
    (bit_present sourceSuccBody 8175 8174 8174 none default_first_cell) _ _ _
    (push_correct false data frames 0 0)
  simp only [home_swap] at result
  exact result

theorem default_first_exit (T : Tape Bit) :
    Switch.run sourceSuccBody 2 (8575,T)=some (7754,T) :=
  bounce sourceSuccBody 8575 8174 7754 (fun a ↦ (bridge_rows a).2.2.2.2.1)
    (fun a ↦ (bridge_rows a).2.2.2.2.2.1) T

theorem default_last (data frames : List Bit) :
    Switch.run sourceSuccBody (4*data.length+8) (7754,banks data frames)=
      some (8114,banks (data++[0]) frames) := by
  have result := run_present Separate.machine sourceSuccBody 7714
    (bit_present sourceSuccBody 7714 7713 7713 none default_last_cell) _ _ _
    (push_correct false data frames 0 0)
  simp only [home_swap] at result
  exact result

theorem default_last_exit (T : Tape Bit) :
    Switch.run sourceSuccBody 2 (8114,T)=some (8640,T) :=
  bounce sourceSuccBody 8114 7713 8640 (fun a ↦ (bridge_rows a).2.2.2.2.2.2.1)
    (fun a ↦ (bridge_rows a).2.2.2.2.2.2.2.1) T

/-- Both delimiter bits of default zero are actually pushed onto data. -/
theorem default_word (data frames : List Bit) :
    ∃ steps, Switch.run sourceSuccBody steps (8215,banks data frames)=
      some (8640,banks (data++word 0) frames) := by
  have path := run_chain sourceSuccBody
    (run_chain sourceSuccBody
      (run_chain sourceSuccBody (default_first data frames)
        (default_first_exit (banks (data++[0]) frames)))
      (default_last (data++[0]) frames))
    (default_last_exit (banks ((data++[0])++[0]) frames))
  rw [show (data++[0])++[0]=data++word 0 by
    simp only [word,List.replicate_zero,List.nil_append,List.append_assoc];rfl] at path
  exact ⟨_,path⟩

theorem clear_then_headback (data frames : List Bit) (n : Nat) :
    ∃ steps, Switch.run sourceSuccBody steps (3852,banks data (frames++word n))=
      some (8640,banks (word n) frames) := by
  obtain ⟨cleared,hc⟩ := clear_correct data (frames++word n)
  have hb := headback_prefix frames [] n
  simp only [List.nil_append] at hb
  exact ⟨_,run_chain sourceSuccBody (run_chain sourceSuccBody hc hb)
    (headback_exit (banks (word n) frames))⟩

/-- Earlier bits are physically erased after the top word has been captured. -/
theorem stage_nonempty (data frames : List Bit) (n : Nat) :
    ∃ steps, Switch.run sourceSuccBody steps (4065,banks (data++word n) frames)=
      some (8640,banks (word n) frames) := by
  have captured := capture_prefix data frames n
  simp only [home_swap] at captured
  have first := run_chain sourceSuccBody captured
    (capture_exit (banks data (frames++word n)))
  obtain ⟨last,hl⟩ := clear_then_headback data frames n
  exact ⟨_,run_chain sourceSuccBody first hl⟩

theorem return_exit (T : Tape Bit) :
    Switch.run sourceSuccBody 2 (8640,T)=some (-1,T) := by
  have first (a : Bit) := (bridge_rows a).2.2.2.2.2.2.2.2.1
  have last (a : Bit) := (bridge_rows a).2.2.2.2.2.2.2.2.2
  simp [Switch.run,Switch.step,first,last]

end CatchUp.Machine.Lowering.SourceSucc
