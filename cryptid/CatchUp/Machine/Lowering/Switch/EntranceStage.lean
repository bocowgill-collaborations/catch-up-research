import CatchUp.Machine.Lowering.Switch.EntranceTransfer
import CatchUp.Machine.Lowering.Switch.EntranceClear

namespace CatchUp.Machine.Lowering.Switch.Entrance
open Turing ConjectureMachines Compilation Separate Words Extract
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem capture_present (q out : Fin 3851) (a w : Bit) (d : Dir) (hq : q.val≠1926)
    (h : Words.machine.transition q a=some (w,d,out)) :
    switchBody.cell (10606+q.val) a=some (w,d,Int.ofNat (10606+out.val)) := by
  rw [capture_cell]
  simp only [Segment.cell,hq,q.isLt,↓reduceIte,↓reduceDIte,h,Option.map_some]

/-- Reuses the old transfer proof only up to its first left return1926. -/
theorem capture_prefix (u v : List Bit) (n : Nat) :
    run switchBody (transferCost u v n) (10809,home false (u++word n) v)=
      some (12532,home false u (v++word n)) := by
  have h := left_prefix_present switchBody 10606 capture_present _ _ _
    (word_transfer false u v n)
  exact h

theorem capture_exit (T : Tape Bit) : run switchBody 2 (12532,T)=some (10596,T) :=
  bounce switchBody 12532 10605 10596 (fun a ↦ (bridge_rows a).1)
    (fun a ↦ (bridge_rows a).2.1) T

theorem headback_prefix (u v : List Bit) (n : Nat) :
    run switchBody (transferCost u v n) (8882,home true (u++word n) v)=
      some (10595,home true u (v++word n)) := by
  have h := run_present Words.machine switchBody 6745
    (word_present switchBody 6745 6744 headback_cell) _ _ _ (word_transfer true u v n)
  exact h

theorem headback_exit (T : Tape Bit) : run switchBody 2 (10595,T)=some (6742,T) :=
  bounce switchBody 10595 6744 6742 (fun a ↦ (bridge_rows a).2.2.1)
    (fun a ↦ (bridge_rows a).2.2.2.1) T

/-- Both zero bits of the default word are created by actual shared bit pushes. -/
theorem default_first (frames data : List Bit) :
    run switchBody (4*frames.length+8) (14969,banks data frames)=
      some (15329,banks data (frames++[0])) := by
  have h := run_present Separate.machine switchBody 14919
    (bit_present switchBody 14919 14918 14918 none default_first_cell) _ _ _
    (push_correct true frames data 0 0)
  exact h

theorem default_first_exit (T : Tape Bit) : run switchBody 2 (15329,T)=some (14508,T) :=
  bounce switchBody 15329 14918 14508 (fun a ↦ (bridge_rows a).2.2.2.2.1)
    (fun a ↦ (bridge_rows a).2.2.2.2.2.1) T

theorem default_last (frames data : List Bit) :
    run switchBody (4*frames.length+8) (14508,banks data frames)=
      some (14868,banks data (frames++[0])) := by
  have h := run_present Separate.machine switchBody 14458
    (bit_present switchBody 14458 14457 14457 none default_last_cell) _ _ _
    (push_correct true frames data 0 0)
  exact h

theorem default_last_exit (T : Tape Bit) : run switchBody 2 (14868,T)=some (10596,T) :=
  bounce switchBody 14868 14457 10596 (fun a ↦ (bridge_rows a).2.2.2.2.2.2.1)
    (fun a ↦ (bridge_rows a).2.2.2.2.2.2.2) T

theorem default_word (data frames : List Bit) :
    ∃ steps, run switchBody steps (14969,banks data frames)=
      some (10596,banks data (frames++word 0)) := by
  have path := run_chain switchBody
    (run_chain switchBody
      (run_chain switchBody (default_first frames data)
        (default_first_exit (banks data (frames++[0]))))
      (default_last (frames++[0]) data))
    (default_last_exit (banks data ((frames++[0])++[0])))
  rw [show (frames++[0])++[0]=frames++word 0 by
    simp only [word,List.replicate_zero,List.nil_append,List.append_assoc];rfl] at path
  exact ⟨_,path⟩

/-- Stage a retained word, erasing every other bit on the result bank. The
opposite bank is arbitrary, including any saved input and earlier frames. -/
theorem clear_then_headback (data frames : List Bit) (head : Nat) :
    ∃ steps, run switchBody steps (10596,banks data (frames++word head))=
      some (6742,banks (word head) frames) := by
  obtain ⟨cleared,hc⟩ := clear_correct data (frames++word head)
  have hb := headback_prefix frames [] head
  simp only [List.nil_append] at hb
  exact ⟨_,run_chain switchBody (run_chain switchBody hc hb)
    (headback_exit (banks (word head) frames))⟩

theorem stage_nonempty (data frames : List Bit) (head : Nat) :
    ∃ steps, run switchBody steps (10809,banks (data++word head) frames)=
      some (6742,banks (word head) frames) := by
  have first := run_chain switchBody (capture_prefix data frames head)
    (capture_exit (banks data (frames++word head)))
  obtain ⟨last,hl⟩ := clear_then_headback data frames head
  exact ⟨_,run_chain switchBody first hl⟩

theorem stage_empty (frames : List Bit) :
    ∃ steps, run switchBody steps (14969,banks [] frames)=
      some (6742,banks (word 0) frames) := by
  obtain ⟨first,hf⟩ := default_word [] frames
  obtain ⟨last,hl⟩ := clear_then_headback [] frames 0
  exact ⟨_,run_chain switchBody hf hl⟩

end CatchUp.Machine.Lowering.Switch.Entrance
