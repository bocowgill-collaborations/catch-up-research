import CatchUp.Machine.Lowering.Switch.Run

namespace CatchUp.Machine.Lowering.Finish
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency false

theorem word_cell (q : Fin 3851) (a : Bit) :
    finishBody.cell (1+q.val) a=(Segment.word 3850 0).cell 1 q.val a := by
  exact Switch.cell_in finishBody (finishBody.segments.take 1)
    (finishBody.segments.drop 2) (.word 3850 0) (by rfl) q.val q.isLt a

/-- The already-proved arbitrary-width transfer occurs in the actual body.
Both caller frames and existing data are arbitrary bit prefixes. -/
theorem transfer_prefix (frames data : List Bit) (n : Nat) :
    Switch.run finishBody (transferCost frames data n)
      (2138,home true (frames++word n) data)=
      some (3851,home true frames (data++word n)) := by
  have result := Switch.run_present Words.machine finishBody 1
    (Switch.word_present finishBody 1 0 word_cell) _ _ _ (word_transfer true frames data n)
  exact result

theorem return_rows (a : Bit) :
    finishBody.cell 3851 a=some (a,.right,0) ∧
    finishBody.cell 0 a=some (a,.left,3852) ∧
    finishBody.cell 3852 a=some (a,.right,3853) ∧
    finishBody.cell 3853 a=some (a,.left,-1) := by
  fin_cases a <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem return_bridge (T : Tape Bit) :
    Switch.run finishBody 2 (3851,T)=some (3852,T) :=
  Switch.bounce finishBody 3851 0 3852 (fun a ↦ (return_rows a).1)
    (fun a ↦ (return_rows a).2.1) T

theorem return_exit (T : Tape Bit) :
    Switch.run finishBody 2 (3852,T)=some (-1,T) := by
  have first (a : Bit) := (return_rows a).2.2.1
  have last (a : Bit) := (return_rows a).2.2.2
  simp [Switch.run,Switch.step,first,last]

/-- Exact whole-tape contract of the frozen finishBody. The required retained
word moves above arbitrary data; every earlier caller bit is preserved. -/
theorem finish_bits (data frames : List Bit) (n : Nat) :
    Switch.run finishBody (transferCost frames data n+4)
      (Int.ofNat finishBody.entry,banks data (frames++word n))=
      some (-1,banks (data++word n) frames) := by
  rw [show Int.ofNat finishBody.entry=(2138 : Int) by decide +kernel,
    show transferCost frames data n+4=transferCost frames data n+(2+2) by omega]
  have tail := Switch.run_chain finishBody (return_bridge (banks (data++word n) frames))
    (return_exit (banks (data++word n) frames))
  exact Switch.run_chain finishBody (transfer_prefix frames data n) tail

theorem finish_correct (data frames : List Nat) (n : Nat) :
    Switch.run finishBody (transferCost (encode frames) (encode data) n+4)
      (Int.ofNat finishBody.entry,natBanks data (frames++[n]))=
      some (-1,natBanks (data++[n]) frames) := by
  simpa only [natBanks,encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil] using finish_bits (encode data) (encode frames) n

end CatchUp.Machine.Lowering.Finish
