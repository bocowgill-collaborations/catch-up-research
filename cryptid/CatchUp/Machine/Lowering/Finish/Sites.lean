import CatchUp.Machine.Lowering.Relocation
import CatchUp.Machine.Lowering.Finish.Contract

namespace CatchUp.Machine.Lowering.Finish
open Turing ConjectureMachines Compilation Separate Words Relocation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def finishPlacements : List Placement :=
  concretePlacements.filter (fun p ↦ p.site.kind==Bank.finish)

theorem finish_count : finishPlacements.length=92 := by decide +kernel

theorem finish_mem (p : Placement) :
    p∈finishPlacements ↔ p∈placements ∧ p.site.kind=Bank.finish := by
  simp only [finishPlacements,←placements_concrete,List.mem_filter,beq_iff_eq]

theorem finish_hook (p : Placement) (h : p∈finishPlacements) :
    placements.find? (fun r ↦ hook p.site.pc=hook r.site.pc)=some p ∧
    program[p.site.pc]?=some (.bank Bank.finish p.site.next) := by
  have member := (finish_mem p).mp h
  have source := site_program p.site (placed_site sites (Cases.states projection) p member.1)
  rw [member.2] at source
  exact ⟨hook_find p member.1,source⟩

/-- Direct coverage of every actual finish instruction, not only of a supplied list. -/
theorem finish_coverage (pc next : Nat)
    (h : program[pc]?=some (.bank Bank.finish next)) :
    ∃ p∈finishPlacements,p.site.pc=pc ∧ p.site.next=next := by
  obtain ⟨p,member,eq⟩ := place_complete sites (Cases.states projection)
    ⟨pc,Bank.finish,next⟩ (site_complete pc next Bank.finish h)
  refine ⟨p,(finish_mem p).mpr ⟨member,?_⟩,?_,?_⟩ <;> rw [eq]

theorem finish_targets_checked :
    finishBody.segments.all (safeSegment finishBody.size)=true := by decide +kernel

theorem finish_targets (q : Nat) (a w : Bit) (d : Dir) (out : Int)
    (h : finishBody.cell q a=some (w,d,out)) : LocalTarget finishBody.size out :=
  safe_cells_target finishBody.size 0 q finishBody.segments a w d out
    (by simp only [Micro.size,Nat.zero_add];exact Nat.le_refl _) finish_targets_checked h

end CatchUp.Machine.Lowering.Finish
