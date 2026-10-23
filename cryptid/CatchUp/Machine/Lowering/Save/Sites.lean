import CatchUp.Machine.Lowering.Relocation
import CatchUp.Machine.Lowering.Save.Contract

namespace CatchUp.Machine.Lowering.Save
open Turing ConjectureMachines Compilation Separate Words Relocation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def savePlacements : List Placement :=
  concretePlacements.filter (fun p ↦ p.site.kind==Bank.save)

theorem save_count : savePlacements.length=92 := by decide +kernel

theorem save_mem (p : Placement) :
    p∈savePlacements ↔ p∈placements ∧ p.site.kind=Bank.save := by
  simp only [savePlacements,←placements_concrete,List.mem_filter,beq_iff_eq]

theorem save_hook (p : Placement) (h : p∈savePlacements) :
    placements.find? (fun r ↦ hook p.site.pc=hook r.site.pc)=some p ∧
    program[p.site.pc]?=some (.bank Bank.save p.site.next) := by
  have member := (save_mem p).mp h
  have source := site_program p.site (placed_site sites (Cases.states projection) p member.1)
  rw [member.2] at source
  exact ⟨hook_find p member.1,source⟩

/-- Direct coverage of every actual save instruction, not only of a supplied list. -/
theorem save_coverage (pc next : Nat)
    (h : program[pc]?=some (.bank Bank.save next)) :
    ∃ p∈savePlacements,p.site.pc=pc ∧ p.site.next=next := by
  obtain ⟨p,member,eq⟩ := place_complete sites (Cases.states projection)
    ⟨pc,Bank.save,next⟩ (site_complete pc next Bank.save h)
  refine ⟨p,(save_mem p).mpr ⟨member,?_⟩,?_,?_⟩ <;> rw [eq]

theorem save_targets_checked :
    saveBody.segments.all (safeSegment saveBody.size)=true := by decide +kernel

theorem save_targets (q : Nat) (a w : Bit) (d : Dir) (out : Int)
    (h : saveBody.cell q a=some (w,d,out)) : LocalTarget saveBody.size out :=
  safe_cells_target saveBody.size 0 q saveBody.segments a w d out
    (by simp only [Micro.size,Nat.zero_add];exact Nat.le_refl _) save_targets_checked h

end CatchUp.Machine.Lowering.Save
