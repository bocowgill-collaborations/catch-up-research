import CatchUp.Machine.Lowering.Relocation
import CatchUp.Machine.Lowering.SourceSucc.Contract

namespace CatchUp.Machine.Lowering.SourceSucc
open Turing ConjectureMachines Compilation Separate Words Relocation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def sourceSuccPlacements : List Placement :=
  concretePlacements.filter (fun p ↦ p.site.kind==Bank.sourceSucc)

theorem source_succ_count : sourceSuccPlacements.length=1 := by decide +kernel

theorem source_succ_site_identity :
    (sourceSuccPlacements.map (fun p ↦ (p.site.pc,p.site.next)))=[(9,6)] := by decide +kernel

theorem source_succ_next (p : Placement) (h : p∈sourceSuccPlacements) : p.site.next=6 := by
  have member : (p.site.pc,p.site.next)∈
      sourceSuccPlacements.map (fun p ↦ (p.site.pc,p.site.next)) := List.mem_map_of_mem h
  rw [source_succ_site_identity,List.mem_singleton,Prod.mk.injEq] at member
  exact member.2

/-- This is the actual shared increment opcode, not behavior attributed to the
normalization body. Its core-machine integration remains a separate obligation. -/
theorem shared_increment_instruction : program[6]?=some (.core .succ) := rfl

theorem source_succ_handoff (p : Placement) (h : p∈sourceSuccPlacements) :
    program[p.site.next]?=some (.core .succ) := by
  rw [source_succ_next p h]
  exact shared_increment_instruction

theorem source_succ_mem (p : Placement) :
    p∈sourceSuccPlacements ↔ p∈placements ∧ p.site.kind=Bank.sourceSucc := by
  simp only [sourceSuccPlacements,←placements_concrete,List.mem_filter,beq_iff_eq]

theorem source_succ_hook (p : Placement) (h : p∈sourceSuccPlacements) :
    placements.find? (fun r ↦ hook p.site.pc=hook r.site.pc)=some p ∧
    program[p.site.pc]?=some (.bank Bank.sourceSucc p.site.next) := by
  have member := (source_succ_mem p).mp h
  have source := site_program p.site (placed_site sites (Cases.states projection) p member.1)
  rw [member.2] at source
  exact ⟨hook_find p member.1,source⟩

/-- Direct coverage of every actual source_succ instruction, not only of a supplied list. -/
theorem source_succ_coverage (pc next : Nat)
    (h : program[pc]?=some (.bank Bank.sourceSucc next)) :
    ∃ p∈sourceSuccPlacements,p.site.pc=pc ∧ p.site.next=next := by
  obtain ⟨p,member,eq⟩ := place_complete sites (Cases.states projection)
    ⟨pc,Bank.sourceSucc,next⟩ (site_complete pc next Bank.sourceSucc h)
  refine ⟨p,(source_succ_mem p).mpr ⟨member,?_⟩,?_,?_⟩ <;> rw [eq]

theorem source_succ_targets_checked :
    sourceSuccBody.segments.all (safeSegment sourceSuccBody.size)=true := by decide +kernel

theorem source_succ_targets (q : Nat) (a w : Bit) (d : Dir) (out : Int)
    (h : sourceSuccBody.cell q a=some (w,d,out)) : LocalTarget sourceSuccBody.size out :=
  safe_cells_target sourceSuccBody.size 0 q sourceSuccBody.segments a w d out
    (by simp only [Micro.size,Nat.zero_add];exact Nat.le_refl _) source_succ_targets_checked h

end CatchUp.Machine.Lowering.SourceSucc
