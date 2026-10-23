import CatchUp.Machine.Lowering.RelocationHooks
import CatchUp.Machine.Lowering.RelocationEntry

namespace CatchUp.Machine.Lowering.Relocation
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def switchPlacements : List Placement :=
  concretePlacements.filter (fun p ↦ p.site.kind==Bank.switch)

theorem switch_count : switchPlacements.length=92 := by decide +kernel


theorem switch_mem (p : Placement) :
    p∈switchPlacements ↔ p∈placements ∧ p.site.kind=Bank.switch := by
  simp only [switchPlacements,←placements_concrete,List.mem_filter,beq_iff_eq]


/-- Only numeric bounds remain computational. Program membership and hook
lookup are consequences of the construction and the shared uniqueness proof. -/
def hookMeta (p : Placement) : Bool :=
  decide (p.site.next<1555)

theorem switch_hooks_checked : switchPlacements.all hookMeta=true := by
  rw [switchPlacements,concretePlacements,site_data_checked]
  decide +kernel

theorem switch_hook (p : Placement) (h : p∈switchPlacements) :
    hook p.site.pc<Cases.states projection ∧
    placements.find? (fun r ↦ hook p.site.pc=hook r.site.pc)=some p ∧
    program[p.site.pc]?=some (.bank Bank.switch p.site.next) ∧
    p.site.next<program.length := by
  have all := List.all_eq_true.mp switch_hooks_checked p h
  have next : p.site.next<1555 := of_decide_eq_true all
  have member := (switch_mem p).mp h
  have source := site_program p.site (placed_site sites (Cases.states projection) p member.1)
  rw [member.2] at source
  have bound := (Cases.entry projection p.site.pc).isLt
  rw [bank_entry p.site.pc p.site.next Bank.switch source] at bound
  have len : program.length=1555 := by
    simpa only [projection,List.length_map] using instruction_count
  exact ⟨bound,hook_find p member.1,source,by simpa only [len] using next⟩

theorem site_complete (pc next : Nat) (kind : Bank)
    (h : program[pc]?=some (.bank kind next)) : (⟨pc,kind,next⟩ : Site)∈sites := by
  simp only [sites,List.mem_filterMap]
  exact ⟨(.bank kind next,pc),List.mem_zipIdx_iff_getElem?.mpr h,rfl⟩

theorem place_complete (ss : List Site) (n : Nat) (s : Site) (h : s∈ss) :
    ∃ p∈place ss n,p.site=s := by
  induction ss generalizing n with
  | nil => simp at h
  | cons head ss ih =>
    simp only [List.mem_cons] at h
    rcases h with eq|h
    · subst s
      exact ⟨⟨head,n⟩,List.mem_cons_self,rfl⟩
    · obtain ⟨p,member,eq⟩ := ih (n+(bankBody head.kind).size+1) h
      exact ⟨p,List.mem_cons_of_mem _ member,eq⟩

/-- Every actual program switch is covered, not merely every supplied certificate. -/
theorem switch_coverage (pc next : Nat)
    (h : program[pc]?=some (.bank Bank.switch next)) :
    ∃ p∈switchPlacements,p.site.pc=pc ∧ p.site.next=next := by
  obtain ⟨p,member,eq⟩ := place_complete sites (Cases.states projection)
    ⟨pc,Bank.switch,next⟩ (site_complete pc next Bank.switch h)
  refine ⟨p,(switch_mem p).mpr ⟨member,?_⟩,?_,?_⟩ <;> rw [eq]

end CatchUp.Machine.Lowering.Relocation
