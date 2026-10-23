import CatchUp.Machine.Lowering.RelocationData

namespace CatchUp.Machine.Lowering.Relocation
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

theorem placed_site (ss : List Site) (n : Nat) (p : Placement) (h : p∈place ss n) :
    p.site∈ss := by
  induction ss generalizing n with
  | nil => simp [place] at h
  | cons s ss ih =>
    simp only [place,List.mem_cons] at h
    rcases h with eq|h
    · subst p;exact List.mem_cons_self
    · exact List.mem_cons_of_mem s (ih _ h)

theorem site_program (s : Site) (h : s∈sites) :
    program[s.pc]?=some (.bank s.kind s.next) := by
  simp only [sites,List.mem_filterMap] at h
  obtain ⟨⟨op,pc⟩,mem,eq⟩ := h
  have read := List.mem_zipIdx_iff_getElem?.mp mem
  cases op with
  | core op => cases eq
  | bank kind next =>
    simp only [Option.some.injEq] at eq
    subst s
    exact read

/-- Any positive cell strictly increases every later prefix sum. -/
theorem take_sum_strict (ns : List Nat) (i j : Nat) (hij : i<j)
    (positive : 0<(ns[i]?).getD 0) : (ns.take i).sum<(ns.take j).sum := by
  induction ns generalizing i j with
  | nil => simp at positive
  | cons n ns ih =>
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [List.getElem?_cons_zero,Option.getD_some] at positive
        simp only [List.take_zero,List.sum_nil,List.take_succ_cons,List.sum_cons]
        omega
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [List.getElem?_cons_succ] at positive
        have rest := ih i j (by omega) positive
        simp only [List.take_succ_cons,List.sum_cons]
        omega

theorem hook_strict (s : Site) (hs : s∈sites) (later : Nat) (h : s.pc<later) :
    hook s.pc<hook later := by
  have op := site_program s hs
  have read : (projection.map literalSize)[s.pc]?=some 2 := by
    simp only [projection,List.getElem?_map,op,Option.map_some,project,literalSize]
  have sum := take_sum_strict (projection.map literalSize) s.pc later h
    (by rw [read];decide)
  unfold hook
  rw [List.map_take,List.map_take]
  omega

theorem equal_hooks_pc (p r : Placement) (hp : p∈placements) (hr : r∈placements)
    (eq : hook p.site.pc=hook r.site.pc) : p.site.pc=r.site.pc := by
  have ps := placed_site sites (Cases.states projection) p hp
  have rs := placed_site sites (Cases.states projection) r hr
  rcases lt_trichotomy p.site.pc r.site.pc with lt|eqpc|lt
  · have := hook_strict p.site ps r.site.pc lt
    omega
  · exact eqpc
  · have := hook_strict r.site rs p.site.pc lt
    omega

theorem pc_unique_checked :
    ((place siteData 208978778).map (fun p ↦ p.site.pc)).Nodup := by
  decide +kernel

theorem pc_unique : (placements.map (fun p ↦ p.site.pc)).Nodup := by
  rw [placements_concrete,concretePlacements,site_data_checked]
  exact pc_unique_checked

theorem hooks_unique : placements.Pairwise (fun p r ↦ hook p.site.pc≠hook r.site.pc) := by
  have pcs : placements.Pairwise (fun p r ↦ p.site.pc≠r.site.pc) := by
    simpa only [List.nodup_iff_pairwise_ne,List.pairwise_map] using pc_unique
  apply pcs.imp_of_mem
  intro p r hp hr ne eq
  exact ne (equal_hooks_pc p r hp hr eq)

/-- First-match lookup returns this member itself, with no payload-equality oracle. -/
theorem find_key {α : Type} (key : α → Nat) (xs : List α) (p : α) (h : p∈xs)
    (unique : xs.Pairwise (fun a b ↦ key a≠key b)) :
    xs.find? (fun r ↦ key p=key r)=some p := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    simp only [List.pairwise_cons] at unique
    rcases h with eq|h
    · subst p
      simp only [List.find?,decide_true]
    · have ne : key p≠key x := Ne.symm (unique.1 p h)
      simpa only [List.find?,ne,decide_false,↓reduceIte] using ih h unique.2

theorem hook_find (p : Placement) (h : p∈placements) :
    placements.find? (fun r ↦ hook p.site.pc=hook r.site.pc)=some p := by
  have unique := hooks_unique
  rw [placements_concrete] at h unique ⊢
  have result := find_key (fun r : Placement ↦ hook r.site.pc) concretePlacements p h unique
  exact result

end CatchUp.Machine.Lowering.Relocation
