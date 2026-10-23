import CatchUp.Machine.Lowering.RelocationGeometry
import CatchUp.Machine.Lowering.RelocationTargets
import CatchUp.Machine.Lowering.RelocationEntry

namespace CatchUp.Machine.Lowering.Relocation
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
attribute [local irreducible] entryState Cases.pool

noncomputable def relocatedState (p : Placement) (q : Int) : Fin totalSize :=
  if q<0 then entryState p.site.next
  else if h : p.base+q.toNat<totalSize then ⟨p.base+q.toNat,h⟩ else 0

noncomputable def relocated (p : Placement) (c : Switch.Config) : Cfg totalSize 2 :=
  ⟨relocatedState p c.1,c.2⟩

theorem relocated_nat (p : Placement) (q : Nat) (h : p.base+q<totalSize) :
    relocatedState p (q : Int)=⟨p.base+q,h⟩ := by
  simp only [relocatedState,show ¬(q : Int)<0 by omega,↓reduceIte,
    Int.toNat_natCast,h,↓reduceDIte]

theorem relocated_return (p : Placement) : relocatedState p (-1)=entryState p.site.next := rfl


theorem body_transition (p : Placement) (hp : p∈placements) (q : Nat)
    (hq : q<(bankBody p.site.kind).size) (a : Bit) :
    machine.transition (relocatedState p (q : Int)) a=
      ((bankBody p.site.kind).cell q a).bind (fun (w,d,n) ↦
        pack (w,d,if n<0 then (Cases.entry projection p.site.next).val else p.base+n.toNat)) := by
  have bounds := placed_bounds p hp
  have hb : p.base+q<totalSize := lt_trans (Nat.add_lt_add_left hq p.base) bounds.2
  rw [relocated_nat p q hb]
  have outside : ¬p.base+q<Cases.states projection :=
    Nat.not_lt.mpr (bounds.1.trans (Nat.le_add_right p.base q))
  have find := placement_find p hp (p.base+q) (Nat.le_add_right _ _)
    (Nat.add_le_add_left (Nat.le_of_lt hq) _)
  have ne : p.base+q≠p.base+(bankBody p.site.kind).size := by omega
  simp only [machine,transition,outside,↓reduceDIte,find,ne,↓reduceIte,
    Nat.add_sub_cancel_left]


theorem bank_bridge (p : Placement) (hp : p∈placements)
    (small : (bankBody p.site.kind).entry<(bankBody p.site.kind).size) (a : Bit) :
    machine.transition (relocatedState p ((bankBody p.site.kind).size : Int)) a=
      some (a,.left,relocatedState p ((bankBody p.site.kind).entry : Int)) := by
  have bounds := placed_bounds p hp
  have target := lt_trans (Nat.add_lt_add_left small p.base) bounds.2
  rw [relocated_nat p _ bounds.2,relocated_nat p _ target]
  have outside : ¬p.base+(bankBody p.site.kind).size<Cases.states projection :=
    Nat.not_lt.mpr (bounds.1.trans (Nat.le_add_right p.base _))
  have find := placement_find p hp (p.base+(bankBody p.site.kind).size)
    (Nat.le_add_right _ _) (Nat.le_refl _)
  simp only [machine,transition,outside,↓reduceDIte,find,↓reduceIte,pack,target]


theorem pack_nat (w : Bit) (d : Dir) (n : Nat) (h : n<totalSize) :
    pack (w,d,n)=some (w,d,⟨n,h⟩) := by
  simp only [pack,h,↓reduceDIte]

theorem bank_hook (p : Placement) (hp : p∈placements)
    (source : program[p.site.pc]?=some (.bank p.site.kind p.site.next))
    (selected : placements.find? (fun r ↦ hook p.site.pc=hook r.site.pc)=some p) (a : Bit) :
    machine.transition (entryState p.site.pc) a=
      some (a,.right,relocatedState p ((bankBody p.site.kind).size : Int)) := by
  have hb := entry_below p.site.pc
  have value := (entry_value p.site.pc).trans
    (bank_entry p.site.pc p.site.next p.site.kind source)
  have equal := congrArg (fun n : Nat ↦
    placements.find? (fun r ↦ n=hook r.site.pc)) value
  have find := equal.trans selected
  have bound := (placed_bounds p hp).2
  conv_rhs => rw [relocated_nat p _ bound]
  simp only [machine,transition,hb,↓reduceDIte,find]
  exact pack_nat a .right _ bound


theorem pack_relocated (p : Placement) (hp : p∈placements) (kind : p.site.kind=Bank.switch)
    (w : Bit) (d : Dir) (q : Int) (safe : LocalTarget switchBody.size q) :
    pack (w,d,if q<0 then (Cases.entry projection p.site.next).val else p.base+q.toNat)=
      some (w,d,relocatedState p q) := by
  by_cases hn : q<0
  · simp only [relocatedState,hn,↓reduceIte,entryState,widenState]
    exact pack_nat w d _ (lt_trans (Cases.entry projection p.site.next).isLt base_below_total)
  · have bound := (placed_bounds p hp).2
    rw [kind] at bound
    change p.base+switchBody.size<totalSize at bound
    have hq : q.toNat<switchBody.size := safe.resolve_left hn
    have target := lt_trans (Nat.add_lt_add_left hq p.base) bound
    simp only [hn,↓reduceIte,relocatedState,target,↓reduceDIte]
    exact pack_nat w d (p.base+q.toNat) target


theorem successful_step (p : Placement) (hp : p∈placements) (kind : p.site.kind=Bank.switch)
    (c out : Switch.Config) (h : Switch.step switchBody c=some out) :
    ConjectureMachines.step machine (relocated p c)=some (relocated p out) := by
  rcases c with ⟨q,T⟩
  have nonneg : ¬q<0 := by
    intro negative
    simp only [Switch.step,negative,↓reduceIte] at h
    cases h
  lift q to Nat using (Int.le_of_not_gt nonneg)
  change Switch.step switchBody ((q : Int),T)=some out at h
  rw [Switch.Extract.step_nat] at h
  cases hc : switchBody.cell q T.head with
  | none => simp only [hc,Option.map_none] at h;cases h
  | some triple =>
    rcases triple with ⟨w,d,target⟩
    have small : q<switchBody.size := by
      by_contra hn
      have impossible := Switch.cells_past switchBody.segments 0 q T.head
        (Nat.le_of_not_lt hn)
      rw [show cells switchBody.segments 0 q T.head=some (w,d,target) from hc]
        at impossible
      cases impossible
    have ht := body_transition p hp q (by simpa only [kind,bankBody] using small) T.head
    simp only [kind,bankBody,hc,Option.bind_some] at ht
    rw [pack_relocated p hp kind w d target (switch_targets _ _ _ _ _ hc)] at ht
    simp only [hc,Option.map_some,Option.some.injEq] at h
    subst out
    simp only [ConjectureMachines.step,relocated,ht,Option.map_some]

/-- Lift every successful finite local run, including its external return.
No claim is made that the caller continuation is a stopping state. -/
theorem successful_run (p : Placement) (hp : p∈placements) (kind : p.site.kind=Bank.switch)
    (n : Nat) (c out : Switch.Config) (h : Switch.run switchBody n c=some out) :
    FlatInit.runFrom machine n (relocated p c)=some (relocated p out) := by
  induction n generalizing c with
  | zero =>
    simpa only [Switch.run,FlatInit.runFrom,Option.map_some] using
      congrArg (Option.map (relocated p)) h
  | succ n ih =>
    cases hs : Switch.step switchBody c with
    | none => simp [Switch.run,hs] at h
    | some mid =>
      have rest : Switch.run switchBody n mid=some out := by
        simpa only [Switch.run,hs,Option.bind_some] using h
      rw [FlatInit.runFrom,successful_step p hp kind c mid hs,Option.bind_some]
      exact ih mid rest

end CatchUp.Machine.Lowering.Relocation
