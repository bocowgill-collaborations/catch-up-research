import CatchUp.Machine.Lowering.Finish.Sites

namespace CatchUp.Machine.Lowering.Finish
open Turing ConjectureMachines Compilation Separate Words Relocation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
attribute [local irreducible] entryState Cases.pool

theorem finish_pack (p : Placement) (hp : p∈placements) (kind : p.site.kind=Bank.finish)
    (w : Bit) (d : Dir) (q : Int) (safe : LocalTarget finishBody.size q) :
    pack (w,d,if q<0 then (Cases.entry projection p.site.next).val else p.base+q.toNat)=
      some (w,d,relocatedState p q) := by
  by_cases hn : q<0
  · simp only [relocatedState,hn,↓reduceIte,entryState,widenState]
    exact pack_nat w d _ (lt_trans (Cases.entry projection p.site.next).isLt base_below_total)
  · have bound := (placed_bounds p hp).2
    rw [kind] at bound
    change p.base+finishBody.size<totalSize at bound
    have hq : q.toNat<finishBody.size := safe.resolve_left hn
    have target := lt_trans (Nat.add_lt_add_left hq p.base) bound
    simp only [hn,↓reduceIte,relocatedState,target,↓reduceDIte]
    exact pack_nat w d (p.base+q.toNat) target

theorem finish_step (p : Placement) (hp : p∈placements) (kind : p.site.kind=Bank.finish)
    (c out : Switch.Config) (h : Switch.step finishBody c=some out) :
    ConjectureMachines.step machine (relocated p c)=some (relocated p out) := by
  rcases c with ⟨q,T⟩
  have nonneg : ¬q<0 := by
    intro negative
    simp only [Switch.step,negative,↓reduceIte] at h
    cases h
  lift q to Nat using (Int.le_of_not_gt nonneg)
  change Switch.step finishBody ((q : Int),T)=some out at h
  rw [Switch.Extract.step_nat] at h
  cases hc : finishBody.cell q T.head with
  | none => simp only [hc,Option.map_none] at h;cases h
  | some triple =>
    rcases triple with ⟨w,d,target⟩
    have small : q<finishBody.size := by
      by_contra hn
      have impossible := Switch.cells_past finishBody.segments 0 q T.head
        (Nat.le_of_not_lt hn)
      rw [show cells finishBody.segments 0 q T.head=some (w,d,target) from hc]
        at impossible
      cases impossible
    have ht := body_transition p hp q (by simpa only [kind,bankBody] using small) T.head
    simp only [kind,bankBody,hc,Option.bind_some] at ht
    rw [finish_pack p hp kind w d target (finish_targets _ _ _ _ _ hc)] at ht
    simp only [hc,Option.map_some,Option.some.injEq] at h
    subst out
    simp only [ConjectureMachines.step,relocated,ht,Option.map_some]

theorem finish_run (p : Placement) (hp : p∈placements) (kind : p.site.kind=Bank.finish)
    (n : Nat) (c out : Switch.Config) (h : Switch.run finishBody n c=some out) :
    FlatInit.runFrom machine n (relocated p c)=some (relocated p out) := by
  induction n generalizing c with
  | zero =>
    simpa only [Switch.run,FlatInit.runFrom,Option.map_some] using
      congrArg (Option.map (relocated p)) h
  | succ n ih =>
    cases hs : Switch.step finishBody c with
    | none => simp [Switch.run,hs] at h
    | some mid =>
      have rest : Switch.run finishBody n mid=some out := by
        simpa only [Switch.run,hs,Option.bind_some] using h
      rw [FlatInit.runFrom,finish_step p hp kind c mid hs,Option.bind_some]
      exact ih mid rest

end CatchUp.Machine.Lowering.Finish
