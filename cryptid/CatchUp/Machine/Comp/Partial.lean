import CatchUp.Machine.Comp.Contract

/-! A continuation-sensitive contract supports the reverse halting direction.
It refers to the actual binary machine, including each saved continuation. -/
namespace CatchUp.Machine.Comp
open Turing ConjectureMachines Compilation Cases
set_option backward.isDefEq.respectTransparency false

def HaltsFrom (p : Program) (c : Cfg (states p) 2) : Prop :=
  (StateTransition.eval (step (machine p)) c).Dom

theorem halts_run_iff (p : Program) (steps : Nat) (c out : Cfg (states p) 2)
    (h : run p steps c=some out) : HaltsFrom p c ↔ HaltsFrom p out := by
  have eq := StateTransition.reaches_eval (FlatInit.runFrom_reaches _ _ _ _ h)
  unfold HaltsFrom
  rw [eq]

/-- Halting after entering a callee is exactly source convergence followed by
halting after its return boundary, with the original frame list. Undefined
source inputs therefore cannot halt. This is separate from ResultContract and
supports the reverse halting direction. -/
def HaltingContract (p : Program) (code : Code) (address : Nat) : Prop :=
  ∀ source frames, HaltsFrom p ⟨entry p address,sourceBanks source frames⟩ ↔
    ∃ result ∈ code.eval source,
      HaltsFrom p ⟨wordState p (Words.start true false),sourceBanks result frames⟩

theorem invoke_halts_iff (p : Program) (first second callSite target continuation : Nat)
    (hfirst : p[first]?=some (.push target second))
    (hsecond : p[second]?=some (.push continuation callSite))
    (hcall : p[callSite]?=some .call) (code : Code)
    (hc : HaltingContract p code target) (source frames : List Nat) :
    HaltsFrom p ⟨entry p first,sourceBanks source frames⟩ ↔
      ∃ result ∈ code.eval source,
        HaltsFrom p ⟨entry p continuation,sourceBanks result frames⟩ := by
  have front := pushes_dynamic_call p first second callSite target continuation
    hfirst hsecond hcall source.reverse frames
  change run p _ ⟨entry p first,sourceBanks source frames⟩=
    some ⟨entry p target,sourceBanks source (frames++[continuation])⟩ at front
  rw [halts_run_iff p _ _ _ front,hc]
  apply exists_congr
  intro result
  apply and_congr_right
  intro _
  have back := return_correct p result.reverse frames continuation
  change run p _ ⟨wordState p (Words.start true false),
    sourceBanks result (frames++[continuation])⟩=
    some ⟨entry p continuation,sourceBanks result frames⟩ at back
  exact halts_run_iff p _ _ _ back

theorem comp_halts_iff (p : Program) (layout : Layout p) (f g : Code)
    (hf : HaltingContract p f layout.targetF) (hg : HaltingContract p g layout.targetG)
    (source frames : List Nat) :
    HaltsFrom p ⟨entry p layout.first,sourceBanks source frames⟩ ↔
      ∃ result ∈ (.comp f g : Code).eval source,
        HaltsFrom p ⟨entry p layout.done,sourceBanks result frames⟩ := by
  rw [invoke_halts_iff p layout.first layout.secondG layout.callG layout.targetG layout.resume
    layout.first_op layout.secondG_op layout.callG_op g hg source frames]
  simp_rw [invoke_halts_iff p layout.resume layout.secondF layout.callF layout.targetF layout.done
    layout.resume_op layout.secondF_op layout.callF_op f hf]
  constructor
  · rintro ⟨middle,hgsource,result,hfsource,hhalt⟩
    exact ⟨result,(comp_mem_iff f g source result).mpr ⟨middle,hgsource,hfsource⟩,hhalt⟩
  · rintro ⟨result,hsource,hhalt⟩
    obtain ⟨middle,hgsource,hfsource⟩ := (comp_mem_iff f g source result).mp hsource
    exact ⟨middle,hgsource,result,hfsource,hhalt⟩

theorem comp_halting_contract (p : Program) (layout : Layout p) (f g : Code)
    (hdone : p[layout.done]?=some .ret)
    (hf : HaltingContract p f layout.targetF) (hg : HaltingContract p g layout.targetG) :
    HaltingContract p (.comp f g) layout.first := by
  intro source frames
  rw [←entry_return p layout.done hdone]
  exact comp_halts_iff p layout f g hf hg source frames

theorem embedding_respects (p : Program) (initial : List Nat) :
    StateTransition.Respects (step (machine p)) (step (generated p initial).toMachine)
      (fun a b ↦ embed p initial a=b) := by
  apply StateTransition.fun_respects.mpr
  intro c
  cases h : step (machine p) c with
  | none => simpa [StateTransition.FRespects,h] using step_embed p initial c
  | some out =>
    exact Relation.TransGen.single (by simpa [h] using step_embed p initial c)

/-- Paid initialization and embedding preserve halting in both directions,
including absence of unintended divergence after a source computation halts. -/
theorem initialized_halts_iff (p : Program) (source : List Nat) :
    Halts (generated p source.reverse).toMachine ↔
      HaltsFrom p ⟨entry p 0,sourceBanks source []⟩ := by
  have initial := StateTransition.reaches_eval
    (FlatInit.runFrom_reaches _ _ _ _ (initializes p source.reverse))
  have body := StateTransition.tr_eval_dom (embedding_respects p source.reverse)
    (show embed p source.reverse ⟨0,Words.natBanks source.reverse []⟩=_ from rfl)
  change (StateTransition.eval (step (generated p source.reverse).toMachine)
    ConjectureMachines.init).Dom ↔ _
  rw [initial]
  exact body.trans (halts_run_iff p 2 _ _ (boot p (sourceBanks source [])))

/-- A full blank-tape halting equivalence for composition, conditional only on
the two continuation-sensitive callee contracts, not their totality. -/
theorem comp_blank_iff (p : Program) (layout : Layout p) (f g : Code)
    (hfirst : layout.first=0) (hdone : p[layout.done]?=some .halt)
    (hf : HaltingContract p f layout.targetF) (hg : HaltingContract p g layout.targetG)
    (source : List Nat) :
    Halts (generated p source.reverse).toMachine ↔ ((.comp f g : Code).eval source).Dom := by
  have done : ∀ result, HaltsFrom p ⟨entry p layout.done,sourceBanks result []⟩ := by
    intro result
    exact Part.dom_iff_mem.mpr ⟨_,StateTransition.mem_eval.mpr
      ⟨Relation.ReflTransGen.refl,terminal p _ layout.done (Or.inr hdone)⟩⟩
  rw [initialized_halts_iff,←hfirst,comp_halts_iff p layout f g hf hg]
  simp only [done,and_true,Part.dom_iff_mem]

end CatchUp.Machine.Comp
