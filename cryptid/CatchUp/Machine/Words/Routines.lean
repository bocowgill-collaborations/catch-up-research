import CatchUp.Machine.Words.Control

namespace CatchUp.Machine.Words
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

theorem run_add (m n : Nat) (c : Cfg 3851 2) :
    run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run,FlatInit.runFrom]
  | succ m ih => simp only [Nat.succ_add,run,FlatInit.runFrom,ih,Option.bind_assoc]

theorem step_present (c : Fin 8) (old out : Cfg 460 2)
    (h : step Separate.machine old = some out) :
    step machine (embed c old) = some (embed c out) := by
  rcases old with ⟨state,T⟩
  cases ht : Separate.machine.transition state T.head with
  | none => simp [step,ht] at h
  | some triple =>
    rcases triple with ⟨write,dir,next⟩
    simp only [step,ht,Option.map_some,Option.some.injEq] at h
    subst out
    simp only [step,embed,normal_present c state next T.head write dir ht,Option.map_some]

/-- Successful finite old runs are preserved. Old stopping states may now
continue, so no inappropriate halting equivalence is assumed here. -/
theorem run_present (c : Fin 8) (n : Nat) (old out : Cfg 460 2)
    (h : Separate.run n old = some out) :
    run n (embed c old) = some (embed c out) := by
  induction n generalizing old with
  | zero => simpa [run,Separate.run,FlatInit.runFrom] using congrArg (Option.map (embed c)) h
  | succ n ih =>
    cases ht : step Separate.machine old with
    | none => simp [Separate.run,FlatInit.runFrom,ht] at h
    | some mid =>
      have rest : Separate.run n mid=some out := by
        simpa only [Separate.run,FlatInit.runFrom,ht,Option.bind_some] using h
      change (step machine (embed c old)).bind (run n) = _
      rw [step_present c old mid ht,Option.bind_some]
      exact ih mid rest

theorem bounce_transition (c : Fin 8) (attr : Fin 20) (a : Bit) :
    machine.transition (bounce c attr) a = some (a,.left,after c (attrs.symm attr).2.1) := by
  have off : 3+c.val*481+460+attr.val-3=c.val*481+(460+attr.val) := by omega
  have div : (c.val*481+(460+attr.val))/481=c.val := by have := attr.isLt;omega
  have rem : (c.val*481+(460+attr.val))%481=460+attr.val := by have := attr.isLt;omega
  simp [machine,bounce,show ¬3+c.val*481+460+attr.val<3 by omega,off,div,rem,
    show ¬460+attr.val<460 by omega,show 460+attr.val<480 by have := attr.isLt;omega]

theorem boundary (c : Fin 8) (s : Side) (b : Bit) (k : Fin 5) (T : Tape Bit)
    (h : (!pushing c && !begun c && decide (b≠0))=false) :
    run 2 ⟨normal c (q 20 s b k),T⟩ = some ⟨after c b,T⟩ := by
  have guard : ¬ ((pushing c=false ∧ begun c=false) ∧ b≠0) := by
    rintro ⟨⟨hp,hb⟩,hn⟩
    simp [hp,hb,hn] at h
  simp [run,FlatInit.runFrom,step,normal_transition,instruction,Separate.machine,
    Separate.q,guard,bounce_transition]

theorem home_flip (s : Side) (a b : List Bit) : home s a b=home (!s) b a := by
  cases s <;> simp [home,view,mirror,Tape.mk₂,Tape.mk']

end CatchUp.Machine.Words
