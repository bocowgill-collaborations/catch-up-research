import CatchUp.Machine.Succ.Control

namespace CatchUp.Machine.Succ
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

theorem run_add (p : Program) (m n : Nat) (c : Cfg (states p) 2) :
    run p (m+n) c=(run p m c).bind (run p n) := by
  induction m generalizing c with
  | zero => simp [run,FlatInit.runFrom]
  | succ m ih => simp only [Nat.succ_add,run,FlatInit.runFrom,ih,Option.bind_assoc]

theorem word_present (p : Program) (old next : Fin 3851) (a w : Bit) (d : Dir)
    (neq : old≠2) (h : Words.machine.transition old a=some (w,d,next)) :
    (machine p).transition (wordState p old) a=some (w,d,wordState p next) := by
  rw [word_transition,Call.word_present (base p) old next a w d neq h]
  rfl

theorem word_step (p : Program) (old out : Cfg 3851 2) (neq : old.state≠2)
    (h : step Words.machine old=some out) :
    step (machine p) (wordEmbed p old)=some (wordEmbed p out) := by
  rcases old with ⟨state,T⟩
  cases ht : Words.machine.transition state T.head with
  | none => simp [step,ht] at h
  | some triple =>
    rcases triple with ⟨w,d,next⟩
    simp only [step,ht,Option.map_some,Option.some.injEq] at h
    subst out
    simp only [step,wordEmbed,word_present p state next T.head w d neq ht,Option.map_some]

/-- A run ending before the old return boundary never executed that boundary:
the old machine's closed right-source region prevents a return to this endpoint. -/
theorem word_run_before (p : Program) (n : Nat) (old out : Cfg 3851 2)
    (h : Words.run n old=some out) (outside : ¬Call.afterReturn out.state) :
    run p n (wordEmbed p old)=some (wordEmbed p out) := by
  induction n generalizing old with
  | zero => simpa [run,Words.run,FlatInit.runFrom] using congrArg (Option.map (wordEmbed p)) h
  | succ n ih =>
    have neq : old.state≠2 := by
      intro eq
      exact outside (Call.invariant_run Call.afterReturn Call.after_return_transition _ _ _ h (Or.inl eq))
    cases ht : step Words.machine old with
    | none => simp [Words.run,FlatInit.runFrom,ht] at h
    | some mid =>
      have rest : Words.run n mid=some out := by
        simpa only [Words.run,FlatInit.runFrom,ht,Option.bind_some] using h
      change (step (machine p) (wordEmbed p old)).bind (run p n)=_
      rw [word_step p old mid neq ht,Option.bind_some]
      exact ih mid rest

theorem word_run_right (p : Program) (n : Nat) (old out : Cfg 3851 2)
    (h : Words.run n old=some out) (inside : Call.rightContext old.state) :
    run p n (wordEmbed p old)=some (wordEmbed p out) := by
  induction n generalizing old with
  | zero => simpa [run,Words.run,FlatInit.runFrom] using congrArg (Option.map (wordEmbed p)) h
  | succ n ih =>
    have neq : old.state≠2 := by intro eq;simp [eq,Call.rightContext] at inside
    cases ht : step Words.machine old with
    | none => simp [Words.run,FlatInit.runFrom,ht] at h
    | some mid =>
      have firstRun : Words.run 1 old=some mid := by simp [Words.run,FlatInit.runFrom,ht]
      have midInside := Call.invariant_run Call.rightContext Call.right_transition 1 old mid firstRun inside
      have rest : Words.run n mid=some out := by
        simpa only [Words.run,FlatInit.runFrom,ht,Option.bind_some] using h
      change (step (machine p) (wordEmbed p old)).bind (run p n)=_
      rw [word_step p old mid neq ht,Option.bind_some]
      exact ih mid rest midInside

theorem bit_present (p : Program) (phase : Fin ((Call.base (base p)).length+2))
    (old next : Fin 460) (a w : Bit) (d : Dir)
    (h : Separate.machine.transition old a=some (w,d,next)) :
    (machine p).transition (bitState p phase old) a =
      some (w,d,bitState p phase next) := by
  rw [bit_transition]
  simp [Dispatch.oldInstruction,h,bitState]

theorem bit_step (p : Program) (phase : Fin ((Call.base (base p)).length+2)) (old out : Cfg 460 2)
    (h : step Separate.machine old=some out) :
    step (machine p) (bitEmbed p phase old)=some (bitEmbed p phase out) := by
  rcases old with ⟨state,T⟩
  cases ht : Separate.machine.transition state T.head with
  | none => simp [step,ht] at h
  | some triple =>
    rcases triple with ⟨w,d,next⟩
    simp only [step,ht,Option.map_some,Option.some.injEq] at h
    subst out
    simp only [step,bitEmbed,bit_present p phase state next T.head w d ht,Option.map_some]

theorem bit_run (p : Program) (phase : Fin ((Call.base (base p)).length+2)) (n : Nat) (old out : Cfg 460 2)
    (h : Separate.run n old=some out) :
    run p n (bitEmbed p phase old)=some (bitEmbed p phase out) := by
  induction n generalizing old with
  | zero => simpa [run,Separate.run,FlatInit.runFrom] using congrArg (Option.map (bitEmbed p phase)) h
  | succ n ih =>
    cases ht : step Separate.machine old with
    | none => simp [Separate.run,FlatInit.runFrom,ht] at h
    | some mid =>
      have rest : Separate.run n mid=some out := by
        simpa only [Separate.run,FlatInit.runFrom,ht,Option.bind_some] using h
      change (step (machine p) (bitEmbed p phase old)).bind (run p n)=_
      rw [bit_step p phase old mid ht,Option.bind_some]
      exact ih mid rest

theorem bit_boundary (p : Program) (phase : Fin ((Call.base (base p)).length+2))
    (s : Side) (b : Bit) (k : Fin 5) (T : Tape Bit) :
    run p 2 ⟨bitState p phase (q 20 s b k),T⟩ =
      some ⟨after p phase b,T⟩ := by
  simp [run,FlatInit.runFrom,step,bit_transition,Dispatch.oldInstruction,Separate.machine,
    Separate.q,bounce_transition,bitState]

theorem pop_bit (p : Program) (phase : Fin ((Call.base (base p)).length+2)) (u v : List Bit) (b : Bit) :
    run p (4*u.length+14) ⟨readStart p phase,home false (u++[b]) v⟩ =
      some ⟨after p phase b,home false u v⟩ := by
  have h := bit_run p phase _ _ _ (Separate.pop_correct false u v b 0 0)
  simp only [Separate.destination,show (0:Fin 5) ≠ 1 by decide,
    show (0:Fin 5) ≠ 2 by decide,show (0:Fin 5) ≠ 3 by decide,
    show (0:Fin 5) ≠ 4 by decide,↓reduceIte,bitEmbed] at h
  rw [show 4*u.length+14=(4*u.length+12)+2 by omega,run_add]
  change (run p (4*u.length+12)
    ⟨bitState p phase (q 10 false 0 0),home false (u++[b]) v⟩).bind _=_
  rw [h,Option.bind_some]
  exact bit_boundary p phase false b 0 _

end CatchUp.Machine.Succ
