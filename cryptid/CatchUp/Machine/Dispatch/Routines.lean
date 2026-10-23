import CatchUp.Machine.Dispatch.Control

namespace CatchUp.Machine.Dispatch
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

def bitEmbed (p : Program) (phase : Fin (p.length+2)) (c : Cfg 460 2) :
    Cfg (states p.length) 2 := ⟨normal p.length phase c.state,c.tape⟩
def wordEmbed (p : Program) (c : Cfg 3851 2) : Cfg (states p.length) 2 :=
  ⟨wordState p.length c.state,c.tape⟩

theorem run_add (p : Program) (m n : Nat) (c : Cfg (states p.length) 2) :
    run p (m+n) c=(run p m c).bind (run p n) := by
  induction m generalizing c with
  | zero => simp [run,FlatInit.runFrom]
  | succ m ih => simp only [Nat.succ_add,run,FlatInit.runFrom,ih,Option.bind_assoc]

theorem bit_present (p : Program) (phase : Fin (p.length+2))
    (old next : Fin 460) (a write : Bit) (dir : Dir)
    (h : Separate.machine.transition old a=some (write,dir,next)) :
    (machine p).transition (normal p.length phase old) a =
      some (write,dir,normal p.length phase next) := by
  rw [normal_transition]
  simp [oldInstruction,h]

theorem bit_step (p : Program) (phase : Fin (p.length+2)) (old out : Cfg 460 2)
    (h : step Separate.machine old=some out) :
    step (machine p) (bitEmbed p phase old)=some (bitEmbed p phase out) := by
  rcases old with ⟨state,T⟩
  cases ht : Separate.machine.transition state T.head with
  | none => simp [step,ht] at h
  | some triple =>
    rcases triple with ⟨write,dir,next⟩
    simp only [step,ht,Option.map_some,Option.some.injEq] at h
    subst out
    simp only [step,bitEmbed,bit_present p phase state next T.head write dir ht,Option.map_some]

theorem bit_run (p : Program) (phase : Fin (p.length+2)) (n : Nat) (old out : Cfg 460 2)
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

theorem word_present (p : Program) (old next : Fin 3851) (a write : Bit) (dir : Dir)
    (h : Words.machine.transition old a=some (write,dir,next)) :
    (machine p).transition (wordState p.length old) a=some (write,dir,wordState p.length next) := by
  rw [word_transition,h]

theorem word_step (p : Program) (old out : Cfg 3851 2)
    (h : step Words.machine old=some out) :
    step (machine p) (wordEmbed p old)=some (wordEmbed p out) := by
  rcases old with ⟨state,T⟩
  cases ht : Words.machine.transition state T.head with
  | none => simp [step,ht] at h
  | some triple =>
    rcases triple with ⟨write,dir,next⟩
    simp only [step,ht,Option.map_some,Option.some.injEq] at h
    subst out
    simp only [step,wordEmbed,word_present p state next T.head write dir ht,Option.map_some]

theorem word_run (p : Program) (n : Nat) (old out : Cfg 3851 2)
    (h : Words.run n old=some out) :
    run p n (wordEmbed p old)=some (wordEmbed p out) := by
  induction n generalizing old with
  | zero => simpa [run,Words.run,FlatInit.runFrom] using congrArg (Option.map (wordEmbed p)) h
  | succ n ih =>
    cases ht : step Words.machine old with
    | none => simp [Words.run,FlatInit.runFrom,ht] at h
    | some mid =>
      have rest : Words.run n mid=some out := by
        simpa only [Words.run,FlatInit.runFrom,ht,Option.bind_some] using h
      change (step (machine p) (wordEmbed p old)).bind (run p n)=_
      rw [word_step p old mid ht,Option.bind_some]
      exact ih mid rest

theorem boundary (p : Program) (phase : Fin (p.length+2)) (s : Side) (b : Bit)
    (k : Fin 5) (T : Tape Bit) :
    run p 2 ⟨normal p.length phase (q 20 s b k),T⟩ = some ⟨after p phase b,T⟩ := by
  simp [run,FlatInit.runFrom,step,normal_transition,oldInstruction,Separate.machine,
    Separate.q,bounce_transition]

theorem pop_bit (p : Program) (phase : Fin (p.length+2)) (u v : List Bit) (b : Bit) :
    run p (4*u.length+14) ⟨readStart p.length phase,home false (u++[b]) v⟩ =
      some ⟨after p phase b,home false u v⟩ := by
  have h := bit_run p phase _ _ _ (Separate.pop_correct false u v b 0 0)
  simp only [Separate.destination,show (0:Fin 5) ≠ 1 by decide,
    show (0:Fin 5) ≠ 2 by decide,show (0:Fin 5) ≠ 3 by decide,
    show (0:Fin 5) ≠ 4 by decide,↓reduceIte,bitEmbed] at h
  rw [show 4*u.length+14=(4*u.length+12)+2 by omega,run_add]
  change (run p (4*u.length+12)
    ⟨normal p.length phase (q 10 false 0 0),home false (u++[b]) v⟩).bind _=_
  rw [h,Option.bind_some]
  exact boundary p phase false b 0 _

theorem return_handoff (p : Program) (T : Tape Bit) :
    run p 2 ⟨wordState p.length (Words.doneState (Words.ctx true true true)),T⟩ =
      some ⟨readStart p.length 0,T⟩ := by
  simp [run,FlatInit.runFrom,step,word_transition,Words.done_transition,global_transition]

end CatchUp.Machine.Dispatch
