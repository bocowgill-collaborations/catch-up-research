import CatchUp.Machine.Succ.Semantics

namespace CatchUp.Machine.Succ
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

theorem local_present (p : Program) (stage : Fin 3)
    (old next : Fin 460) (a w : Bit) (d : Dir)
    (h : Separate.machine.transition old a=some (w,d,next)) :
    (machine p).transition (normal p stage old) a =
      some (w,d,normal p stage next) := by
  rw [normal_transition]
  simp [oldInstruction,h]

theorem local_step (p : Program) (stage : Fin 3) (old out : Cfg 460 2)
    (h : step Separate.machine old=some out) :
    step (machine p) (localEmbed p stage old)=some (localEmbed p stage out) := by
  rcases old with ⟨state,T⟩
  cases ht : Separate.machine.transition state T.head with
  | none => simp [step,ht] at h
  | some triple =>
    rcases triple with ⟨w,d,next⟩
    simp only [step,ht,Option.map_some,Option.some.injEq] at h
    subst out
    simp only [step,localEmbed,local_present p stage state next T.head w d ht,Option.map_some]

theorem local_run (p : Program) (stage : Fin 3) (n : Nat) (old out : Cfg 460 2)
    (h : Separate.run n old=some out) :
    run p n (localEmbed p stage old)=some (localEmbed p stage out) := by
  induction n generalizing old with
  | zero => simpa [run,Separate.run,FlatInit.runFrom] using congrArg (Option.map (localEmbed p stage)) h
  | succ n ih =>
    cases ht : step Separate.machine old with
    | none => simp [Separate.run,FlatInit.runFrom,ht] at h
    | some mid =>
      have rest : Separate.run n mid=some out := by
        simpa only [Separate.run,FlatInit.runFrom,ht,Option.bind_some] using h
      change (step (machine p) (localEmbed p stage old)).bind (run p n)=_
      rw [local_step p stage old mid ht,Option.bind_some]
      exact ih mid rest

theorem local_boundary (p : Program) (stage : Fin 3) (s : Side) (b : Bit)
    (k : Fin 5) (T : Tape Bit) :
    run p 2 ⟨normal p stage (q 20 s b k),T⟩=some ⟨next p stage b,T⟩ := by
  simp [run,FlatInit.runFrom,step,normal_transition,oldInstruction,Separate.machine,
    Separate.q,bridge_transition]

theorem pop_local (p : Program) (stage : Fin 3) (u v : List Bit) (b : Bit) :
    run p (4*u.length+14) ⟨normal p stage (q 10 false 0 0),home false (u++[b]) v⟩ =
      some ⟨next p stage b,home false u v⟩ := by
  have h := local_run p stage _ _ _ (Separate.pop_correct false u v b 0 0)
  simp only [Separate.destination,show (0:Fin 5) ≠ 1 by decide,
    show (0:Fin 5) ≠ 2 by decide,show (0:Fin 5) ≠ 3 by decide,
    show (0:Fin 5) ≠ 4 by decide,↓reduceIte,localEmbed] at h
  rw [show 4*u.length+14=(4*u.length+12)+2 by omega,run_add,h,Option.bind_some]
  exact local_boundary p stage false b 0 _

theorem push_local (p : Program) (stage : Fin 3) (u v : List Bit) (b : Bit) :
    run p (4*u.length+10) ⟨normal p stage (q 2 false b 0),home false u v⟩ =
      some ⟨next p stage b,home false (u++[b]) v⟩ := by
  have h := local_run p stage _ _ _ (Separate.push_correct false u v b 0)
  simp only [Separate.destination,show (0:Fin 5) ≠ 1 by decide,
    show (0:Fin 5) ≠ 2 by decide,show (0:Fin 5) ≠ 3 by decide,
    show (0:Fin 5) ≠ 4 by decide,↓reduceIte,localEmbed] at h
  rw [show 4*u.length+10=(4*u.length+8)+2 by omega,run_add,h,Option.bind_some]
  exact local_boundary p stage false b 0 _

def succCost (u : List Bit) (n : Nat) := 12*(u.length+n+1)+38

/-- On canonical words the closing delimiter is replaced by one and a new
closing delimiter. Both arbitrary raw prefixes are preserved, and the head
returns home before the actual return routine starts. -/
theorem successor_bits (p : Program) (u v : List Bit) (n : Nat) :
    run p (succCost u n) ⟨entry p (some .succ),home false (u++Words.word n) v⟩ =
      some ⟨wordState p (Words.start true false),home false (u++Words.word (n+1)) v⟩ := by
  let w := u++[0]++List.replicate n 1
  have len : w.length=u.length+n+1 := by simp [w];omega
  have cost : succCost u n=(4*w.length+14)+((4*w.length+10)+(4*(w++[1]).length+10)) := by
    simp only [succCost,List.length_append,List.length_singleton,len]
    omega
  have a := pop_local p 0 w v 0
  have b := push_local p 1 w v 1
  have c := push_local p 2 (w++[1]) v 0
  simp only [next,show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide,
    show (2:Fin 3)≠1 by decide,↓reduceIte] at a b c
  rw [cost,run_add]
  change (run p (4*w.length+14) ⟨normal p 0 (q 10 false 0 0),_⟩).bind _=_
  have word0 : u++Words.word n=w++[0] := by simp [w,Words.word,List.append_assoc]
  rw [word0,a,Option.bind_some,run_add,b,Option.bind_some,c]
  have word1 : (w++[1])++[0]=u++Words.word (n+1) := by
    simp [w,Words.word,List.replicate_succ',List.append_assoc]
  rw [word1]

theorem successor_nat (p : Program) (data frames : List Nat) (n : Nat) :
    run p (succCost (Words.encode data) n)
      ⟨entry p (some .succ),Words.natBanks (data++[n]) frames⟩ =
      some ⟨wordState p (Words.start true false),Words.natBanks (data++[n+1]) frames⟩ := by
  simpa [Words.natBanks,Words.encode,List.flatMap_append,home_swap] using
    successor_bits p (Words.encode data) (Words.encode frames) n

/-- The selected callee actually increments data and returns. The target and
continuation are unbounded naturals; only the target's opcode is prescribed. -/
theorem call_successor_return (p : Program) (data frames : List Nat) (n target continuation : Nat)
    (h : p[target]?=some .succ) :
    run p (callCost (data++[n]) frames target continuation+
      succCost (Words.encode data) n+returnCost (data++[n+1]) frames continuation)
      ⟨wordState p (Words.start false false),
        Words.natBanks (data++[n,target,continuation]) frames⟩ =
      some ⟨entry p p[continuation]?,Words.natBanks (data++[n+1]) frames⟩ := by
  have callee := successor_nat p data (frames++[continuation]) n
  rw [←h] at callee
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using
    call_callee_return p (data++[n]) (data++[n+1]) frames target continuation
      (succCost (Words.encode data) n) callee

/-- A nested call can change data, return to a return instruction, and then
unwind the outer saved continuation. Every earlier word and frame survives. -/
theorem nested_successor (p : Program) (data frames : List Nat)
    (n outerTarget outerContinuation innerTarget innerContinuation : Nat)
    (outer : p[outerTarget]?=some .call) (inner : p[innerTarget]?=some .succ)
    (resume : p[innerContinuation]?=some .ret) :
    run p (callCost (data++[n,innerTarget,innerContinuation]) frames outerTarget outerContinuation+
      ((callCost (data++[n]) (frames++[outerContinuation]) innerTarget innerContinuation+
        succCost (Words.encode data) n+
        returnCost (data++[n+1]) (frames++[outerContinuation]) innerContinuation)+
        returnCost (data++[n+1]) frames outerContinuation))
      ⟨wordState p (Words.start false false),
        Words.natBanks (data++[n,innerTarget,innerContinuation,outerTarget,outerContinuation]) frames⟩ =
      some ⟨entry p p[outerContinuation]?,Words.natBanks (data++[n+1]) frames⟩ := by
  have first := call_correct p (data++[n,innerTarget,innerContinuation]) frames
    outerTarget outerContinuation
  have second := call_successor_return p data (frames++[outerContinuation]) n
    innerTarget innerContinuation inner
  simp only [List.append_assoc,List.cons_append,List.nil_append] at first
  rw [run_add,first,Option.bind_some,outer,entry_call,run_add,second,Option.bind_some,
    resume,entry_return,return_correct]

theorem malformed_closing_bit (p : Program) (u v : List Bit) :
    run p (4*u.length+14)
      ⟨entry p (some .succ),home false (u++[1]) v⟩=some ⟨global p 3,home false u v⟩ := by
  simpa [entry,next] using pop_local p 0 u v 1

end CatchUp.Machine.Succ
