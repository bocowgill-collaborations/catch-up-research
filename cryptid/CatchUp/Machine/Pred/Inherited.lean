import CatchUp.Machine.Pred.Arithmetic

namespace CatchUp.Machine.Pred
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

theorem succ_run (p : Program) (stage : Fin 3) (n : Nat) (old out : Cfg 460 2)
    (h : Separate.run n old=some out) :
    run p n (primitiveEmbed p (succNormal p stage) old)=
      some (primitiveEmbed p (succNormal p stage) out) := by
  apply primitive_run p (succNormal p stage) _ n old out h
  intro old next a w d ht
  rw [succ_transition,Succ.local_present (base p) stage old next a w d ht]
  rfl

theorem succ_boundary (p : Program) (stage : Fin 3) (s : Side) (b : Bit)
    (k : Fin 5) (T : Tape Bit) :
    run p 2 ⟨succNormal p stage (q 20 s b k),T⟩=
      some ⟨lift p (Succ.next (base p) stage b),T⟩ := by
  simp [run,FlatInit.runFrom,step,succ_transition,Succ.normal_transition,Succ.oldInstruction,
    Separate.machine,Separate.q,succ_bridge_transition]

theorem pop_succ (p : Program) (stage : Fin 3) (u v : List Bit) (b : Bit) :
    run p (4*u.length+14) ⟨succNormal p stage (q 10 false 0 0),home false (u++[b]) v⟩ =
      some ⟨lift p (Succ.next (base p) stage b),home false u v⟩ := by
  have h := succ_run p stage _ _ _ (Separate.pop_correct false u v b 0 0)
  simp only [Separate.destination,show (0:Fin 5) ≠ 1 by decide,
    show (0:Fin 5) ≠ 2 by decide,show (0:Fin 5) ≠ 3 by decide,
    show (0:Fin 5) ≠ 4 by decide,↓reduceIte,primitiveEmbed] at h
  rw [show 4*u.length+14=(4*u.length+12)+2 by omega,run_add,h,Option.bind_some]
  exact succ_boundary p stage false b 0 _

theorem push_succ (p : Program) (stage : Fin 3) (u v : List Bit) (b : Bit) :
    run p (4*u.length+10) ⟨succNormal p stage (q 2 false b 0),home false u v⟩ =
      some ⟨lift p (Succ.next (base p) stage b),home false (u++[b]) v⟩ := by
  have h := succ_run p stage _ _ _ (Separate.push_correct false u v b 0)
  simp only [Separate.destination,show (0:Fin 5) ≠ 1 by decide,
    show (0:Fin 5) ≠ 2 by decide,show (0:Fin 5) ≠ 3 by decide,
    show (0:Fin 5) ≠ 4 by decide,↓reduceIte,primitiveEmbed] at h
  rw [show 4*u.length+10=(4*u.length+8)+2 by omega,run_add,h,Option.bind_some]
  exact succ_boundary p stage false b 0 _

def succCost (u : List Bit) (n : Nat) := 12*(u.length+n+1)+38

/-- On canonical words the closing delimiter is replaced by one and a new
closing delimiter. Both arbitrary raw prefixes are preserved, and the head
returns home before the actual return routine starts. -/
theorem successor_bits (p : Program) (u v : List Bit) (n : Nat) :
    run p (succCost u n) ⟨succNormal p 0 (q 10 false 0 0),home false (u++Words.word n) v⟩ =
      some ⟨wordState p (Words.start true false),home false (u++Words.word (n+1)) v⟩ := by
  let w := u++[0]++List.replicate n 1
  have len : w.length=u.length+n+1 := by simp [w];omega
  have cost : succCost u n=(4*w.length+14)+((4*w.length+10)+(4*(w++[1]).length+10)) := by
    simp only [succCost,List.length_append,List.length_singleton,len]
    omega
  have a := pop_succ p 0 w v 0
  have b := push_succ p 1 w v 1
  have c := push_succ p 2 (w++[1]) v 0
  simp only [Succ.next,show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide,
    show (2:Fin 3)≠1 by decide,↓reduceIte] at a b c
  rw [cost,run_add]
  change (run p (4*w.length+14) ⟨succNormal p 0 (q 10 false 0 0),_⟩).bind _=_
  have word0 : u++Words.word n=w++[0] := by simp [w,Words.word,List.append_assoc]
  rw [word0,a,Option.bind_some,run_add,b,Option.bind_some,c]
  have word1 : (w++[1])++[0]=u++Words.word (n+1) := by
    simp [w,Words.word,List.replicate_succ',List.append_assoc]
  rw [word1]

theorem successor_nat (p : Program) (address : Nat) (h : p[address]?=some .succ)
    (data frames : List Nat) (n : Nat) :
    run p (succCost (Words.encode data) n)
      ⟨entry p address,Words.natBanks (data++[n]) frames⟩ =
      some ⟨wordState p (Words.start true false),Words.natBanks (data++[n+1]) frames⟩ := by
  rw [entry_successor p address h]
  simpa [Words.natBanks,Words.encode,List.flatMap_append,home_swap] using
    successor_bits p (Words.encode data) (Words.encode frames) n

theorem call_successor_return (p : Program) (data frames : List Nat) (n target continuation : Nat)
    (h : p[target]?=some .succ) :
    run p (callCost (data++[n]) frames target continuation+
      succCost (Words.encode data) n+returnCost (data++[n+1]) frames continuation)
      ⟨wordState p (Words.start false false),
        Words.natBanks (data++[n,target,continuation]) frames⟩ =
      some ⟨entry p continuation,Words.natBanks (data++[n+1]) frames⟩ := by
  have callee := successor_nat p target h data (frames++[continuation]) n
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using
    call_callee_return p (data++[n]) (data++[n+1]) frames target continuation
      (succCost (Words.encode data) n) callee

end CatchUp.Machine.Pred
