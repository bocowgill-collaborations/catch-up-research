import CatchUp.Machine.Tail.Semantics

namespace CatchUp.Machine.Tail
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

/-- Relabel successful primitive runs; missing boundaries are proved separately. -/
def primitiveEmbed (p : Program) (f : Fin 460 → Fin (states p)) (c : Cfg 460 2) :
    Cfg (states p) 2 := ⟨f c.state,c.tape⟩

theorem primitive_step (p : Program) (f : Fin 460 → Fin (states p))
    (preserves : ∀ old next a w d, Separate.machine.transition old a=some (w,d,next) →
      (machine p).transition (f old) a=some (w,d,f next))
    (old out : Cfg 460 2) (h : step Separate.machine old=some out) :
    step (machine p) (primitiveEmbed p f old)=some (primitiveEmbed p f out) := by
  rcases old with ⟨state,T⟩
  cases ht : Separate.machine.transition state T.head with
  | none => simp [step,ht] at h
  | some triple =>
    rcases triple with ⟨w,d,next⟩
    simp only [step,ht,Option.map_some,Option.some.injEq] at h
    subst out
    simp only [step,primitiveEmbed,preserves state next T.head w d ht,Option.map_some]

theorem primitive_run (p : Program) (f : Fin 460 → Fin (states p))
    (preserves : ∀ old next a w d, Separate.machine.transition old a=some (w,d,next) →
      (machine p).transition (f old) a=some (w,d,f next))
    (n : Nat) (old out : Cfg 460 2) (h : Separate.run n old=some out) :
    run p n (primitiveEmbed p f old)=some (primitiveEmbed p f out) := by
  induction n generalizing old with
  | zero =>
    simpa [run,Separate.run,FlatInit.runFrom] using congrArg (Option.map (primitiveEmbed p f)) h
  | succ n ih =>
    cases ht : step Separate.machine old with
    | none => simp [Separate.run,FlatInit.runFrom,ht] at h
    | some mid =>
      have rest : Separate.run n mid=some out := by
        simpa only [Separate.run,FlatInit.runFrom,ht,Option.bind_some] using h
      change (step (machine p) (primitiveEmbed p f old)).bind (run p n)=_
      rw [primitive_step p f preserves old mid ht,Option.bind_some]
      exact ih mid rest

theorem local_run (p : Program) (site : Fin (p.length+1)) (stage : Fin 9)
    (n : Nat) (old out : Cfg 460 2) (h : Separate.run n old=some out) :
    run p n (primitiveEmbed p (normal p site stage) old)=
      some (primitiveEmbed p (normal p site stage) out) := by
  apply primitive_run p (normal p site stage) _ n old out h
  intro old next a w d ht
  rw [normal_transition]
  simp [oldInstruction,ht]

theorem local_boundary (p : Program) (site : Fin (p.length+1)) (stage : Fin 9)
    (s : Side) (b : Bit) (k : Fin 5) (T : Tape Bit) :
    run p 2 ⟨normal p site stage (q 20 s b k),T⟩=some ⟨next p site stage b,T⟩ := by
  simp [run,FlatInit.runFrom,step,normal_transition,oldInstruction,Separate.machine,
    Separate.q,bridge_transition]

theorem pop_local (p : Program) (site : Fin (p.length+1)) (stage : Fin 9)
    (u v : List Bit) (b : Bit) :
    run p (4*u.length+14) ⟨normal p site stage (q 10 false 0 0),home false (u++[b]) v⟩ =
      some ⟨next p site stage b,home false u v⟩ := by
  have h := local_run p site stage _ _ _ (Separate.pop_correct false u v b 0 0)
  simp only [Separate.destination,show (0:Fin 5) ≠ 1 by decide,
    show (0:Fin 5) ≠ 2 by decide,show (0:Fin 5) ≠ 3 by decide,
    show (0:Fin 5) ≠ 4 by decide,↓reduceIte,primitiveEmbed] at h
  rw [show 4*u.length+14=(4*u.length+12)+2 by omega,run_add,h,Option.bind_some]
  exact local_boundary p site stage false b 0 _

theorem push_local (p : Program) (site : Fin (p.length+1)) (stage : Fin 9)
    (u v : List Bit) (b : Bit) :
    run p (4*u.length+10) ⟨normal p site stage (q 2 false b 0),home false u v⟩ =
      some ⟨next p site stage b,home false (u++[b]) v⟩ := by
  have h := local_run p site stage _ _ _ (Separate.push_correct false u v b 0)
  simp only [Separate.destination,show (0:Fin 5) ≠ 1 by decide,
    show (0:Fin 5) ≠ 2 by decide,show (0:Fin 5) ≠ 3 by decide,
    show (0:Fin 5) ≠ 4 by decide,↓reduceIte,primitiveEmbed] at h
  rw [show 4*u.length+10=(4*u.length+8)+2 by omega,run_add,h,Option.bind_some]
  exact local_boundary p site stage false b 0 _

theorem restore_zero (p : Program) (site : Fin (p.length+1)) (u v : List Bit) :
    run p (8*u.length+24)
      ⟨normal p site 4 (q 2 false 0 0),home false u v⟩ =
      some ⟨branch p site false,home false (u++Words.word 0) v⟩ := by
  have a := push_local p site 4 u v 0
  have b := push_local p site 5 (u++[0]) v 0
  simp only [next,show (4:Fin 9)≠0 by decide,show (4:Fin 9)≠1 by decide,
    show (4:Fin 9)≠2 by decide,show (4:Fin 9)≠3 by decide,↓reduceIte] at a
  have b' : run p (4*(u++[0]).length+10)
      ⟨normal p site 5 (q 2 false 0 0),home false (u++[0]) v⟩ =
      some ⟨branch p site false,home false (u++Words.word 0) v⟩ := by
    simpa [next,Words.word,List.append_assoc] using b
  rw [show 8*u.length+24=(4*u.length+10)+(4*(u++[0]).length+10) by simp;omega,
    run_add,a,Option.bind_some,b']

theorem zero_tail (p : Program) (site : Fin (p.length+1)) (stage : Fin 9)
    (hstage : stage=1 ∨ stage=3) (u v : List Bit) :
    run p (12*u.length+38)
      ⟨normal p site stage (q 10 false 0 0),home false (u++[0]) v⟩ =
      some ⟨branch p site false,home false (u++Words.word 0) v⟩ := by
  have a := pop_local p site stage u v 0
  have hn : next p site stage 0=normal p site 4 (q 2 false 0 0) := by
    rcases hstage with rfl|rfl <;> simp [next]
  rw [hn] at a
  rw [show 12*u.length+38=(4*u.length+14)+(8*u.length+24) by omega,
    run_add,a,Option.bind_some,restore_zero]

theorem zero_bits (p : Program) (site : Fin (p.length+1)) (test : Bool) (u v : List Bit) :
    run p (16*u.length+56)
      ⟨normal p site (if test then 2 else 0) (q 10 false 0 0),
        home false (u++Words.word 0) v⟩ =
      some ⟨branch p site false,home false (u++Words.word 0) v⟩ := by
  have a := pop_local p site (if test then 2 else 0) (u++[0]) v 0
  have hn : next p site (if test then 2 else 0) 0=
      normal p site (if test then 3 else 1) (q 10 false 0 0) := by
    cases test <;> simp [next]
  rw [hn] at a
  have tail := zero_tail p site (if test then 3 else 1)
    (by cases test <;> simp) u v
  rw [show 16*u.length+56=(4*(u++[0]).length+14)+(12*u.length+38) by simp;omega,run_add]
  have word0 : u++Words.word 0=(u++[0])++[0] := by simp [Words.word,List.append_assoc]
  rw [word0,a,Option.bind_some,tail]
  rw [word0]

def predCost (u : List Bit) : Nat → Nat
  | 0 => 16*u.length+56
  | n+1 => 12*(u.length+n+1)+42
def testCost (u : List Bit) (n : Nat) := 16*(u.length+n)+56

theorem positive_pred_bits (p : Program) (site : Fin (p.length+1)) (u v : List Bit) (n : Nat) :
    run p (predCost u (n+1))
      ⟨normal p site 0 (q 10 false 0 0),home false (u++Words.word (n+1)) v⟩ =
      some ⟨branch p site true,home false (u++Words.word n) v⟩ := by
  let w := u++[0]++List.replicate n 1
  have len : w.length=u.length+n+1 := by simp [w];omega
  have a := pop_local p site 0 (w++[1]) v 0
  have b := pop_local p site 1 w v 1
  have c := push_local p site 6 w v 0
  have a' : next p site 0 0=normal p site 1 (q 10 false 0 0) := by simp [next]
  have b' : next p site 1 1=normal p site 6 (q 2 false 0 0) := by simp [next]
  have c' : next p site 6 0=branch p site true := by simp [next]
  rw [a'] at a
  rw [b'] at b
  rw [c'] at c
  have cost : predCost u (n+1)=(4*(w++[1]).length+14)+((4*w.length+14)+(4*w.length+10)) := by
    simp only [predCost,List.length_append,List.length_singleton,len]
    omega
  have w0 : u++Words.word (n+1)=(w++[1])++[0] := by
    simp [w,Words.word,List.replicate_succ',List.append_assoc]
  rw [cost,run_add,w0,a,Option.bind_some,run_add,b,Option.bind_some,c]
  congr 2
  simp [w,Words.word,List.append_assoc]

theorem positive_test_bits (p : Program) (site : Fin (p.length+1)) (u v : List Bit) (n : Nat) :
    run p (testCost u (n+1))
      ⟨normal p site 2 (q 10 false 0 0),home false (u++Words.word (n+1)) v⟩ =
      some ⟨branch p site true,home false (u++Words.word (n+1)) v⟩ := by
  let w := u++[0]++List.replicate n 1
  have len : w.length=u.length+n+1 := by simp [w];omega
  have a := pop_local p site 2 (w++[1]) v 0
  have b := pop_local p site 3 w v 1
  have c := push_local p site 7 w v 1
  have d := push_local p site 8 (w++[1]) v 0
  have a' : next p site 2 0=normal p site 3 (q 10 false 0 0) := by simp [next]
  have b' : next p site 3 1=normal p site 7 (q 2 false 1 0) := by simp [next]
  have c' : next p site 7 1=normal p site 8 (q 2 false 0 0) := by simp [next]
  have d' : next p site 8 0=branch p site true := by simp [next]
  rw [a'] at a
  rw [b'] at b
  rw [c'] at c
  rw [d'] at d
  have cost : testCost u (n+1)=(4*(w++[1]).length+14)+
      ((4*w.length+14)+((4*w.length+10)+(4*(w++[1]).length+10))) := by
    simp only [testCost,List.length_append,List.length_singleton,len]
    omega
  have w0 : u++Words.word (n+1)=(w++[1])++[0] := by
    simp [w,Words.word,List.replicate_succ',List.append_assoc]
  rw [cost,run_add,w0,a,Option.bind_some,run_add,b,Option.bind_some,run_add,c,Option.bind_some,d]

/-- Every natural is covered, and the actual selected instruction address is
reached. Both arbitrary raw bank prefixes and the physical home are preserved. -/
theorem predecessor_bits (p : Program) (address z s : Nat)
    (h : p[address]?=some (.pred z s)) (u v : List Bit) (n : Nat) :
    run p (predCost u n) ⟨entry p address,home false (u++Words.word n) v⟩ =
      some ⟨entry p (if n=0 then z else s),home false (u++Words.word (n-1)) v⟩ := by
  rw [entry_pred p address z s h]
  cases n with
  | zero => simpa [predCost,branch_pred p address z s false h] using
      zero_bits p (index p address) false u v
  | succ n => simpa [branch_pred p address z s true h] using
      positive_pred_bits p (index p address) u v n

theorem zero_test_bits (p : Program) (address z s : Nat)
    (h : p[address]?=some (.test z s)) (u v : List Bit) (n : Nat) :
    run p (testCost u n) ⟨entry p address,home false (u++Words.word n) v⟩ =
      some ⟨entry p (if n=0 then z else s),home false (u++Words.word n) v⟩ := by
  rw [entry_test p address z s h]
  cases n with
  | zero => simpa [testCost,branch_test p address z s false h] using
      zero_bits p (index p address) true u v
  | succ n => simpa [branch_test p address z s true h] using
      positive_test_bits p (index p address) u v n

end CatchUp.Machine.Tail
