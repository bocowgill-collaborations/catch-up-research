import CatchUp.Machine.Tail.Composition

namespace CatchUp.Machine.Tail
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

theorem tail_transition (p : Program) (stage : Fin 2) (old : Fin 460) (a : Bit) :
    (machine p).transition (tailNormal p stage old) a=tailInstruction p stage old a := by
  simp [machine,tailNormal,old.isLt]

theorem tail_bridge_transition (p : Program) (stage : Fin 2) (b a : Bit) :
    (machine p).transition (tailBridge p stage b) a=some (a,.left,tailNext p stage b) := by
  simp [machine,tailBridge,show ¬460+b.val<460 by omega,
    show 460+b.val<462 by have := b.isLt;omega]

theorem tail_empty_transition (p : Program) (stage : Fin 2) (a : Bit) :
    (machine p).transition (tailEmpty p stage) a=
      some (a,.left,if stage=0 then wordState p (Words.start true false) else global p 3) := by
  simp [machine,tailEmpty]

theorem tail_run (p : Program) (stage : Fin 2) (n : Nat) (old out : Cfg 460 2)
    (h : Separate.run n old=some out) :
    run p n (primitiveEmbed p (tailNormal p stage) old)=
      some (primitiveEmbed p (tailNormal p stage) out) := by
  apply primitive_run p (tailNormal p stage) _ n old out h
  intro old next a w d ht
  rw [tail_transition]
  simp [tailInstruction,ht]

theorem tail_boundary (p : Program) (stage : Fin 2) (s : Side) (b : Bit)
    (k : Fin 5) (T : Tape Bit) :
    run p 2 ⟨tailNormal p stage (q 20 s b k),T⟩=
      some ⟨tailNext p stage b,T⟩ := by
  simp [run,FlatInit.runFrom,step,tail_transition,tailInstruction,Separate.machine,
    Separate.q,tail_bridge_transition]

theorem tail_empty_boundary (p : Program) (stage : Fin 2) (s : Side) (b : Bit)
    (k : Fin 5) (T : Tape Bit) :
    run p 2 ⟨tailNormal p stage (q 19 s b k),T⟩=
      some ⟨if stage=0 then wordState p (Words.start true false) else global p 3,T⟩ := by
  simp [run,FlatInit.runFrom,step,tail_transition,tailInstruction,Separate.machine,
    Separate.q,tail_empty_transition]

theorem tail_pop (p : Program) (stage : Fin 2) (u v : List Bit) (b : Bit) :
    run p (4*u.length+14) ⟨tailNormal p stage (q 10 false 0 0),home false (u++[b]) v⟩=
      some ⟨tailNext p stage b,home false u v⟩ := by
  have h := tail_run p stage _ _ _ (Separate.pop_correct false u v b 0 0)
  simp only [Separate.destination,show (0:Fin 5) ≠ 1 by decide,
    show (0:Fin 5) ≠ 2 by decide,show (0:Fin 5) ≠ 3 by decide,
    show (0:Fin 5) ≠ 4 by decide,↓reduceIte,primitiveEmbed] at h
  rw [show 4*u.length+14=(4*u.length+12)+2 by omega,run_add,h,Option.bind_some]
  exact tail_boundary p stage false b 0 _

theorem tail_pop_empty (p : Program) (stage : Fin 2) (v : List Bit) :
    run p 8 ⟨tailNormal p stage (q 10 false 0 0),home false [] v⟩=
      some ⟨if stage=0 then wordState p (Words.start true false) else global p 3,
        home false [] v⟩ := by
  have h := tail_run p stage _ _ _ (Separate.pop_empty false v 0 0)
  simp only [primitiveEmbed] at h
  rw [show 8=6+2 by rfl,run_add,h,Option.bind_some]
  exact tail_empty_boundary p stage false 0 0 _

def onesCost (u : List Bit) (n : Nat) := (n+1)*(4*u.length+2*n+14)
def discardCost (u : List Bit) (n : Nat) := (n+2)*(4*u.length+2*n+16)

theorem discard_ones (p : Program) (u v : List Bit) (n : Nat) :
    run p (onesCost u n)
      ⟨tailNormal p 1 (q 10 false 0 0),home false (u++[0]++List.replicate n 1) v⟩=
      some ⟨wordState p (Words.start true false),home false u v⟩ := by
  induction n with
  | zero => simpa [onesCost,tailNext] using tail_pop p 1 u v 0
  | succ n ih =>
    have first := tail_pop p 1 (u++[0]++List.replicate n 1) v 1
    simp only [tailNext,show (1:Fin 2)≠0 by decide,↓reduceIte]
      at first
    have cost : onesCost u (n+1)=
        (4*(u++[0]++List.replicate n 1).length+14)+onesCost u n := by
      simp only [onesCost,List.length_append,List.length_singleton,List.length_replicate]
      ring
    have bits : u++[0]++List.replicate (n+1) 1=
        (u++[0]++List.replicate n 1)++[1] := by
      simp [List.replicate_succ',List.append_assoc]
    rw [cost,run_add,bits,first,Option.bind_some,ih]

/-- Remove the whole framed word, preserving arbitrary earlier raw data and
the opposite bank. The routine ends at the real return entry with head home. -/
theorem discard_bits (p : Program) (u v : List Bit) (n : Nat) :
    run p (discardCost u n) ⟨tailStart p,home false (u++Words.word n) v⟩=
      some ⟨wordState p (Words.start true false),home false u v⟩ := by
  have first := tail_pop p 0 (u++[0]++List.replicate n 1) v 0
  simp only [tailNext,↓reduceIte] at first
  have cost : discardCost u n=
      (4*(u++[0]++List.replicate n 1).length+14)+onesCost u n := by
    simp only [discardCost,onesCost,List.length_append,List.length_singleton,
      List.length_replicate]
    ring
  have bits : u++Words.word n=(u++[0]++List.replicate n 1)++[0] := by
    simp [Words.word,List.append_assoc]
  rw [cost,run_add,tailStart,bits,first,Option.bind_some,discard_ones]

theorem discard_empty_bits (p : Program) (v : List Bit) :
    run p 8 ⟨tailStart p,home false [] v⟩=
      some ⟨wordState p (Words.start true false),home false [] v⟩ := by
  simpa [tailStart] using tail_pop_empty p 0 v

theorem entry_tail (p : Program) (address : Nat) (h : p[address]?=some .tail) :
    entry p address=tailStart p := by simp [entry,h]

theorem discard_nat (p : Program) (address : Nat) (h : p[address]?=some .tail)
    (data frames : List Nat) (n : Nat) :
    run p (discardCost (Words.encode data) n)
      ⟨entry p address,Words.natBanks (data++[n]) frames⟩=
      some ⟨wordState p (Words.start true false),Words.natBanks data frames⟩ := by
  rw [entry_tail p address h]
  simpa [Words.natBanks,Words.encode,List.flatMap_append,home_swap] using
    discard_bits p (Words.encode data) (Words.encode frames) n

theorem discard_empty_nat (p : Program) (address : Nat) (h : p[address]?=some .tail)
    (frames : List Nat) :
    run p 8 ⟨entry p address,Words.natBanks [] frames⟩=
      some ⟨wordState p (Words.start true false),Words.natBanks [] frames⟩ := by
  rw [entry_tail p address h]
  simpa [Words.natBanks,Words.encode,home_swap] using discard_empty_bits p (Words.encode frames)

theorem malformed_tail_closer (p : Program) (u v : List Bit) :
    run p (4*u.length+14) ⟨tailStart p,home false (u++[1]) v⟩=
      some ⟨global p 3,home false u v⟩ := by
  simpa [tailStart,tailNext] using tail_pop p 0 u v 1

theorem missing_tail_opener (p : Program) (v : List Bit) :
    run p 8 ⟨tailNormal p 1 (q 10 false 0 0),home false [] v⟩=
      some ⟨global p 3,home false [] v⟩ := by
  simpa using tail_pop_empty p 1 v

end CatchUp.Machine.Tail
