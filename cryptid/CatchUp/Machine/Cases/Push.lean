import CatchUp.Machine.Cases.Contracts

namespace CatchUp.Machine.Cases
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

theorem literal_run (p : Program) (i : Fin (pool p).length) (n : Nat)
    (old out : Cfg 460 2) (h : Separate.run n old=some out) :
    run p n (primitiveEmbed p (literalNormal p i) old)=
      some (primitiveEmbed p (literalNormal p i) out) := by
  apply primitive_run p (literalNormal p i) _ n old out h
  intro old next a w d ht
  rw [literal_transition]
  simp [literalInstruction,ht]

theorem literal_boundary (p : Program) (i : Fin (pool p).length)
    (s : Side) (b : Bit) (k : Fin 5) (T : Tape Bit) :
    run p 2 ⟨literalNormal p i (q 20 s b k),T⟩=
      some ⟨advance p i.val (literalCell p i.val).2,T⟩ := by
  simp [run,FlatInit.runFrom,step,literal_transition,literalInstruction,Separate.machine,
    Separate.q,literal_bridge_transition]

theorem literal_bit (p : Program) (i : Nat) (b : Bit) (continuation : Option Nat)
    (hcell : (pool p)[i]?=some (b,continuation)) (u v : List Bit) :
    run p (4*u.length+10) ⟨literalStart p i,home false u v⟩=
      some ⟨advance p i continuation,home false (u++[b]) v⟩ := by
  obtain ⟨hi,_⟩ := List.getElem?_eq_some_iff.mp hcell
  have h := literal_run p ⟨i,hi⟩ _ _ _ (Separate.push_correct false u v b 0)
  simp only [Separate.destination,show (0:Fin 5) ≠ 1 by decide,
    show (0:Fin 5) ≠ 2 by decide,show (0:Fin 5) ≠ 3 by decide,
    show (0:Fin 5) ≠ 4 by decide,↓reduceIte,primitiveEmbed] at h
  have start : literalStart p i=literalNormal p ⟨i,hi⟩ (q 2 false b 0) := by
    simp only [literalStart,hi,↓reduceDIte,literalCell,hcell,Option.getD_some]
  rw [start,show 4*u.length+10=(4*u.length+8)+2 by omega,run_add,h,Option.bind_some]
  simpa [literalCell,hcell] using literal_boundary p ⟨i,hi⟩ false b 0 (home false (u++[b]) v)

def bitCost (u : List Bit) (n : Nat) := n*(4*u.length+2*n+8)
def literalCost (u : List Bit) (n : Nat) := bitCost u (n+2)

/-- Traverse a contiguous pool prefix. All metadata and every emitted bit are
specified by the pool identity, rather than trusted from an external trace. -/
theorem emit_prefix (p : Program) (bs : List Bit) (pre post : List Cell)
    (continuation : Nat) (u v : List Bit)
    (hpool : pool p=pre++bs.map (fun b ↦ (b,none))++[(0,some continuation)]++post) :
    run p (bitCost u bs.length) ⟨literalStart p pre.length,home false u v⟩=
      some ⟨literalStart p (pre.length+bs.length),home false (u++bs) v⟩ := by
  induction bs generalizing pre u with
  | nil => simp [bitCost,run,FlatInit.runFrom]
  | cons b bs ih =>
    have hc : (pool p)[pre.length]?=some (b,none) := by
      rw [hpool]
      simp
    have first := literal_bit p pre.length b none hc u v
    have restPool : pool p=(pre++[(b,none)])++bs.map (fun b ↦ (b,none))++
        [(0,some continuation)]++post := by
      simpa [List.map_cons,List.append_assoc] using hpool
    have rest := ih (pre++[(b,none)]) (u++[b]) restPool
    have cost : bitCost u (b::bs).length=(4*u.length+10)+bitCost (u++[b]) bs.length := by
      simp only [bitCost,List.length_cons,List.length_append,List.length_nil]
      ring
    rw [cost,run_add,first,Option.bind_some]
    simpa [advance,List.length_append,List.length_singleton,List.append_assoc,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest

theorem push_fragment (p : Program) (pre post : List Cell) (n continuation : Nat)
    (u v : List Bit) (hpool : pool p=pre++fragment n continuation++post) :
    run p (literalCost u n) ⟨literalStart p pre.length,home false u v⟩=
      some ⟨entry p continuation,home false (u++Words.word n) v⟩ := by
  let bs : List Bit := 0::List.replicate n 1
  have hpoolBits : pool p=pre++bs.map (fun b ↦ (b,none))++[(0,some continuation)]++post := by
    simpa only [fragment,bs,List.append_assoc] using hpool
  have first := emit_prefix p bs pre post continuation u v hpoolBits
  have hc : (pool p)[pre.length+bs.length]?=some (0,some continuation) := by
    have hpool' : pool p=(pre++bs.map (fun b ↦ (b,none)))++(0,some continuation)::post := by
      simpa [fragment,bs,List.append_assoc] using hpool
    rw [hpool']
    have len : (pre++bs.map (fun b ↦ (b,none))).length=pre.length+bs.length := by simp
    rw [←len,List.getElem?_append_right (by omega),Nat.sub_self]
    rfl
  have last := literal_bit p (pre.length+bs.length) 0 (some continuation) hc (u++bs) v
  have cost : literalCost u n=bitCost u bs.length+(4*(u++bs).length+10) := by
    simp only [literalCost,bitCost,List.length_append,bs,List.length_cons,List.length_replicate]
    ring
  rw [cost,run_add,first,Option.bind_some,last]
  simp [advance,bs,Words.word,List.append_assoc]

/-- Create the entire literal word at runtime, preserve both earlier raw banks,
restore home, then enter the literal instruction's actual continuation. -/
theorem literal_push_bits (p : Program) (address n continuation : Nat)
    (h : p[address]?=some (.push n continuation)) (u v : List Bit) :
    run p (literalCost u n) ⟨entry p address,home false u v⟩=
      some ⟨entry p continuation,home false (u++Words.word n) v⟩ := by
  have hp := pool_at p address (.push n continuation) h
  simp only [chunk] at hp
  rw [entry,h]
  exact push_fragment p (pool (p.take address)) (pool (p.drop (address+1))) n continuation u v hp

theorem literal_push_nat (p : Program) (address n continuation : Nat)
    (h : p[address]?=some (.push n continuation)) (data frames : List Nat) :
    run p (literalCost (Words.encode data) n) ⟨entry p address,Words.natBanks data frames⟩=
      some ⟨entry p continuation,Words.natBanks (data++[n]) frames⟩ := by
  simpa [Words.natBanks,Words.encode,List.flatMap_append,home_swap] using
    literal_push_bits p address n continuation h (Words.encode data) (Words.encode frames)

theorem literal_invalid_continuation (p : Program) (address n continuation : Nat)
    (h : p[address]?=some (.push n continuation)) (bad : p.length≤continuation)
    (data frames : List Nat) :
    run p (literalCost (Words.encode data) n) ⟨entry p address,Words.natBanks data frames⟩=
      some ⟨global p 3,Words.natBanks (data++[n]) frames⟩ := by
  rw [literal_push_nat p address n continuation h]
  simp [entry,List.getElem?_eq_none bad]

end CatchUp.Machine.Cases
