import CatchUp.Machine.Words.Routines

namespace CatchUp.Machine.Words
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

def nextBit (s started : Bool) (b : Bit) : Fin 3851 :=
  if started && decide (b=0) then doneState (ctx s true started) else start s true

theorem move_bit (s started : Bool) (u v : List Bit) (b : Bit)
    (header : started=false → b=0) :
    run (4*(u.length+v.length)+24) ⟨start s started,home s (u++[b]) v⟩ =
      some ⟨nextBit s started b,home s u (v++[b])⟩ := by
  have hp := run_present (ctx s false started) _ _ _ (Separate.pop_correct s u v b 0 0)
  simp only [Separate.destination,show (0:Fin 5) ≠ 1 by decide,
    show (0:Fin 5) ≠ 2 by decide,show (0:Fin 5) ≠ 3 by decide,
    show (0:Fin 5) ≠ 4 by decide,↓reduceIte,embed] at hp
  have hg : (!pushing (ctx s false started) && !begun (ctx s false started) &&
      decide (b≠0))=false := by cases started <;> simp_all
  have hb := boundary (ctx s false started) s b 0 (home s u v) hg
  simp only [after,ctx_pushing,ctx_side,ctx_begun,Bool.false_eq_true,↓reduceIte] at hb
  rw [home_flip s u v] at hb hp
  have hpush := run_present (ctx s true started) _ _ _ (Separate.push_correct (!s) v u b 0)
  simp only [Separate.destination,show (0:Fin 5) ≠ 1 by decide,
    show (0:Fin 5) ≠ 2 by decide,show (0:Fin 5) ≠ 3 by decide,
    show (0:Fin 5) ≠ 4 by decide,↓reduceIte,embed] at hpush
  have he := boundary (ctx s true started) (!s) b 0 (home (!s) (v++[b]) u) (by simp)
  simp only [after,ctx_pushing,ctx_side,ctx_begun,↓reduceIte] at he
  rw [home_flip (!s) (v++[b]) u] at he
  rw [home_flip (!s) (v++[b]) u] at hpush
  simp only [Bool.not_not] at he hpush
  simp only [start]
  rw [show 4*(u.length+v.length)+24 = (4*u.length+12)+(2+((4*v.length+8)+2)) by omega,
    run_add,hp,Option.bind_some,run_add,hb,Option.bind_some,run_add,hpush,Option.bind_some]
  exact he

theorem ones_loop (s : Bool) (u v : List Bit) (n : Nat) :
    run ((n+1)*(4*(u.length+v.length+n)+24))
      ⟨start s true,home s (u++[0]++List.replicate n 1) v⟩ =
      some ⟨doneState (ctx s true true),home s u (v++List.replicate n 1++[0])⟩ := by
  induction n generalizing v with
  | zero => simpa [nextBit] using move_bit s true u v 0 (by simp)
  | succ n ih =>
    let cost := 4*(u.length+v.length+(n+1))+24
    have first : run cost ⟨start s true,home s (u++[0]++List.replicate (n+1) 1) v⟩ =
        some ⟨start s true,home s (u++[0]++List.replicate n 1) (v++[1])⟩ := by
      convert move_bit s true (u++[0]++List.replicate n 1) v 1 (by simp) using 1 <;>
        simp [cost,nextBit,List.replicate_succ',List.append_assoc,
          Nat.add_assoc,Nat.add_comm]
    have rest : run ((n+1)*cost)
        ⟨start s true,home s (u++[0]++List.replicate n 1) (v++[1])⟩ =
        some ⟨doneState (ctx s true true),home s u (v++List.replicate (n+1) 1++[0])⟩ := by
      convert ih (v++[1]) using 1 <;>
        simp [cost,List.replicate_succ,List.append_assoc,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    change run ((n+1+1)*cost) _ = _
    rw [show (n+1+1)*cost=cost+(n+1)*cost by ring,run_add,first,Option.bind_some]
    exact rest

def transferCost (u v : List Bit) (n : Nat) : Nat :=
  (n+2)*(4*(u.length+v.length+n+1)+24)

/-- Move one complete framed natural word to the opposite bank. Both
prefixes are arbitrary bit lists; word-stack well-formedness is not needed. -/
theorem word_transfer (s : Bool) (u v : List Bit) (n : Nat) :
    run (transferCost u v n) ⟨start s false,home s (u++word n) v⟩ =
      some ⟨doneState (ctx s true true),home s u (v++word n)⟩ := by
  let cost := 4*(u.length+v.length+n+1)+24
  have first : run cost ⟨start s false,home s (u++word n) v⟩ =
      some ⟨start s true,home s (u++[0]++List.replicate n 1) (v++[0])⟩ := by
    convert move_bit s false (u++[0]++List.replicate n 1) v 0 (by simp) using 1 <;>
      simp [cost,word,nextBit,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  have rest : run ((n+1)*cost)
      ⟨start s true,home s (u++[0]++List.replicate n 1) (v++[0])⟩ =
      some ⟨doneState (ctx s true true),home s u (v++word n)⟩ := by
    convert ones_loop s u (v++[0]) n using 1 <;>
      simp [cost,word,List.append_assoc,Nat.add_comm,Nat.add_left_comm]
  change run ((n+2)*cost) _ = _
  rw [show (n+2)*cost=cost+(n+1)*cost by ring,run_add,first,Option.bind_some]
  exact rest

end CatchUp.Machine.Words
