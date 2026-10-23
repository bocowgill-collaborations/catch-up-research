import CatchUp.Machine.Lowering.Switch.Extract

namespace CatchUp.Machine.Lowering.Switch.Entrance
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 16000000

/-- After the left-word return, the old primitive enters right-hand contexts
and cannot reach that return again. This is a finite control invariant. -/
def RightControl (q : Fin 3851) : Prop := q.val=2 ∨ 1927 ≤ q.val

instance (q : Fin 3851) : Decidable (RightControl q) := inferInstanceAs
  (Decidable (q.val=2 ∨ 1927 ≤ q.val))

def rightCheck (q : Fin 3851) (a : Bit) : Bool :=
  if RightControl q then
    match Words.machine.transition q a with
    | none => true
    | some (_,_,out) => decide (RightControl out)
  else true

theorem right_checks :
    (List.finRange 3851).all (fun q ↦ (List.finRange 2).all (rightCheck q))=true := by
  decide +kernel

theorem right_closed (q : Fin 3851) (a : Bit) (h : RightControl q) :
    match Words.machine.transition q a with
    | none => True
    | some (_,_,out) => RightControl out := by
  have all := List.all_eq_true.mp right_checks q (List.mem_finRange q)
  have one := List.all_eq_true.mp all a (List.mem_finRange a)
  simp only [rightCheck,h,↓reduceIte] at one
  cases ht : Words.machine.transition q a with
  | none => trivial
  | some triple => simpa only [ht,decide_eq_true_eq] using one

theorem right_run (n : Nat) (c out : Cfg 3851 2) (hc : RightControl c.state)
    (h : Words.run n c=some out) : RightControl out.state := by
  induction n generalizing c with
  | zero =>
    have eq : c=out := Option.some.inj h
    simpa only [←eq] using hc
  | succ n ih =>
    cases ht : Words.machine.transition c.state c.tape.head with
    | none => simp [FlatInit.runFrom,ConjectureMachines.step,ht] at h
    | some triple =>
      rcases triple with ⟨w,d,q⟩
      have next : RightControl q := by simpa only [ht] using right_closed c.state c.tape.head hc
      simp only [FlatInit.runFrom,ConjectureMachines.step,ht,Option.map_some,
        Option.bind_some] at h
      exact ih _ next h

/-- A run ending at the left-word return cannot have executed its old outgoing
instruction. Thus only successful transitions away from other states are needed. -/
theorem left_prefix_present (m : Micro) (offset : Nat)
    (hc : ∀ (q out : Fin 3851) (a w : Bit) (d : Dir), q.val≠1926 →
      Words.machine.transition q a=some (w,d,out) →
      m.cell (offset+q.val) a=some (w,d,Int.ofNat (offset+out.val)))
    (n : Nat) (c : Cfg 3851 2) (T : Tape Bit)
    (h : Words.run n c=some ⟨(⟨1926,by decide⟩ : Fin 3851),T⟩) :
    run m n (embedControl offset c)=
      some (embedControl offset ⟨(⟨1926,by decide⟩ : Fin 3851),T⟩) := by
  induction n generalizing c with
  | zero =>
    simpa only [FlatInit.runFrom,run,Option.map_some] using
      congrArg (Option.map (embedControl offset)) h
  | succ n ih =>
    have hq : c.state.val≠1926 := by
      intro he
      have eq : c.state=⟨1926,by decide⟩ := Fin.ext he
      have ht : Words.machine.transition c.state c.tape.head=some (c.tape.head,.right,2) := by
        rw [eq];rfl
      simp only [FlatInit.runFrom,ConjectureMachines.step,ht,Option.map_some,
        Option.bind_some] at h
      have impossible := right_run n _ _ (Or.inl rfl) h
      simp [RightControl] at impossible
    cases ht : ConjectureMachines.step Words.machine c with
    | none => simp [FlatInit.runFrom,ht] at h
    | some mid =>
      have rest : Words.run n mid=some ⟨(⟨1926,by decide⟩ : Fin 3851),T⟩ := by
        simpa only [FlatInit.runFrom,ht,Option.bind_some] using h
      have hs : step m (embedControl offset c)=some (embedControl offset mid) := by
        cases he : Words.machine.transition c.state c.tape.head with
        | none => simp [ConjectureMachines.step,he] at ht
        | some triple =>
          rcases triple with ⟨w,d,q⟩
          simp only [ConjectureMachines.step,he,Option.map_some,Option.some.injEq] at ht
          subst mid
          simp only [step,embedControl]
          rw [Int.ofNat_eq_natCast,ite_eq_right (by omega)]
          change (m.cell (offset+c.state.val) c.tape.head).map _ = _
          rw [hc _ _ _ _ _ hq he]
          rfl
      rw [run,hs,Option.bind_some]
      exact ih mid rest

end CatchUp.Machine.Lowering.Switch.Entrance
