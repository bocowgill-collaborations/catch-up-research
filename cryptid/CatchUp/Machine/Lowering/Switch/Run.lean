import CatchUp.Machine.Lowering.Library

/-! Execution of the existing finite binary templates. Integer -1 is their
external exit port. No new controller or table is introduced in this file. -/
namespace CatchUp.Machine.Lowering.Switch
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

abbrev Config := Int × Tape Bit

def step (m : Micro) (c : Config) : Option Config :=
  if c.1<0 then none else
    (m.cell c.1.toNat c.2.head).map fun (w,d,q) ↦ (q,(c.2.write w).move d)

def run (m : Micro) : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step m c).bind (run m n)

theorem run_add (m : Micro) (n k : Nat) (c : Config) :
    run m (n+k) c=(run m n c).bind (run m k) := by
  induction n generalizing c with
  | zero => simp only [Nat.zero_add,run,Option.bind_some]
  | succ n ih => simp only [Nat.succ_add,run,ih,Option.bind_assoc]

theorem cells_skip (pre post : List Segment) (offset q : Nat) (a : Bit) :
    cells (pre++post) offset ((pre.map Segment.size).sum+q) a =
      cells post (offset+(pre.map Segment.size).sum) q a := by
  induction pre generalizing offset with
  | nil => simp only [List.nil_append,List.map_nil,List.sum_nil,Nat.zero_add,Nat.add_zero]
  | cons s pre ih =>
    simp only [List.cons_append,List.map_cons,List.sum_cons]
    rw [cells,ite_eq_right (by omega)]
    convert ih (offset+s.size) using 1 <;> congr 1 <;> omega

theorem cell_in (m : Micro) (pre post : List Segment) (s : Segment)
    (h : m.segments=pre++s::post) (q : Nat) (hq : q<s.size) (a : Bit) :
    m.cell ((pre.map Segment.size).sum+q) a =
      s.cell (pre.map Segment.size).sum q a := by
  rw [Micro.cell,h,cells_skip]
  simp only [Nat.zero_add,cells,hq,ite_eq_left]

def embedControl {n : Nat} (offset : Nat) (c : Cfg n 2) : Config :=
  (Int.ofNat (offset+c.state.val),c.tape)

theorem word_present (m : Micro) (offset next : Nat)
    (hc : ∀ (q : Fin 3851) (a : Bit), m.cell (offset+q.val) a=
      (Segment.word 3850 next).cell offset q.val a)
    (q out : Fin 3851) (a w : Bit) (d : Dir)
    (h : Words.machine.transition q a=some (w,d,out)) :
    m.cell (offset+q.val) a=some (w,d,Int.ofNat (offset+out.val)) := by
  rw [hc]
  by_cases he : q.val=3850
  · have eq : q=⟨3850,by decide⟩ := Fin.ext he
    subst q
    have stop : Words.machine.transition ⟨3850,by decide⟩ a=none := rfl
    rw [stop] at h
    cases h
  · simp only [Segment.cell,he,q.isLt,↓reduceIte,↓reduceDIte,h,Option.map_some]

theorem step_present {n : Nat} (old : Machine n 2) (m : Micro) (offset : Nat)
    (hc : ∀ (q out : Fin n) (a w : Bit) (d : Dir),
      old.transition q a=some (w,d,out) →
      m.cell (offset+q.val) a=some (w,d,Int.ofNat (offset+out.val)))
    (c out : Cfg n 2) (h : ConjectureMachines.step old c=some out) :
    step m (embedControl offset c)=some (embedControl offset out) := by
  rcases c with ⟨q,T⟩
  cases ht : old.transition q T.head with
  | none => simp [ConjectureMachines.step,ht] at h
  | some triple =>
    rcases triple with ⟨w,d,target⟩
    simp only [ConjectureMachines.step,ht,Option.map_some,Option.some.injEq] at h
    subst out
    simp only [step,embedControl]
    rw [Int.ofNat_eq_natCast,ite_eq_right (by omega)]
    change (m.cell (offset+q.val) T.head).map _ = _
    rw [hc q target T.head w d ht]
    rfl

theorem run_present {n : Nat} (old : Machine n 2) (m : Micro) (offset : Nat)
    (hc : ∀ (q out : Fin n) (a w : Bit) (d : Dir),
      old.transition q a=some (w,d,out) →
      m.cell (offset+q.val) a=some (w,d,Int.ofNat (offset+out.val)))
    (steps : Nat) (c out : Cfg n 2)
    (h : FlatInit.runFrom old steps c=some out) :
    run m steps (embedControl offset c)=some (embedControl offset out) := by
  induction steps generalizing c with
  | zero => simpa [FlatInit.runFrom,run] using congrArg (Option.map (embedControl offset)) h
  | succ steps ih =>
    cases ht : ConjectureMachines.step old c with
    | none => simp [FlatInit.runFrom,ht] at h
    | some mid =>
      have rest : FlatInit.runFrom old steps mid=some out := by
        simpa only [FlatInit.runFrom,ht,Option.bind_some] using h
      rw [run,step_present old m offset hc c mid ht,Option.bind_some]
      exact ih mid rest

theorem bit_present (m : Micro) (offset z o : Nat) (empty : Option Nat)
    (hc : ∀ (q : Fin 460) (a : Bit), m.cell (offset+q.val) a=
      (Segment.bit z o empty).cell offset q.val a)
    (q out : Fin 460) (a w : Bit) (d : Dir)
    (h : Separate.machine.transition q a=some (w,d,out)) :
    m.cell (offset+q.val) a=some (w,d,Int.ofNat (offset+out.val)) := by
  rw [hc]
  simp only [Segment.cell,q.isLt,↓reduceDIte,h]

theorem bounce (m : Micro) (first mid dest : Nat)
    (hfirst : ∀ a, m.cell first a=some (a,.right,Int.ofNat mid))
    (hmid : ∀ a, m.cell mid a=some (a,.left,Int.ofNat dest)) (T : Tape Bit) :
    run m 2 ((first : Int),T)=some ((dest : Int),T) := by
  have hf : ¬(first : Int)<0 := by omega
  have hm : ¬(mid : Int)<0 := by omega
  simp [run,step,hfirst,hmid,Int.ofNat_eq_natCast,hf,hm]

theorem run_chain (m : Micro) {n k : Nat} {first mid last : Config}
    (hfirst : run m n first=some mid) (hlast : run m k mid=some last) :
    run m (n+k) first=some last := by
  rw [run_add,hfirst,Option.bind_some,hlast]

end CatchUp.Machine.Lowering.Switch
