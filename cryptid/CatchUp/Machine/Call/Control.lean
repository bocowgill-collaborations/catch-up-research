import CatchUp.Machine.Call.Boundary

namespace CatchUp.Machine.Call
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

inductive Instruction where
  | halt | call | ret
  deriving DecidableEq, Repr

def Instruction.lower : Instruction → Dispatch.Instruction
  | .halt => .halt | .call => .push | .ret => .ret
abbrev Program := List Instruction
def base (p : Program) : Dispatch.Program := p.map Instruction.lower
abbrev states (p : Program) := Dispatch.states (base p).length
abbrev wordState (p : Program) := Dispatch.wordState (base p).length
abbrev global (p : Program) := Dispatch.global (base p).length
abbrev readStart (p : Program) := Dispatch.readStart (base p).length
def entry (p : Program) (op : Option Instruction) : Fin (states p) :=
  Dispatch.entry (base p).length (op.map Instruction.lower)

/-- Two old rows are retargeted. Word control 2 dispatches the target after
save instead of immediately returning; boot control 1 enters a general call.
Every allocated control remains paid, with no new uncounted dispatch state. -/
def machine (p : Program) : Machine (states p) 2 where
  transition state a :=
    if state=wordState p 2 then some (a,.left,readStart p 0)
    else if state=global p 1 then some (a,.left,wordState p (Words.start false false))
    else (Dispatch.machine (base p)).transition state a

abbrev run (p : Program) := FlatInit.runFrom (machine p)
def wordEmbed (p : Program) (c : Cfg 3851 2) : Cfg (states p) 2 :=
  ⟨wordState p c.state,c.tape⟩
def bitEmbed (p : Program) (phase : Fin ((base p).length+2)) (c : Cfg 460 2) :
    Cfg (states p) 2 := ⟨Dispatch.normal (base p).length phase c.state,c.tape⟩

theorem base_length (p : Program) : (base p).length=p.length := by simp [base]
theorem base_get (p : Program) (address : Nat) :
    (base p)[address]?=(p[address]?).map Instruction.lower := by simp [base]

theorem word_ne_global (p : Program) (old : Fin 3851) (q : Fin 5) :
    wordState p old≠global p q := by
  intro h
  have hval := congrArg Fin.val h
  simp only [wordState,global,Dispatch.word_value,Dispatch.global_value] at hval
  have := q.isLt
  omega

theorem word_injective (p : Program) : Function.Injective (wordState p) := by
  intro a b h
  have hval := congrArg Fin.val h
  simp only [wordState,Dispatch.word_value] at hval
  apply Fin.ext
  omega

theorem word_transition (p : Program) (old : Fin 3851) (a : Bit) (h : old≠2) :
    (machine p).transition (wordState p old) a =
      (Dispatch.machine (base p)).transition (wordState p old) a := by
  have neq : wordState p old≠wordState p 2 := fun eq ↦ h (word_injective p eq)
  simp [machine,neq,word_ne_global]

theorem bit_transition (p : Program) (phase : Fin ((base p).length+2))
    (old : Fin 460) (a : Bit) :
    (machine p).transition (Dispatch.normal (base p).length phase old) a =
      Dispatch.oldInstruction (base p) phase old a := by
  have localVal : (Dispatch.normal (base p).length phase old).val =
      3856+phase.val*480+old.val := Dispatch.local_value _ phase _
  have neq : Dispatch.normal (base p).length phase old≠wordState p 2 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [wordState,Dispatch.word_value] at hv
    omega
  have boot : Dispatch.normal (base p).length phase old≠global p 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [global,Dispatch.global_value] at hv
    omega
  simp [machine,neq,boot,Dispatch.normal_transition]

theorem bounce_transition (p : Program) (phase : Fin ((base p).length+2))
    (attr : Fin 20) (a : Bit) :
    (machine p).transition (Dispatch.bounce (base p).length phase attr) a =
      some (a,.left,Dispatch.after (base p) phase (Words.attrs.symm attr).2.1) := by
  have localVal : (Dispatch.bounce (base p).length phase attr).val =
      3856+phase.val*480+(460+attr.val) := Dispatch.local_value _ phase _
  have neq : Dispatch.bounce (base p).length phase attr≠wordState p 2 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [wordState,Dispatch.word_value] at hv
    omega
  have boot : Dispatch.bounce (base p).length phase attr≠global p 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [global,Dispatch.global_value] at hv
    omega
  simp [machine,neq,boot,Dispatch.bounce_transition]

theorem word_two (p : Program) (a : Bit) :
    (machine p).transition (wordState p 2) a=some (a,.left,readStart p 0) := by
  simp [machine]

theorem global_transition (p : Program) (q : Fin 5) (a : Bit) :
    (machine p).transition (global p q) a =
      if q=0 then some (a,.right,global p 1)
      else if q=1 then some (a,.left,wordState p (Words.start false false))
      else if q=2 then some (a,.left,readStart p 0) else none := by
  have neq : global p q≠wordState p 2 := (word_ne_global p 2 q).symm
  have eqiff : (global p q=global p 1) ↔ q=1 := by
    constructor
    · intro h
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa only [global,Dispatch.global_value] using hv
    · exact congrArg (global p)
  simp only [machine,neq,↓reduceIte,eqiff]
  by_cases hq : q=1 <;> simp [hq,global,Dispatch.global_transition]

end CatchUp.Machine.Call
