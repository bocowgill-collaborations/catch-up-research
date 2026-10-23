import CatchUp.Machine.Call.Control

namespace CatchUp.Machine.Call
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

def opposite : Dir → Dir
  | .left => .right | .right => .left
def reflect {q : Nat} (M : Machine q 2) : Machine q 2 where
  transition s a := (M.transition s a).map fun (w,d,n) ↦ (w,opposite d,n)
def mirrorCfg {q : Nat} (c : Cfg q 2) : Cfg q 2 := ⟨c.state,Separate.mirror c.tape⟩

theorem mirror_twice (T : Tape Bit) : Separate.mirror (Separate.mirror T)=T := by
  cases T
  rfl

theorem mirror_cfg_twice {q : Nat} (c : Cfg q 2) : mirrorCfg (mirrorCfg c)=c := by
  cases c
  simp [mirrorCfg,mirror_twice]

theorem reflect_twice {q : Nat} (M : Machine q 2) : reflect (reflect M)=M := by
  apply congrArg Machine.mk
  funext s a
  cases h : M.transition s a with
  | none => simp [reflect,h]
  | some triple =>
    rcases triple with ⟨w,d,n⟩
    cases d <;> simp [reflect,h,opposite]

theorem reflect_step {q : Nat} (M : Machine q 2) (c : Cfg q 2) :
    step (reflect M) (mirrorCfg c)=(step M c).map mirrorCfg := by
  rcases c with ⟨s,T⟩
  cases h : M.transition s T.head with
  | none => simp [step,reflect,mirrorCfg,Separate.mirror,h]
  | some triple =>
    rcases triple with ⟨w,d,n⟩
    simp [step,reflect,mirrorCfg,Separate.mirror,h]
    cases d <;> rfl

theorem reflect_run {q : Nat} (M : Machine q 2) (n : Nat) (c : Cfg q 2) :
    FlatInit.runFrom (reflect M) n (mirrorCfg c)=
      (FlatInit.runFrom M n c).map mirrorCfg := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [FlatInit.runFrom,reflect_step]
    cases h : step M c with
    | none => simp
    | some mid => simpa [h] using ih mid

theorem mirror_init {q : Nat} [NeZero q] :
    mirrorCfg (ConjectureMachines.init : Cfg q 2)=ConjectureMachines.init := rfl

end CatchUp.Machine.Call
