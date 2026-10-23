import CatchUp.Machine.Succ.Arithmetic

namespace CatchUp.Machine.Succ
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev body (p : Program) : BundledMachine 2 := ⟨states p,machine p⟩
abbrev reflectedBody (p : Program) : BundledMachine 2 := ⟨states p,Call.reflect (machine p)⟩
def inputBits (data : List Nat) : Array Bit := (0::0::wire (Words.encode data)).toArray
abbrev raw (p : Program) (data : List Nat) := FlatInit.initialise (inputBits data) (reflectedBody p)

/-- Mirror the existing paid writer and mirrored body. The writer emits left
data and returns home; the running body is unmirrored. All frames start empty. -/
def generated (p : Program) (data : List Nat) : BundledMachine 2 :=
  ⟨(raw p data).states,Call.reflect (raw p data).toMachine⟩

def embed (p : Program) (data : List Nat) (c : Cfg (states p) 2) : Cfg (generated p data).states 2 :=
  Call.mirrorCfg (FlatInit.embed (inputBits data) (reflectedBody p) (Call.mirrorCfg c))

theorem input_size (data : List Nat) : (inputBits data).size=2+2*(Words.encode data).length := by
  simp [inputBits,Words.wire_length]
  omega

theorem state_count (p : Program) (data : List Nat) :
    (generated p data).states=480*p.length+4*(Words.encode data).length+6206 := by
  change (raw p data).states=_
  rw [FlatInit.initialise_states,input_size]
  change ((5+(3851+((Call.base (base p)).length+2)*480))+1386)+
    2*(2+2*(Words.encode data).length)=_
  rw [base_length]
  ring

theorem input_tape (data : List Nat) :
    Separate.mirror (Tape.mk₁ (inputBits data).toList)=Words.natBanks data [] := by
  simp [inputBits,Words.natBanks,Words.encode,banks,home,view,Separate.mirror,
    Tape.mk₁,Tape.mk₂,Tape.mk']

theorem initializes (p : Program) (data : List Nat) :
    FlatInit.runFrom (generated p data).toMachine (4+4*(Words.encode data).length)
      ConjectureMachines.init = some (embed p data ⟨0,Words.natBanks data []⟩) := by
  have h := FlatInit.initialise_run (inputBits data) (reflectedBody p)
  have hm := Call.reflect_run (raw p data).toMachine (2*(inputBits data).size) ConjectureMachines.init
  rw [Call.mirror_init,h,Option.map_some] at hm
  have count : 2*(inputBits data).size=4+4*(Words.encode data).length := by rw [input_size];omega
  conv at hm => lhs;arg 2;rw [count]
  change FlatInit.runFrom (generated p data).toMachine _ ConjectureMachines.init =
    some ⟨FlatInit.bodyState (inputBits data) (reflectedBody p) 0,
      Separate.mirror (Tape.mk₁ (inputBits data).toList)⟩ at hm
  rw [input_tape] at hm
  exact hm

theorem step_embed (p : Program) (data : List Nat) (c : Cfg (states p) 2) :
    step (generated p data).toMachine (embed p data c)=(step (machine p) c).map (embed p data) := by
  change step (Call.reflect (FlatInit.machine (inputBits data) (reflectedBody p)))
    (Call.mirrorCfg (FlatInit.embed (inputBits data) (reflectedBody p) (Call.mirrorCfg c)))=_
  rw [Call.reflect_step,FlatInit.step_embed]
  change ((step (Call.reflect (machine p)) (Call.mirrorCfg c)).map
    (FlatInit.embed (inputBits data) (reflectedBody p))).map Call.mirrorCfg=_
  rw [Call.reflect_step]
  simp only [Option.map_map]
  rfl

theorem run_embed (p : Program) (data : List Nat) (steps : Nat) (c : Cfg (states p) 2) :
    FlatInit.runFrom (generated p data).toMachine steps (embed p data c)=
      (run p steps c).map (embed p data) := by
  induction steps generalizing c with
  | zero => rfl
  | succ steps ih =>
    simp only [FlatInit.runFrom,step_embed]
    cases h : step (machine p) c with
    | none => simp
    | some mid => simpa [h,run,FlatInit.runFrom] using ih mid

theorem full_add (p : Program) (data : List Nat) (m n : Nat) (c : Cfg (generated p data).states 2) :
    FlatInit.runFrom (generated p data).toMachine (m+n) c =
      (FlatInit.runFrom (generated p data).toMachine m c).bind
        (FlatInit.runFrom (generated p data).toMachine n) := by
  induction m generalizing c with
  | zero => simp [FlatInit.runFrom]
  | succ m ih => simp only [Nat.succ_add,FlatInit.runFrom,ih,Option.bind_assoc]

end CatchUp.Machine.Succ
