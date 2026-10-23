import CatchUp.Machine.Lowering.Switch.Restore

/-! A finite-machine view of the unchanged switch table. The extra local state
is its external return port, not a new control in the full candidate. -/
namespace CatchUp.Machine.Lowering.Switch
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem cells_past (ss : List Segment) (offset q : Nat) (a : Bit)
    (h : (ss.map Segment.size).sum≤q) : cells ss offset q a=none := by
  induction ss generalizing offset q with
  | nil => rfl
  | cons s ss ih =>
    rw [cells,ite_eq_right (by simp only [List.map_cons,List.sum_cons] at h;omega)]
    apply ih
    simp only [List.map_cons,List.sum_cons] at h
    omega

def stateOf (m : Micro) (q : Int) : Fin (m.size+1) :=
  if h : 0≤q ∧ q.toNat< m.size then ⟨q.toNat,by omega⟩ else ⟨m.size,by omega⟩

def binary (m : Micro) : Machine (m.size+1) 2 where
  transition q a := if q.val< m.size then
    (m.cell q.val a).map (fun (w,d,target) ↦ (w,d,stateOf m target)) else none

def embed (m : Micro) (c : Config) : Cfg (m.size+1) 2 := ⟨stateOf m c.1,c.2⟩

theorem binary_step (m : Micro) (c : Config) :
    ConjectureMachines.step (binary m) (embed m c)=(step m c).map (embed m) := by
  rcases c with ⟨q,T⟩
  by_cases hn : q<0
  · have hnon : ¬0≤q := by omega
    simp [ConjectureMachines.step,binary,embed,stateOf,step,hn,hnon]
  · by_cases hb : q.toNat< m.size
    · have hnon : 0≤q := by omega
      simp [ConjectureMachines.step,binary,embed,stateOf,step,hn,hb,hnon,
        Option.map_map,Function.comp_def]
    · have hcell : m.cell q.toNat T.head=none :=
        cells_past m.segments 0 q.toNat T.head
          (by simpa only [Micro.size] using Nat.le_of_not_lt hb)
      simp [ConjectureMachines.step,binary,embed,stateOf,step,hn,hb,hcell]

theorem binary_run (m : Micro) (n : Nat) (c : Config) :
    FlatInit.runFrom (binary m) n (embed m c)=(run m n c).map (embed m) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [FlatInit.runFrom,run,binary_step]
    cases h : step m c with
    | none => simp only [Option.map_none,Option.bind_none]
    | some mid => simpa only [h,Option.map_some,Option.bind_some] using ih mid

/-- The finite binary restore loop preserves arbitrary bit prefixes on both
banks, not just well-formed natural-number stacks. -/
theorem binary_restore_input (original : List Nat) (data frames : List Bit) :
    ∃ steps, FlatInit.runFrom (binary switchBody) steps
      ⟨⟨6742,by decide +kernel⟩,banks data (frames++savedPayload original)⟩=
      some ⟨⟨1395,by decide +kernel⟩,banks (data++encode original) frames⟩ := by
  change ∃ steps, FlatInit.runFrom (binary switchBody) steps
    (embed switchBody (6742,banks data (frames++savedPayload original)))=
    some (embed switchBody (1395,banks (data++encode original) frames))
  obtain ⟨steps,h⟩ := restore_input original data frames
  refine ⟨steps,?_⟩
  rw [binary_run,h]
  rfl

/-- A finite binary Turing-machine theorem for the actual restore-loop table,
including arbitrary saved-input length, naturals and caller-frame depth. The
next state is the real extraction entry, not the switch return port. -/
theorem binary_restore_retained_head (original frames : List Nat) (retained : Nat) :
    ∃ steps, FlatInit.runFrom (binary switchBody) steps
      ⟨⟨6742,by decide +kernel⟩,natBanks [retained] (frames++savedFrames original)⟩=
      some ⟨⟨1395,by decide +kernel⟩,natBanks (retained::original) frames⟩ := by
  change ∃ steps, FlatInit.runFrom (binary switchBody) steps
    (embed switchBody (6742,natBanks [retained] (frames++savedFrames original)))=
    some (embed switchBody (1395,natBanks (retained::original) frames))
  obtain ⟨steps,h⟩ := restore_retained_head original frames retained
  refine ⟨steps,?_⟩
  rw [binary_run,h]
  rfl

end CatchUp.Machine.Lowering.Switch
