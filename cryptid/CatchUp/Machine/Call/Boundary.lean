import CatchUp.Machine.Dispatch.Prototype

namespace CatchUp.Machine.Call
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Right-source word contexts cannot return to left-source contexts. -/
def rightContext (state : Fin 3851) : Prop := 1927≤state.val
def afterReturn (state : Fin 3851) : Prop := state=2 ∨ rightContext state

theorem normal_right (c : Fin 8) (old : Fin 460) (hc : 4≤c.val) :
    rightContext (Words.normal c old) := by
  simp only [rightContext,Words.normal]
  omega

theorem bounce_right (c : Fin 8) (attr : Fin 20) (hc : 4≤c.val) :
    rightContext (Words.bounce c attr) := by
  simp only [rightContext,Words.bounce]
  omega

theorem after_right (c : Fin 8) (b : Bit) (hc : 4≤c.val) :
    rightContext (Words.after c b) := by
  have side : Words.side c=true := by simp [Words.side,hc]
  unfold Words.after
  split_ifs <;>
    simp [rightContext,Words.doneState,Words.start,Words.normal,Words.ctx,side] <;> omega

theorem instruction_right (c : Fin 8) (old : Fin 460) (a w : Bit) (d : Dir)
    (next : Fin 3851) (hc : 4≤c.val) (h : Words.instruction c old a=some (w,d,next)) :
    rightContext next := by
  unfold Words.instruction at h
  split at h
  · cases h
    exact normal_right c _ hc
  · dsimp only at h
    split_ifs at h
    cases h
    exact bounce_right c _ hc

theorem right_transition (state next : Fin 3851) (a w : Bit) (d : Dir)
    (hs : rightContext state) (h : Words.machine.transition state a=some (w,d,next)) :
    rightContext next := by
  have large : 3≤state.val := by dsimp [rightContext] at hs;omega
  let c : Fin 8 := ⟨(state.val-3)/481,by have := state.isLt;omega⟩
  let slot := (state.val-3)%481
  have repr : state.val=3+c.val*481+slot := by dsimp [c,slot];omega
  have hc : 4≤c.val := by dsimp [rightContext] at hs;dsimp [c];omega
  have bound : slot<481 := Nat.mod_lt _ (by decide)
  by_cases old : slot<460
  · let q : Fin 460 := ⟨slot,old⟩
    have eq : state=Words.normal c q := by apply Fin.ext;simpa [Words.normal,q] using repr
    rw [eq,Words.normal_transition] at h
    exact instruction_right c q a w d next hc h
  · by_cases mid : slot<480
    · let attr : Fin 20 := ⟨slot-460,by omega⟩
      have eq : state=Words.bounce c attr := by
        apply Fin.ext
        simp only [Words.bounce,attr]
        omega
      rw [eq,Words.bounce_transition] at h
      cases h
      exact after_right c _ hc
    · have eq : state=Words.doneState c := by
        apply Fin.ext
        simp only [Words.doneState]
        omega
      have side : Words.side c=true := by simp [Words.side,hc]
      simp [eq,Words.done_transition,side] at h

theorem after_return_transition (state next : Fin 3851) (a w : Bit) (d : Dir)
    (hs : afterReturn state) (h : Words.machine.transition state a=some (w,d,next)) :
    afterReturn next := by
  rcases hs with hs|hs
  · subst state
    rw [Words.transition_two] at h
    cases h
    exact Or.inr (by change 1927≤(Words.start true false).val;decide)
  · exact Or.inr (right_transition state next a w d hs h)

theorem invariant_run (P : Fin 3851 → Prop)
    (closed : ∀ s n a w d, P s → Words.machine.transition s a=some (w,d,n) → P n)
    (steps : Nat) (old out : Cfg 3851 2) (h : Words.run steps old=some out) (hs : P old.state) :
    P out.state := by
  induction steps generalizing old with
  | zero =>
    simp only [Words.run,FlatInit.runFrom,Option.some.injEq] at h
    subst out
    exact hs
  | succ steps ih =>
    rcases old with ⟨state,T⟩
    cases ht : Words.machine.transition state T.head with
    | none => simp [Words.run,FlatInit.runFrom,step,ht] at h
    | some triple =>
      rcases triple with ⟨w,d,next⟩
      have rest : Words.run steps ⟨next,(T.write w).move d⟩=some out := by
        simpa only [Words.run,FlatInit.runFrom,step,ht,Option.map_some,Option.bind_some] using h
      exact ih _ rest (closed state next T.head w d hs ht)

end CatchUp.Machine.Call
