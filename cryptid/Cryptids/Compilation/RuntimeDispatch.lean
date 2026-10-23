/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.RuntimeData

/-! # Exact instruction and return-tag dispatch -/

@[expose] public section
namespace ConjectureMachines.Compilation.Runtime
open Turing PartrecToTM2 K' StateTransition Relation Function

set_option backward.isDefEq.respectTransparency false

def opcodePhase (tag : Nat) : Phase := codePhase (6 + tag)

def returnPhase : Nat → Phase
  | 0 => .halt | 1 => .cons1 | 2 => .cons2 | 3 => .comp1 | _ => .fix1

theorem dispatch_reaches (tag : Nat) (values table : List Nat) (frames : List Γ')
    (store : Option Γ') (bound : tag < 7) :
    ∃ resultStore, Reaches₁ (TM2.step machine)
      (dataCfg .dispatch store (tag :: values) table frames)
      (dataCfg (opcodePhase tag) resultStore values table frames) := by
  let choices := [label .zero, label .successor, label .tail, label .cons,
    label .comp, label .branch, label .fix]
  have hb : tag < choices.length := bound
  obtain ⟨resultStore, run⟩ := choose_reaches choices (label .invalid) tag values
    (trList table) frames store hb
  have selected : choices[tag] = label (opcodePhase tag) := by
    interval_cases tag <;> rfl
  refine ⟨resultStore, (phase_reaches .dispatch store _ (by decide)).trans ?_⟩
  simpa only [StateTransition.Reaches₁, dataCfg, entry, selected, choices] using run

theorem return_dispatch_reaches (tag : Nat) (values table : List Nat)
    (suffix : List Γ') (store : Option Γ') (bound : tag < 5) :
    ∃ resultStore, Reaches₁ (TM2.step machine)
      (dataCfg .returned store values table (trList [tag] ++ suffix))
      (dataCfg (returnPhase tag) resultStore values table suffix) := by
  let choices := [label .halt, label .cons1, label .cons2, label .comp1, label .fix1]
  let next := choose choices (label .invalid)
  have moved := moveWord_reaches stack main next store
    (K'.elim (trList values) [] (trList table) (trList [tag] ++ suffix)) tag suffix
    (by decide) (by decide) (by decide) rfl (by simp [trList])
  have moved' : Reaches₁ (TM2.step machine)
      ⟨some (moveWord stack main next), store,
        K'.elim (trList values) [] (trList table) (trList [tag] ++ suffix)⟩
      ⟨some next, none, K'.elim (trList (tag :: values)) [] (trList table) suffix⟩ := by
    convert moved using 2
    funext k
    cases k <;> simp [trList, List.append_assoc]
  have hb : tag < choices.length := bound
  obtain ⟨resultStore, run⟩ := choose_reaches choices (label .invalid) tag values
    (trList table) suffix none hb
  have selected : choices[tag] = label (returnPhase tag) := by
    interval_cases tag <;> rfl
  refine ⟨resultStore, (phase_reaches .returned store _ (by decide)).trans
    (moved'.trans ?_)⟩
  simpa only [StateTransition.Reaches₁, dataCfg, selected, choices, next] using run

end ConjectureMachines.Compilation.Runtime
