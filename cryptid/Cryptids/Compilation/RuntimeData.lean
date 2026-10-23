/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.Runtime
public import Cryptids.Compilation.RuntimeMacros

/-! # Data-preserving interpreter subroutines -/

@[expose] public section
namespace ConjectureMachines.Compilation.Runtime
open Turing PartrecToTM2 K' StateTransition Relation Function

set_option backward.isDefEq.respectTransparency false

theorem agrees : RuntimeMacros.Agrees machine := by
  intro q hq
  cases q <;> simp_all [RuntimeMacros.NonRet, machine]

/-- Stable macro boundaries: reverse scratch empty, with arbitrary return-frame symbols. -/
def dataCfg (phase : Phase) (store : Option Γ') (values table : List Nat)
    (frames : List Γ') : Cfg' :=
  ⟨some (label phase), store, K'.elim (trList values) [] (trList table) frames⟩

theorem trList_append (first second : List Nat) :
    trList (first ++ second) = trList first ++ trList second := by
  induction first with
  | nil => rfl
  | cons n rest ih => simp [trList, ih, List.append_assoc]

theorem phase_step (phase : Phase) (store : Option Γ') (S : K' → List Γ')
    (live : phase ≠ .halt) :
    TM2.step machine ⟨some (label phase), store, S⟩ =
      some ⟨some (entry phase), store, S⟩ := by
  simp [TM2.step, machine, label, returnNumber_returnCode, codePhase_phaseCode,
    live, TM2.stepAux]

theorem phase_reaches (phase : Phase) (store : Option Γ') (S : K' → List Γ')
    (live : phase ≠ .halt) :
    Reaches₁ (TM2.step machine) ⟨some (label phase), store, S⟩
      ⟨some (entry phase), store, S⟩ := .single (phase_step phase store S live)

theorem pushSymbols_reaches (dst : K') (symbols : List Γ') (next : Λ')
    (store : Option Γ') (S : K' → List Γ') :
    Reaches (TM2.step machine) ⟨some (pushSymbols dst symbols next), store, S⟩
      ⟨some next, store, update S dst (symbols ++ S dst)⟩ := by
  induction symbols using List.reverseRecOn generalizing next S with
  | nil => simp only [pushSymbols, List.foldl_nil, List.nil_append, update_eq_self]; exact .refl
  | append_singleton symbols symbol ih =>
    simp only [pushSymbols, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change ReflTransGen _ _ _
    have first := RuntimeMacros.push_ok agrees dst symbol
      (pushSymbols dst symbols next) store S
    have rest := ih next (update S dst (symbol :: S dst))
    simpa only [StateTransition.Reaches, pushSymbols, update_self, update_idem, List.append_assoc,
      List.singleton_append] using first.to_reflTransGen.trans rest

theorem pushWord_reaches (dst : K') (n : Nat) (next : Λ')
    (store : Option Γ') (S : K' → List Γ') :
    Reaches (TM2.step machine) ⟨some (pushWord dst n next), store, S⟩
      ⟨some next, store, update S dst (trList [n] ++ S dst)⟩ :=
  pushSymbols_reaches dst (trList [n]) next store S

theorem moveWord_reaches (src dst : K') (next : Λ') (store : Option Γ')
    (S : K' → List Γ') (n : Nat) (suffix : List Γ')
    (hsrc : src ≠ rev) (hdst : dst ≠ rev) (hne : src ≠ dst)
    (hrev : S rev = []) (hword : S src = trNat n ++ Γ'.cons :: suffix) :
    Reaches₁ (TM2.step machine) ⟨some (moveWord src dst next), store, S⟩
      ⟨some next, none, update (update S src suffix) dst (trList [n] ++ S dst)⟩ := by
  exact RuntimeMacros.moveWord_ok agrees src dst next store S n suffix
    hsrc hdst hne hrev hword

theorem copyWord_reaches (src : K') (next : Λ') (store : Option Γ')
    (S : K' → List Γ') (n : Nat) (suffix : List Γ') (hsrc : src ≠ rev)
    (hrev : S rev = []) (hword : S src = trNat n ++ Γ'.cons :: suffix) :
    Reaches₁ (TM2.step machine) ⟨some (copyWord src next), store, S⟩
      ⟨some next, none,
        update (update (update S src suffix) main
          (trList [n] ++ (update S src suffix) main)) stack
          (trList [n] ++ (update S src suffix) stack)⟩ :=
  RuntimeMacros.copyWord_ok agrees src next store S n suffix hsrc hrev hword

/-- Dispatch consumes the natural tag, including all intermediate predecessor values. -/
theorem choose_reaches (choices : List Λ') (fallback : Λ') (n : Nat)
    (values : List Nat) (table frames : List Γ') (store : Option Γ')
    (bound : n < choices.length) :
    ∃ resultStore, Reaches₁ (TM2.step machine)
      ⟨some (choose choices fallback), store, K'.elim (trList (n :: values)) [] table frames⟩
      ⟨some choices[n], resultStore, K'.elim (trList values) [] table frames⟩ := by
  induction choices generalizing n store with
  | nil => simp at bound
  | cons first rest ih =>
    cases n with
    | zero =>
      obtain ⟨resultStore, run⟩ := RuntimeMacros.pred_ok agrees first (choose rest fallback)
        store (0 :: values) table frames
      exact ⟨resultStore, run⟩
    | succ n =>
      obtain ⟨middleStore, run⟩ := RuntimeMacros.pred_ok agrees first (choose rest fallback)
        store ((n + 1) :: values) table frames
      obtain ⟨resultStore, finish⟩ := ih n middleStore (by simpa using bound)
      exact ⟨resultStore, run.trans finish⟩

end ConjectureMachines.Compilation.Runtime
