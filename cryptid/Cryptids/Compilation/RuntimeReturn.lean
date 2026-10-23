/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.RuntimeData

/-! # Exact return-body boundaries of the fixed interpreter

Return tags have already been consumed at these boundaries. Source addresses,
saved values and older continuation symbols remain tape data throughout.
-/

@[expose] public section

namespace ConjectureMachines.Compilation.Runtime

open Turing PartrecToTM2 K' StateTransition Relation Function

set_option backward.isDefEq.respectTransparency false

/-- Consume one complete delimited word, retaining its suffix exactly. -/
theorem discardWord_reaches (src : K') (next : Λ') (store : Option Γ')
    (S : K' → List Γ') (n : Nat) (suffix : List Γ')
    (hword : S src = trNat n ++ Γ'.cons :: suffix) :
    Reaches₁ (TM2.step machine) ⟨some (discardWord src next), store, S⟩
      ⟨some next, some Γ'.cons, update S src suffix⟩ := by
  have split : splitAtPred natEnd (S src) = (trNat n, some Γ'.cons, suffix) := by
    rw [hword]
    exact splitAtPred_eq _ _ _ _ _ (trNat_natEnd n) ⟨rfl, rfl⟩
  exact RuntimeMacros.clear_ok agrees split

/-- The marker after saved values is found without inspecting their word values. -/
theorem savedValues_split (saved : List Nat) (suffix : List Γ') :
    splitAtPred endFrame (trList saved ++ Γ'.consₗ :: suffix) =
      (trList saved, some Γ'.consₗ, suffix) := by
  apply splitAtPred_eq
  · intro symbol member
    exact Bool.decide_false (trList_ne_consₗ saved symbol member)
  · exact ⟨rfl, rfl⟩

/-- A first cons result keeps its default head and restores the saved right input. -/
theorem cons1_reaches (store : Option Γ') (out saved table : List Nat)
    (right : Nat) (older : List Γ') :
    Reaches₁ (TM2.step machine)
      (dataCfg .cons1 store out table
        (trList saved ++ Γ'.consₗ :: (trList [right] ++ older)))
      (dataCfg .evaluate none (right :: saved) table (trList [2, out.headI] ++ older)) := by
  refine (phase_reaches .cons1 store _ (by decide)).trans ?_
  simp only [entry]
  refine (RuntimeMacros.head_main_ok agrees).trans ?_
  refine (moveWord_reaches main aux _ none _ out.headI []
    (by decide) (by decide) (by decide) rfl rfl).trans ?_
  simp only [elim_update_main, elim_update_aux, elim_aux]
  refine (RuntimeMacros.move₂_ok agrees (by decide) rfl
    (savedValues_split saved (trList [right] ++ older))).trans ?_
  simp only [Option.elim_some, elim_update_stack, elim_update_main, elim_main,
    List.append_nil]
  refine (RuntimeMacros.clear_ok agrees (L₁ := []) (o := some Γ'.consₗ)
    (L₂ := trList [right] ++ older) rfl).trans ?_
  simp only [elim_update_stack]
  refine (moveWord_reaches stack main _ _ _ right older
    (by decide) (by decide) (by decide) rfl
    (by simp [trList, List.append_assoc])).trans ?_
  simp only [elim_update_stack, elim_update_main, elim_main]
  refine (moveWord_reaches aux stack _ _ _ out.headI (trList table)
    (by decide) (by decide) (by decide) rfl
    (by simp [trList, List.append_assoc])).trans_left ?_
  simp only [elim_update_aux, elim_update_stack, elim_stack]
  convert! pushWord_reaches stack 2 (label .evaluate) none _ using 2
  simp [dataCfg, elim_update_stack, trList, List.append_assoc]

/-- A second cons result prefixes the previously saved first value. -/
theorem cons2_reaches (store : Option Γ') (out table : List Nat)
    (headValue : Nat) (older : List Γ') :
    Reaches₁ (TM2.step machine)
      (dataCfg .cons2 store out table (trList [headValue] ++ older))
      (dataCfg .returned none (headValue :: out) table older) := by
  refine (phase_reaches .cons2 store _ (by decide)).trans ?_
  simp only [entry]
  simpa [StateTransition.Reaches₁, dataCfg, trList, List.append_assoc] using
    moveWord_reaches stack main (label .returned) store
    (K'.elim (trList out) [] (trList table) (trList [headValue] ++ older)) headValue older
    (by decide) (by decide) (by decide) rfl
    (by simp [trList, List.append_assoc])

/-- Composition evaluates its saved left address on the whole returned list. -/
theorem comp1_reaches (store : Option Γ') (out table : List Nat)
    (left : Nat) (older : List Γ') :
    Reaches₁ (TM2.step machine)
      (dataCfg .comp1 store out table (trList [left] ++ older))
      (dataCfg .evaluate none (left :: out) table older) := by
  refine (phase_reaches .comp1 store _ (by decide)).trans ?_
  simp only [entry]
  simpa [StateTransition.Reaches₁, dataCfg, trList, List.append_assoc] using
    moveWord_reaches stack main (label .evaluate) store
    (K'.elim (trList out) [] (trList table) (trList [left] ++ older)) left older
    (by decide) (by decide) (by decide) rfl
    (by simp [trList, List.append_assoc])

/-- A zero fix flag, including the default head of an empty list, returns its tail. -/
theorem fix1_zero_reaches (store : Option Γ') (out table : List Nat)
    (body : Nat) (older : List Γ') (zero : out.headI = 0) :
    Reaches₁ (TM2.step machine)
      (dataCfg .fix1 store out table (trList [body] ++ older))
      (dataCfg .returned (some Γ'.cons) out.tail table older) := by
  refine (phase_reaches .fix1 store _ (by decide)).trans ?_
  simp only [entry]
  obtain ⟨store', hp⟩ := RuntimeMacros.pred_ok agrees
    (discardWord stack (label .returned))
    (discardWord main (moveWord stack aux
      (copyWord aux (pushWord stack 4 (label .evaluate)))))
    store out (trList table) (trList [body] ++ older)
  rw [zero] at hp
  refine hp.trans ?_
  simpa [StateTransition.Reaches₁, dataCfg, trList, List.append_assoc] using
    discardWord_reaches stack (label .returned) store'
      (K'.elim (trList out.tail) [] (trList table) (trList [body] ++ older)) body older
      (by simp [trList, List.append_assoc])

/-- Every positive fix flag is removed in full before the body is evaluated again. -/
theorem fix1_positive_reaches (store : Option Γ') (out table : List Nat)
    (body : Nat) (older : List Γ') (positive : out.headI ≠ 0) :
    Reaches₁ (TM2.step machine)
      (dataCfg .fix1 store out table (trList [body] ++ older))
      (dataCfg .evaluate none (body :: out.tail) table (trList [4, body] ++ older)) := by
  refine (phase_reaches .fix1 store _ (by decide)).trans ?_
  simp only [entry]
  obtain ⟨store', hp⟩ := RuntimeMacros.pred_ok agrees
    (discardWord stack (label .returned))
    (discardWord main (moveWord stack aux
      (copyWord aux (pushWord stack 4 (label .evaluate)))))
    store out (trList table) (trList [body] ++ older)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero positive
  rw [hn] at hp
  refine hp.trans ?_
  refine (discardWord_reaches main _ store' _ n (trList out.tail) rfl).trans ?_
  simp only [elim_update_main]
  refine (moveWord_reaches stack aux _ _ _ body older
    (by decide) (by decide) (by decide) rfl
    (by simp [trList, List.append_assoc])).trans ?_
  simp only [elim_update_stack, elim_update_aux, elim_aux]
  refine (copyWord_reaches aux _ _ _ body (trList table) (by decide) rfl
    (by simp [trList, List.append_assoc])).trans_left ?_
  simp only [elim_update_aux, elim_update_main, elim_update_stack, elim_main, elim_stack]
  convert! pushWord_reaches stack 4 (label .evaluate) none _ using 2
  simp [dataCfg, trList, List.append_assoc]

/-- The fix return boundary branches only on zero, never on the size of a positive flag. -/
theorem fix1_reaches (store : Option Γ') (out table : List Nat)
    (body : Nat) (older : List Γ') :
    ∃ store', Reaches₁ (TM2.step machine)
      (dataCfg .fix1 store out table (trList [body] ++ older))
      (if out.headI = 0 then dataCfg .returned store' out.tail table older
       else dataCfg .evaluate store' (body :: out.tail) table (trList [4, body] ++ older)) := by
  by_cases zero : out.headI = 0
  · refine ⟨some Γ'.cons, ?_⟩
    simpa only [zero, ite_true] using fix1_zero_reaches store out table body older zero
  · refine ⟨none, ?_⟩
    simpa only [zero, ite_false] using fix1_positive_reaches store out table body older zero

/-- The halt instruction consumes one real TM2 step and clears the local store. -/
theorem halt_step (store : Option Γ') (values table : List Nat) (frames : List Γ') :
    TM2.step machine (dataCfg .halt store values table frames) =
      some ⟨none, none, K'.elim (trList values) [] (trList table) frames⟩ := by
  simp [TM2.step, machine, dataCfg, label, returnNumber_returnCode,
    codePhase_phaseCode, TM2.stepAux]

/-- Halting is positive reachability to an absent label, with every stack unchanged. -/
theorem halt_reaches (store : Option Γ') (values table : List Nat) (frames : List Γ') :
    Reaches₁ (TM2.step machine) (dataCfg .halt store values table frames)
      ⟨none, none, K'.elim (trList values) [] (trList table) frames⟩ :=
  .single (halt_step store values table frames)

/-- An absent control label has no successor, independently of all tape data. -/
theorem halt_terminal (store : Option Γ') (S : K' → List Γ') :
    TM2.step machine ⟨none, store, S⟩ = none := rfl

namespace ReturnFixtures

/-- Finite observations of every tape and the actual return-label number. -/
def symbolWord : Γ' → Nat
  | .consₗ => 0 | .cons => 1 | .bit0 => 2 | .bit1 => 3

def phaseNumber (cfg : Cfg') : Option Nat :=
  match cfg.l with
  | some (.ret continuation) => some (returnNumber continuation)
  | _ => none

abbrev Snapshot := List (List Nat)

def snapshot (cfg : Cfg') : Snapshot :=
  [[match cfg.l with
    | none => 0
    | some (.ret continuation) => returnNumber continuation + 1
    | _ => 100,
   cfg.var.elim 0 (fun symbol ↦ symbolWord symbol + 1)],
   (cfg.stk main).map symbolWord, (cfg.stk rev).map symbolWord,
   (cfg.stk aux).map symbolWord, (cfg.stk stack).map symbolWord]

/-- Observe a target phase after at least one actual step; fuel is only a fixture bound. -/
def runToPhase (phase : Phase) : Nat → Cfg' → Option Snapshot
  | 0, _ => none
  | fuel + 1, cfg => do
    let next ← TM2.step machine cfg
    if phaseNumber next = some (phaseCode phase) then some (snapshot next)
    else runToPhase phase fuel next

def table : List Nat := [7, 0, 13]

/-- An intentionally unparsed suffix must survive every return body byte for byte. -/
def older : List Γ' := [.bit1, .consₗ, .bit0, .cons]

theorem cons1_empty :
    runToPhase .evaluate 200
      (dataCfg .cons1 (some .bit0) [] table (Γ'.consₗ :: (trList [0] ++ older))) =
      some (snapshot (dataCfg .evaluate none [0] table (trList [2, 0] ++ older))) := by
  decide +kernel

theorem cons1_saved :
    runToPhase .evaluate 200
      (dataCfg .cons1 (some .consₗ) [9, 3] table
        (trList [8, 0, 5] ++ Γ'.consₗ :: (trList [7] ++ older))) =
      some (snapshot (dataCfg .evaluate none [7, 8, 0, 5] table
        (trList [2, 9] ++ older))) := by
  decide +kernel

theorem cons2_empty :
    runToPhase .returned 200
      (dataCfg .cons2 (some .bit1) [] table (trList [12] ++ older)) =
      some (snapshot (dataCfg .returned none [12] table older)) := by
  decide +kernel

theorem comp1_whole :
    runToPhase .evaluate 200
      (dataCfg .comp1 (some .cons) [3, 0, 7] table (trList [8] ++ older)) =
      some (snapshot (dataCfg .evaluate none [8, 3, 0, 7] table older)) := by
  decide +kernel

theorem fix1_empty :
    runToPhase .returned 200
      (dataCfg .fix1 (some .bit0) [] table (trList [6] ++ older)) =
      some (snapshot (dataCfg .returned (some .cons) [] table older)) := by
  decide +kernel

theorem fix1_zero :
    runToPhase .returned 200
      (dataCfg .fix1 none [0, 12, 0] table (trList [6] ++ older)) =
      some (snapshot (dataCfg .returned (some .cons) [12, 0] table older)) := by
  decide +kernel

theorem fix1_one :
    runToPhase .evaluate 200
      (dataCfg .fix1 (some .consₗ) [1] table (trList [6] ++ older)) =
      some (snapshot (dataCfg .evaluate none [6] table (trList [4, 6] ++ older))) := by
  decide +kernel

theorem fix1_nineteen :
    runToPhase .evaluate 200
      (dataCfg .fix1 (some .bit1) [19, 0, 5] table (trList [6] ++ older)) =
      some (snapshot (dataCfg .evaluate none [6, 0, 5] table (trList [4, 6] ++ older))) := by
  decide +kernel

theorem halt_exact :
    (snapshot <$> TM2.step machine (dataCfg .halt (some .bit0) [8, 0] table older)) =
        some (snapshot ⟨none, none, K'.elim (trList [8, 0]) [] (trList table) older⟩) ∧
      ((TM2.step machine (dataCfg .halt (some .bit0) [8, 0] table older)).bind
        (TM2.step machine)).isNone = true := by
  decide +kernel

end ReturnFixtures

end ConjectureMachines.Compilation.Runtime
