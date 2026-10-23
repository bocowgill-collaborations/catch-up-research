/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.Code

/-! # Fixed four-stack interpreter control

Program rows, program counters and return frames are data. The finite macro control
contains no source Code payload. Its simulation proof is developed separately.
-/

@[expose] public section
namespace ConjectureMachines.Compilation.Runtime
open Turing PartrecToTM2 K'

/-- Only these fixed phases inhabit return labels in the interpreter. -/
inductive Phase where
  | start | evaluate | lookup | readRow | restore | dispatch
  | zero | successor | tail | cons | comp | branch | fix
  | returned | halt | cons1 | cons2 | comp1 | fix1 | invalid
  deriving DecidableEq, Repr

def phaseCode : Phase → Nat
  | .start => 0 | .evaluate => 1 | .lookup => 2 | .readRow => 3
  | .restore => 4 | .dispatch => 5 | .zero => 6 | .successor => 7
  | .tail => 8 | .cons => 9 | .comp => 10 | .branch => 11 | .fix => 12
  | .returned => 13 | .halt => 14 | .cons1 => 15 | .cons2 => 16
  | .comp1 => 17 | .fix1 => 18 | .invalid => 19

def codePhase : Nat → Phase
  | 0 => .start | 1 => .evaluate | 2 => .lookup | 3 => .readRow
  | 4 => .restore | 5 => .dispatch | 6 => .zero | 7 => .successor
  | 8 => .tail | 9 => .cons | 10 => .comp | 11 => .branch | 12 => .fix
  | 13 => .returned | 14 => .halt | 15 => .cons1 | 16 => .cons2
  | 17 => .comp1 | 18 => .fix1 | _ => .invalid

theorem codePhase_phaseCode (phase : Phase) : codePhase (phaseCode phase) = phase := by
  cases phase <;> rfl

def returnCode : Nat → Cont'
  | 0 => .halt
  | n + 1 => .cons₂ (returnCode n)

def returnNumber : Cont' → Nat
  | .halt => 0
  | .cons₂ k => returnNumber k + 1
  | _ => 20

theorem returnNumber_returnCode (n : Nat) : returnNumber (returnCode n) = n := by
  induction n <;> simp_all [returnCode, returnNumber]

def label (phase : Phase) : Λ' := .ret (returnCode (phaseCode phase))

/-- Move a whole natural word, reversing twice and replacing its separator. -/
def moveWord (src dst : K') (next : Λ') : Λ' :=
  .move natEnd src rev (.push dst (fun _ => some .cons) (unrevTo dst next))
where
  unrevTo (dst : K') (next : Λ') : Λ' := .move (fun _ => false) rev dst next

/-- Remove one source word and prepend it to both main and continuation stacks. -/
def copyWord (src : K') (next : Λ') : Λ' :=
  .move natEnd src rev (.push main (fun _ => some .cons)
    (.push stack (fun _ => some .cons) (.copy next)))

def copyValues (next : Λ') : Λ' := .move (fun _ => false) main rev (.copy next)

/-- Push symbols in their written order rather than their execution order. -/
def pushSymbols (dst : K') (symbols : List Γ') (next : Λ') : Λ' :=
  symbols.foldl (fun code symbol => .push dst (fun _ => some symbol) code) next

def pushWord (dst : K') (n : Nat) (next : Λ') : Λ' := pushSymbols dst (trList [n]) next

def discardWord (src : K') (next : Λ') : Λ' := .clear natEnd src next

def choose : List Λ' → Λ' → Λ'
  | [], fallback => fallback
  | first :: rest, fallback => .pred first (choose rest fallback)

def endFrame : Γ' → Bool := fun symbol => symbol = .consₗ

/-- All source-dependent control is read from `aux`; each lookup restores the whole table. -/
def entry : Phase → Λ'
  | .start =>
    moveWord main stack (move₂ endFrame main aux
      (.clear (fun _ => true) main (moveWord stack main (pushWord stack 0 (label .evaluate)))))
  | .evaluate => .push stack (fun _ => some .consₗ) (label .lookup)
  | .lookup => .pred (label .readRow)
      (moveWord aux stack (moveWord aux stack (moveWord aux stack (label .lookup))))
  | .readRow => copyWord aux (copyWord aux (copyWord aux (label .restore)))
  | .restore => .move (fun _ => true) stack rev (.read fun symbol =>
      if symbol = some .consₗ then
        moveWord main stack (moveWord main stack (label .dispatch))
      else .push stack id (moveWord stack aux (label .restore)))
  | .dispatch => choose
      [label .zero, label .successor, label .tail, label .cons,
       label .comp, label .branch, label .fix] (label .invalid)
  | .zero => discardWord stack (discardWord stack (pushWord main 0 (label .returned)))
  | .successor => discardWord stack (discardWord stack (head main (.succ (label .returned))))
  | .tail => discardWord stack (discardWord stack (discardWord main (label .returned)))
  | .cons => moveWord stack aux (.push stack (fun _ => some .consₗ)
      (copyValues (pushWord stack 1 (moveWord aux main (label .evaluate)))))
  | .comp => moveWord stack aux (moveWord stack main
      (moveWord aux stack (pushWord stack 3 (label .evaluate))))
  | .branch => .pred
      (moveWord stack aux (discardWord stack (moveWord aux main (label .evaluate))))
      (discardWord stack (moveWord stack main (label .evaluate)))
  | .fix => moveWord stack aux (discardWord stack
      (copyWord aux (pushWord stack 4 (label .evaluate))))
  | .returned => moveWord stack main (choose
      [label .halt, label .cons1, label .cons2, label .comp1, label .fix1] (label .invalid))
  | .halt => label .halt
  | .cons1 => head main (moveWord main aux
      (move₂ endFrame stack main (.clear (fun _ => true) stack
        (moveWord stack main (moveWord aux stack (pushWord stack 2 (label .evaluate)))))))
  | .cons2 => moveWord stack main (label .returned)
  | .comp1 => moveWord stack main (label .evaluate)
  | .fix1 => .pred (discardWord stack (label .returned))
      (discardWord main (moveWord stack aux (copyWord aux (pushWord stack 4 (label .evaluate)))))
  | .invalid => label .invalid

/-- Mathlib's primitive macro steps with only return dispatch replaced. -/
def machine : Λ' → Stmt'
  | .ret k =>
    let phase := codePhase (returnNumber k)
    if phase = .halt then .load (fun _ => none) .halt
    else .goto (fun _ => entry phase)
  | other => PartrecToTM2.tr other

def phases : List Phase :=
  [.start, .evaluate, .lookup, .readRow, .restore, .dispatch, .zero, .successor,
   .tail, .cons, .comp, .branch, .fix, .returned, .halt, .cons1, .cons2, .comp1, .fix1, .invalid]

theorem phases_cover (phase : Phase) : phase ∈ phases := by cases phase <;> simp [phases]

/-- Ordered finite candidate support; the executable program is independent of source data. -/
def labels : List Λ' :=
  phases.flatMap (fun phase => label phase :: CodeBackend.trStmtsList (entry phase))

end ConjectureMachines.Compilation.Runtime
