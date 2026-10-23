/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see the repository LICENSE.
-/
import CatchUp.Search

/-! # Small reproducible executable observations for an independent absolute-score checker. -/

open CatchUp

private def outcomeCode : Outcome → Int
  | .win => 1
  | .draw => 0
  | .loss => -1

private def counters (mask : ℕ) : Finset ℕ :=
  ((List.range 6).filterMap fun i ↦
    if mask.testBit i then some (i + 1) else none).toFinset

/-- Enumerate irregular noninitial states and small roots; no result here is a proof premise. -/
def main : IO Unit := do
  for mask in List.range 64 do
    for deficit in List.range 13 do
      let result := Position.eval ⟨counters mask, deficit⟩
      IO.println s!"state,{mask},{deficit},{outcomeCode result}"
  for N in List.range 10 do
    IO.println s!"root,{N},{outcomeCode (evalInitial (Finset.Icc 1 N))}"
