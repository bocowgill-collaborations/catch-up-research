import CatchUp.Executable
namespace CatchUp
/-- A zero-deficit normalized position has the same value as the corresponding Catch-Up root. -/
theorem position_value_zero_deficit_eq_value (S : Finset ℕ) :
    Position.value ⟨S, 0⟩ = value S := by
  rw [Position.value_eq_value_aux S 0 0 (by omega)]
  rw [value]
  rw [valueAux.eq_def, valueAux.eq_def]
  by_cases hS : S = ∅
  · simp [hS]
  · simp only [hS, Nat.zero_add, Nat.not_lt_zero, if_false]
    congr 1

end CatchUp
