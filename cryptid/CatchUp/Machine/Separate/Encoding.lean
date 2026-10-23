import CatchUp.Machine.Separate.Calls

namespace CatchUp.Machine.Separate
open Turing

/-- Blank extension cannot identify distinct marker/bit words, even when
their final data bit is zero. -/
theorem wire_injective : Function.Injective (fun w ↦ ListBlank.mk (wire w)) := by
  intro w
  induction w with
  | nil =>
    intro v h
    cases v with
    | nil => rfl
    | cons a v =>
      have head := congrArg ListBlank.head h
      simp at head
  | cons a w ih =>
    intro v h
    cases v with
    | nil =>
      have head := congrArg ListBlank.head h
      simp at head
    | cons b v =>
      have bit := congrArg (fun t : ListBlank Bit ↦ t.tail.head) h
      have rest := congrArg (fun t : ListBlank Bit ↦ t.tail.tail) h
      simp only [wire_cons,ListBlank.tail_mk,List.tail_cons,ListBlank.head_mk,
        List.headI_cons] at bit rest
      exact congrArg₂ List.cons bit (ih rest)

theorem banks_injective (data frames data' frames' : List Bit)
    (h : banks data frames = banks data' frames') : data=data' ∧ frames=frames' := by
  have left := congrArg (fun t : Tape Bit ↦ t.left.tail) h
  have right := congrArg (fun t : Tape Bit ↦ t.right.tail) h
  simp only [banks,home,view,↓reduceIte,Tape.mk₂,Tape.mk',ListBlank.head_mk,
    List.headI_cons,ListBlank.tail_mk,List.tail_cons] at left right
  exact ⟨wire_injective left,wire_injective right⟩

end CatchUp.Machine.Separate
