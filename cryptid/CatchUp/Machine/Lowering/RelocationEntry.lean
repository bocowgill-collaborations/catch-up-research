import CatchUp.Machine.Lowering.RelocationGeometry

namespace CatchUp.Machine.Lowering.Relocation
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Arithmetic layout identity, for arbitrary interpreter programs. -/
theorem prefix_formula (p : Cases.Program) :
    Cases.prefixStates p=10360+4638*p.length := by
  have h := base_formula p
  change 2+(Cases.prefixStates p+(Cases.pool p).length*462)+2*463=
    11288+4638*p.length+462*(Cases.pool p).length at h
  omega

theorem literal_normal_val (p : Cases.Program) (i : Fin (Cases.pool p).length)
    (old : Fin 460) :
    (Cases.literalNormal p i old).val=2+Cases.prefixStates p+462*i.val+old.val := by
  change 2+(Cases.prefixStates p+(old.val+462*i.val))=_
  omega

/-- The redirected bank hook is the actual projected instruction entry, rather
than an arbitrary control inside a paid literal routine. -/
theorem push_zero_entry (p : Cases.Program) (pc next : Nat)
    (h : p[pc]?=some (.push 0 next)) :
    (Cases.entry p pc).val=2+Cases.prefixStates p+462*Cases.offset p pc+40 := by
  have pool := Cases.pool_at p pc (.push 0 next) h
  have inside : Cases.offset p pc<(Cases.pool p).length := by
    rw [Cases.offset,pool]
    simp only [List.length_append,Cases.chunk,Cases.fragment,List.replicate_zero,
      List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.length_cons,
      List.length_nil]
    omega
  have cell : Cases.literalCell p (Cases.offset p pc)=(0,none) := by
    simp only [Cases.literalCell,Cases.offset,pool,Cases.chunk,Cases.fragment,
      List.replicate_zero,List.map_cons,List.map_nil,List.cons_append,List.nil_append]
    simp
  simp only [Cases.entry,h,Cases.literalStart,inside,↓reduceDIte,cell]
  rw [literal_normal_val]
  rfl

theorem bank_entry (pc next : Nat) (kind : Bank)
    (h : program[pc]?=some (.bank kind next)) :
    (Cases.entry projection pc).val=hook pc := by
  have hp : projection[pc]?=some (.push 0 next) := by
    simp only [projection,List.getElem?_map,h,Option.map_some,project]
  rw [push_zero_entry projection pc next hp,prefix_formula,Cases.offset,pool_length]
  unfold hook
  omega

theorem base_below_total : Cases.states projection<totalSize := by
  rw [base_count]
  decide +kernel

/-- Widen an existing control without changing its numeric index. Keeping this
operation generic avoids expanding the large interpreter state count. -/
def widenState {n m : Nat} (q : Fin n) (h : n < m) : Fin m :=
  ⟨q.val,lt_trans q.isLt h⟩

theorem widen_value {n m : Nat} (q : Fin n) (h : n < m) :
    (widenState q h).val=q.val := rfl

theorem widen_below {n m : Nat} (q : Fin n) (h : n < m) :
    (widenState q h).val<n := q.isLt

/-- Entry of the paid interpreter in the candidate body. -/
def entryState (pc : Nat) : Fin totalSize :=
  widenState (Cases.entry projection pc) base_below_total

theorem entry_below (pc : Nat) : (entryState pc).val<Cases.states projection := by
  have result := widen_below (Cases.entry projection pc) base_below_total
  exact result

theorem entry_value (pc : Nat) : (entryState pc).val=(Cases.entry projection pc).val := by
  have result := widen_value (Cases.entry projection pc) base_below_total
  exact result

end CatchUp.Machine.Lowering.Relocation
