/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.Normalize
public import Cryptids.Compilation.LocalCertificate
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Direct numeric binary block templates

Labels contain a source program counter, or a write-site number and an alphabet symbol.
The move/read/write macros generalize Mario Carneiro's Apache-2.0 Mathlib implementation
in `Computability/TuringMachine/PostTuringMachine.lean` to arbitrary target labels.
The site tables are explicit data with constructor-based classification certificates.
No equality test on function-valued labels is used by the executable machine.
-/

@[expose] public section

namespace ConjectureMachines.Compilation.BinaryTemplates

open Turing TM1

variable {Γ σ A B : Type*}

/-- A block-sized move, with an arbitrary target label type. -/
def move (width : Nat) (d : Dir) (q : Stmt Bool A σ) : Stmt Bool A σ :=
  (Stmt.move d)^[width] q

/-- The read tree from Mathlib's block translation, generalized to arbitrary target labels. -/
def readAux : (width : Nat) →
    (List.Vector Bool width → Stmt Bool A σ) → Stmt Bool A σ
  | 0, f => f List.Vector.nil
  | width + 1, f =>
    .branch (fun a _ ↦ a)
      (.move .right (readAux width fun v ↦ f (true ::ᵥ v)))
      (.move .right (readAux width fun v ↦ f (false ::ᵥ v)))

/-- Read one encoded symbol and return the tape head to its starting position. -/
def read {width : Nat} (dec : List.Vector Bool width → Γ)
    (f : Γ → Stmt Bool A σ) : Stmt Bool A σ :=
  readAux width fun v ↦ move width .left (f (dec v))

/-- Write bits successively, ending just after their last cell. -/
def write : List Bool → Stmt Bool A σ → Stmt Bool A σ
  | [], q => q
  | a :: bits, q => .write (fun _ _ ↦ a) (.move .right (write bits q))

/-- Control renaming commutes with block-sized movement. -/
theorem map_move (f : A → B) (width : Nat) (d : Dir) (q : Stmt Bool A σ) :
    TM1Number.mapStmt f (move width d q) = move width d (TM1Number.mapStmt f q) := by
  induction width with
  | zero => rfl
  | succ width ih =>
    simpa only [move, Function.iterate_succ_apply', TM1Number.mapStmt] using
      congrArg (Stmt.move d) ih

/-- Control renaming commutes with the entire read tree. -/
theorem map_readAux (f : A → B) (width : Nat)
    (body : List.Vector Bool width → Stmt Bool A σ) :
    TM1Number.mapStmt f (readAux width body) =
      readAux width (fun v ↦ TM1Number.mapStmt f (body v)) := by
  induction width with
  | zero => rfl
  | succ width ih => simp only [readAux, TM1Number.mapStmt, ih]

/-- Control renaming commutes with reading and restoring the tape head. -/
theorem map_read (f : A → B) {width : Nat} (dec : List.Vector Bool width → Γ)
    (body : Γ → Stmt Bool A σ) :
    TM1Number.mapStmt f (read dec body) =
      read dec (fun a ↦ TM1Number.mapStmt f (body a)) := by
  simp only [read, map_readAux, map_move]

/-- Control renaming commutes with writing every bit. -/
theorem map_write (f : A → B) (bits : List Bool) (q : Stmt Bool A σ) :
    TM1Number.mapStmt f (write bits q) = write bits (TM1Number.mapStmt f q) := by
  induction bits with
  | nil => rfl
  | cons a bits ih => simp only [write, TM1Number.mapStmt, ih]

/-- The generalized movement macro is definitionally Mathlib's macro on its label type. -/
theorem move_mathlib (width : Nat) (d : Dir)
    (q : Stmt Bool (TM1to1.Λ' Γ A σ) σ) :
    move width d q = TM1to1.move width d q := rfl

/-- The generalized read tree has exactly Mathlib's branch and movement structure. -/
theorem readAux_mathlib (width : Nat)
    (body : List.Vector Bool width → Stmt Bool (TM1to1.Λ' Γ A σ) σ) :
    readAux width body = TM1to1.readAux width body := by
  induction width with
  | zero => rfl
  | succ width ih => simp only [readAux, TM1to1.readAux, ih]

/-- The generalized reader is exactly Mathlib's reader. -/
theorem read_mathlib {width : Nat} (dec : List.Vector Bool width → Γ)
    (body : Γ → Stmt Bool (TM1to1.Λ' Γ A σ) σ) :
    read dec body = TM1to1.read dec body := by
  simp only [read, TM1to1.read, readAux_mathlib, move_mathlib]

/-- The generalized writer is exactly Mathlib's writer. -/
theorem write_mathlib (bits : List Bool) (q : Stmt Bool (TM1to1.Λ' Γ A σ) σ) :
    write bits q = TM1to1.write bits q := by
  induction bits with
  | nil => rfl
  | cons a bits ih => simp only [write, TM1to1.write, ih]

/-- Movement introduces no additional jumps. -/
theorem move_allHeadFree (width : Nat) (d : Dir) (q : Stmt Bool A σ)
    (h : Block.AllHeadFree q) : Block.AllHeadFree (move width d q) := by
  induction width with
  | zero => exact h
  | succ width ih =>
    simpa only [move, Function.iterate_succ_apply', Block.AllHeadFree] using ih

/-- Each leaf of the read tree retains its head-free goto property. -/
theorem readAux_allHeadFree (width : Nat)
    (body : List.Vector Bool width → Stmt Bool A σ)
    (h : ∀ v, Block.AllHeadFree (body v)) : Block.AllHeadFree (readAux width body) := by
  induction width with
  | zero => exact h _
  | succ width ih => exact ⟨ih _ (fun _ ↦ h _), ih _ (fun _ ↦ h _)⟩

/-- Reading and returning the tape head introduces no head-dependent gotos. -/
theorem read_allHeadFree {width : Nat} (dec : List.Vector Bool width → Γ)
    (body : Γ → Stmt Bool A σ) (h : ∀ a, Block.AllHeadFree (body a)) :
    Block.AllHeadFree (read dec body) :=
  readAux_allHeadFree _ _ (fun v ↦ move_allHeadFree _ _ _ (h (dec v)))

/-- Writing introduces no additional jumps. -/
theorem write_allHeadFree (bits : List Bool) (q : Stmt Bool A σ)
    (h : Block.AllHeadFree q) : Block.AllHeadFree (write bits q) := by
  induction bits with
  | nil => exact h
  | cons _ _ ih => exact ih

section Tables

variable {n w m : Nat}

/-- Explicit source write PCs, saved goto functions, and the inverse classification table.
`row` checks the shape of each listed row; `covers` checks that no source write is omitted.
Neither condition asks Lean to decide equality of functions. -/
structure WriteSites (M : Fin n → Stmt Γ (Fin n) σ) (w : Nat) where
  pc : Fin w → Fin n
  next : Fin w → Γ → σ → Fin n
  siteFor : Fin n → Option (Fin w)
  row : ∀ i, ∃ f, M (pc i) = .write f (.goto (next i))
  lookup : ∀ i, siteFor (pc i) = some i
  inverse : ∀ q i, siteFor q = some i → pc i = q
  covers : ∀ q f tail, M q = .write f tail → ∃ i, siteFor q = some i

/-- A classified write row has exactly its site's saved continuation. -/
theorem WriteSites.continuation {M : Fin n → Stmt Γ (Fin n) σ} (sites : WriteSites M w)
    {q : Fin n} {f : Γ → σ → Γ} {tail : Stmt Γ (Fin n) σ} {i : Fin w}
    (row : M q = .write f tail) (site : sites.siteFor q = some i) :
    tail = .goto (sites.next i) := by
  obtain ⟨g, hg⟩ := sites.row i
  rw [sites.inverse q i site, row] at hg
  exact (Stmt.write.inj hg).2

/-- Classification succeeds exactly on source write rows. -/
theorem WriteSites.classified_iff {M : Fin n → Stmt Γ (Fin n) σ}
    (sites : WriteSites M w) (q : Fin n) :
    (∃ i, sites.siteFor q = some i) ↔ ∃ f tail, M q = .write f tail := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨f, hf⟩ := sites.row i
    exact ⟨f, _, sites.inverse q i hi ▸ hf⟩
  · rintro ⟨f, tail, h⟩
    exact sites.covers q f tail h

/-- First come the normal PCs, followed by site-major, glyph-minor writer PCs. -/
def labelEquiv (n w m : Nat) : (Fin n ⊕ (Fin w × Fin m)) ≃ Fin (n + w * m) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

/-- Numeric normal PC; it has the same natural value as its source PC. -/
def normal (w m : Nat) (q : Fin n) : Fin (n + w * m) := labelEquiv n w m (.inl q)

/-- Numeric writer PC; its value is `n + m * site + glyph`. -/
def writer (n : Nat) (i : Fin w) (a : Fin m) : Fin (n + w * m) :=
  labelEquiv n w m (.inr (i, a))

@[simp] theorem normal_val (q : Fin n) : (normal w m q).val = q.val := rfl

@[simp] theorem writer_val (i : Fin w) (a : Fin m) :
    (writer n i a).val = n + (a.val + m * i.val) := rfl

/-- Exact decoder; no search through raw compiler labels occurs. -/
def decode {M : Fin n → Stmt Γ (Fin n) σ} (sites : WriteSites M w) (alphabet : Fin m ≃ Γ)
    (q : Fin (n + w * m)) : TM1to1.Λ' Γ (Fin n) σ :=
  match (labelEquiv n w m).symm q with
  | .inl q => .normal q
  | .inr (i, a) => .write (alphabet a) (.goto (sites.next i))

@[simp] theorem decode_normal {M : Fin n → Stmt Γ (Fin n) σ} (sites : WriteSites M w)
    (alphabet : Fin m ≃ Γ) (q : Fin n) :
    decode sites alphabet (normal w m q) = .normal q := by
  simp only [decode, normal, Equiv.symm_apply_apply]

@[simp] theorem decode_writer {M : Fin n → Stmt Γ (Fin n) σ} (sites : WriteSites M w)
    (alphabet : Fin m ≃ Γ) (i : Fin w) (a : Fin m) :
    decode sites alphabet (writer n i a) = .write (alphabet a) (.goto (sites.next i)) := by
  simp only [decode, writer, Equiv.symm_apply_apply]

/-- A normal row performs exactly its primitive, then transfers to a numeric PC.
The fallback branches are unreachable when `OnePrimitive` and site coverage are checked. -/
def normalRow [Inhabited Γ] (C : BlockCode Γ) (M : Fin n → Stmt Γ (Fin n) σ)
    (sites : WriteSites M w) (alphabet : Fin m ≃ Γ) (q : Fin n) :
    Stmt Bool (Fin (n + w * m)) σ :=
  match M q with
  | .move d (.goto l) => move C.width d (.goto fun _ v ↦ normal w m (l default v))
  | .write f _ =>
    match sites.siteFor q with
    | some i => read C.decode fun a ↦ .goto fun _ v ↦ writer n i (alphabet.symm (f a v))
    | none => .halt
  | .load f (.goto l) =>
    read C.decode fun a ↦ .load (fun _ v ↦ f a v)
      (.goto fun _ v ↦ normal w m (l default v))
  | .branch p (.goto l) (.goto r) =>
    read C.decode fun a ↦ .branch (fun _ v ↦ p a v)
      (.goto fun _ v ↦ normal w m (l default v))
      (.goto fun _ v ↦ normal w m (r default v))
  | .goto l => .goto fun _ v ↦ normal w m (l default v)
  | .halt => .halt
  | _ => .halt

/-- Direct finite binary machine. Its only extra states are the site/glyph writer table. -/
def machine [Inhabited Γ] (C : BlockCode Γ) (M : Fin n → Stmt Γ (Fin n) σ)
    (sites : WriteSites M w) (alphabet : Fin m ≃ Γ) (q : Fin (n + w * m)) :
    Stmt Bool (Fin (n + w * m)) σ :=
  match (labelEquiv n w m).symm q with
  | .inl q => normalRow C M sites alphabet q
  | .inr (i, a) =>
    write (C.encode (alphabet a)).toList
      (move C.width .left (.goto fun _ v ↦ normal w m (sites.next i default v)))

@[simp] theorem machine_normal [Inhabited Γ] (C : BlockCode Γ)
    (M : Fin n → Stmt Γ (Fin n) σ) (sites : WriteSites M w) (alphabet : Fin m ≃ Γ)
    (q : Fin n) : machine C M sites alphabet (normal w m q) = normalRow C M sites alphabet q := by
  simp only [machine, normal, Equiv.symm_apply_apply]

@[simp] theorem machine_writer [Inhabited Γ] (C : BlockCode Γ)
    (M : Fin n → Stmt Γ (Fin n) σ) (sites : WriteSites M w) (alphabet : Fin m ≃ Γ)
    (i : Fin w) (a : Fin m) :
    machine C M sites alphabet (writer n i a) =
      write (C.encode (alphabet a)).toList
        (move C.width .left (.goto fun _ v ↦ normal w m (sites.next i default v))) := by
  simp only [machine, writer, Equiv.symm_apply_apply]

/-- Every classified primitive normal row decodes to the exact block-compiler row. -/
theorem normalRow_refines [Inhabited Γ] (C : BlockCode Γ)
    (M : Fin n → Stmt Γ (Fin n) σ) (sites : WriteSites M w) (alphabet : Fin m ≃ Γ)
    (q : Fin n) (primitive : TM1Normalize.OnePrimitive (M q)) :
    TM1Number.mapStmt (decode sites alphabet) (normalRow C M sites alphabet q) =
      Block.fastNormalFree C (M q) := by
  cases row : M q with
  | move d tail =>
    cases tail <;> simp_all only [TM1Normalize.OnePrimitive]
    simp only [normalRow, row, map_move, TM1Number.mapStmt, decode_normal,
      move_mathlib, Block.fastNormalFree]
  | write f tail =>
    obtain ⟨i, hi⟩ := sites.covers q f tail row
    have ht := sites.continuation row hi
    simp only [normalRow, row, hi, map_read, read_mathlib, TM1Number.mapStmt,
      decode_writer, Equiv.apply_symm_apply, ht, Block.fastNormalFree]
  | load f tail =>
    cases tail <;> simp_all only [TM1Normalize.OnePrimitive]
    simp only [normalRow, row, map_read, read_mathlib, TM1Number.mapStmt,
      decode_normal, Block.fastNormalFree]
  | branch p left right =>
    cases left <;> cases right <;> simp_all only [TM1Normalize.OnePrimitive]
    simp only [normalRow, row, map_read, read_mathlib, TM1Number.mapStmt,
      decode_normal, Block.fastNormalFree]
  | goto l =>
    simp only [normalRow, row, TM1Number.mapStmt, decode_normal, Block.fastNormalFree]
  | halt => simp only [normalRow, row, TM1Number.mapStmt, Block.fastNormalFree]

/-- The explicit sites list contains no duplicate source PCs. -/
theorem WriteSites.pc_injective {M : Fin n → Stmt Γ (Fin n) σ} (sites : WriteSites M w) :
    Function.Injective sites.pc := by
  intro i j h
  have e := congrArg sites.siteFor h
  simpa only [sites.lookup, Option.some.injEq] using e

/-- The exact site table never lists more write sites than there are source PCs. -/
theorem WriteSites.count_le {M : Fin n → Stmt Γ (Fin n) σ} (sites : WriteSites M w) :
    w ≤ n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective sites.pc sites.pc_injective

/-- Every saved writer continuation is head-free when the source rows are head-free. -/
theorem WriteSites.next_headFree [Inhabited Γ] {M : Fin n → Stmt Γ (Fin n) σ}
    (sites : WriteSites M w) (headFree : ∀ q, Block.AllHeadFree (M q)) (i : Fin w) :
    Block.HeadFree (sites.next i) := by
  obtain ⟨f, row⟩ := sites.row i
  simpa only [row, Block.AllHeadFree] using headFree (sites.pc i)

/-- Every numeric row, including every writer glyph, has the exact frozen compiler body. -/
theorem rows_refine [Inhabited Γ] (C : BlockCode Γ)
    (M : Fin n → Stmt Γ (Fin n) σ) (sites : WriteSites M w) (alphabet : Fin m ≃ Γ)
    (primitive : ∀ q, TM1Normalize.OnePrimitive (M q)) :
    LocalCertificate.TM1Rows (machine C M sites alphabet) (Block.compilerFree C M)
      (decode sites alphabet) := by
  intro label
  obtain ⟨label, rfl⟩ := (labelEquiv n w m).surjective label
  cases label with
  | inl q =>
    change TM1Number.mapStmt (decode sites alphabet)
      (machine C M sites alphabet (normal w m q)) =
      Block.compilerFree C M (decode sites alphabet (normal w m q))
    simp only [machine_normal, decode_normal, Block.compilerFree]
    exact normalRow_refines C M sites alphabet q (primitive q)
  | inr pair =>
    rcases pair with ⟨i, a⟩
    change TM1Number.mapStmt (decode sites alphabet)
      (machine C M sites alphabet (writer n i a)) =
      Block.compilerFree C M (decode sites alphabet (writer n i a))
    simp only [machine_writer, decode_writer, map_write, map_move,
      TM1Number.mapStmt, decode_normal, write_mathlib, move_mathlib,
      Block.compilerFree, Block.fastNormalFree]

/-- Numeric normal rows use head-free jumps, including every read-tree leaf. -/
theorem normalRow_allHeadFree [Inhabited Γ] (C : BlockCode Γ)
    (M : Fin n → Stmt Γ (Fin n) σ) (sites : WriteSites M w) (alphabet : Fin m ≃ Γ)
    (q : Fin n) : Block.AllHeadFree (normalRow C M sites alphabet q) := by
  cases row : M q with
  | move d tail =>
    cases tail <;> simp only [normalRow, row, Block.AllHeadFree]
    exact move_allHeadFree _ _ _ (fun _ _ ↦ rfl)
  | write f tail =>
    simp only [normalRow, row]
    cases sites.siteFor q with
    | none => trivial
    | some i => exact read_allHeadFree _ _ (fun _ _ _ ↦ rfl)
  | load f tail =>
    cases tail <;> simp only [normalRow, row, Block.AllHeadFree]
    exact read_allHeadFree _ _ (fun _ _ _ ↦ rfl)
  | branch p left right =>
    cases left <;> cases right <;> simp only [normalRow, row, Block.AllHeadFree]
    exact read_allHeadFree _ _ (fun _ ↦ ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩)
  | goto l => simp only [normalRow, row, Block.AllHeadFree, Block.HeadFree, implies_true]
  | halt => simp only [normalRow, row, Block.AllHeadFree]

/-- All rows of the target have tape-head-independent jumps. -/
theorem machine_allHeadFree [Inhabited Γ] (C : BlockCode Γ)
    (M : Fin n → Stmt Γ (Fin n) σ) (sites : WriteSites M w) (alphabet : Fin m ≃ Γ)
    (q : Fin (n + w * m)) : Block.AllHeadFree (machine C M sites alphabet q) := by
  obtain ⟨q, rfl⟩ := (labelEquiv n w m).surjective q
  cases q with
  | inl q =>
    change Block.AllHeadFree (machine C M sites alphabet (normal w m q))
    rw [machine_normal]
    exact normalRow_allHeadFree C M sites alphabet q
  | inr pair =>
    rcases pair with ⟨i, a⟩
    change Block.AllHeadFree (machine C M sites alphabet (writer n i a))
    rw [machine_writer]
    exact write_allHeadFree _ _ (move_allHeadFree _ _ _ (fun _ _ ↦ rfl))

/-- A nonempty source has a nonempty numeric target, with state zero initially selected. -/
instance labelNeZero [NeZero n] : NeZero (n + w * m) :=
  ⟨by have := NeZero.ne n; omega⟩

@[simp] theorem normal_zero [NeZero n] : normal w m (0 : Fin n) = 0 := rfl

/-- The actual default numeric PC decodes to the actual default normal source label. -/
theorem decode_initial [NeZero n] {M : Fin n → Stmt Γ (Fin n) σ}
    (sites : WriteSites M w) (alphabet : Fin m ≃ Γ) :
    decode sites alphabet default = default := by
  exact decode_normal sites alphabet (0 : Fin n)

/-- Exact finite label count, independent of symbol or store function evaluation. -/
theorem state_count : Fintype.card (Fin (n + w * m)) = n + w * m := Fintype.card_fin _

/-- Each numeric label is strictly below the stated finite count. -/
theorem state_bound (q : Fin (n + w * m)) : q.val < n + w * m := q.isLt

/-- Full finite control supports every statement over that control type. -/
theorem supportsStmt_univ [Fintype A] (stmt : Stmt Γ A σ) :
    SupportsStmt Finset.univ stmt := by
  induction stmt with
  | move _ _ ih | write _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ ihq ihr => exact ⟨ihq, ihr⟩
  | goto l => exact fun _ _ ↦ Finset.mem_univ _
  | halt => trivial

/-- No reachable-label oracle is required: the explicit finite type is a support. -/
theorem supports_univ [Fintype A] [Inhabited A]
    (M : A → Stmt Γ A σ) : Supports M Finset.univ :=
  ⟨Finset.mem_univ _, fun q _ ↦ supportsStmt_univ (M q)⟩

/-- Both halting directions on every source input, after the exact block input encoding. -/
theorem halts_iff [Inhabited Γ] [Inhabited σ] [NeZero n] (C : BlockCode Γ)
    (M : Fin n → Stmt Γ (Fin n) σ) (sites : WriteSites M w) (alphabet : Fin m ≃ Γ)
    (primitive : ∀ q, TM1Normalize.OnePrimitive (M q))
    (headFree : ∀ q, Block.AllHeadFree (M q)) (input : List Γ) :
    (TM1.eval (machine C M sites alphabet) (blockInput C input)).Dom ↔
      (TM1.eval M input).Dom :=
  (LocalCertificate.tm1_halts_iff _ _ (decode sites alphabet)
    (rows_refine C M sites alphabet primitive) (decode_initial sites alphabet)
    (blockInput C input)).trans
    (Block.free_dom C M (supports_univ M) (fun q _ ↦ headFree q) input)

end Tables

end ConjectureMachines.Compilation.BinaryTemplates
