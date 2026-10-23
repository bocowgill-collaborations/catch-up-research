/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.Finite
public import Mathlib.Computability.TuringMachine.ToPartrec

/-! Verified compilation of finite-control multi-stack programs to binary Post machines. -/
@[expose] public section

namespace ConjectureMachines.Compilation
open Turing
set_option maxSynthPendingDepth 32

/-- Fixed-width binary encoding with the two laws needed by Mathlib's simulator. -/
structure BlockCode (Γ : Type*) [Inhabited Γ] where
  width : ℕ
  encode : Γ → List.Vector Bool width
  decode : List.Vector Bool width → Γ
  blank : encode default = List.Vector.replicate width false
  roundtrip : ∀ a, decode (encode a) = a

namespace BlockCode
section Enumerated
variable {Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
variable (symbols : List Γ) (cover : ∀ a, a ∈ symbols)

/-- A default-first explicit enumeration. Duplicate nonblank entries are harmless. -/
def alphabet : List Γ := default :: symbols.filter (fun a ↦ a != default)

include cover in
theorem mem_alphabet (a : Γ) : a ∈ alphabet symbols := by
  by_cases h : a = default <;> simp [alphabet, h, cover a]

/-- Position of a symbol in the supplied default-first alphabet enumeration. -/
def rank (a : Γ) : ℕ := (alphabet symbols).idxOf a

include cover in
theorem rank_lt (a : Γ) : rank symbols a < (alphabet symbols).length :=
  List.idxOf_lt_length_iff.mpr (mem_alphabet symbols cover a)

include cover in
theorem rank_injective : Function.Injective (rank symbols) := by
  intro a b h
  have ha := List.getElem?_idxOf (mem_alphabet symbols cover a)
  have hb := List.getElem?_idxOf (mem_alphabet symbols cover b)
  change (alphabet symbols)[rank symbols a]? = some a at ha
  change (alphabet symbols)[rank symbols b]? = some b at hb
  rw [h, hb] at ha
  exact Option.some.inj ha.symm

/-- Width is floor(log₂ enumeration size)+1, within one bit of the minimum for nodup lists. -/
def bits : ℕ := (alphabet symbols).length.log2 + 1

include cover in
theorem rank_lt_pow (a : Γ) : rank symbols a < 2 ^ bits symbols :=
  (rank_lt symbols cover a).trans Nat.lt_log2_self

/-- Little-endian fixed-width symbol encoding, computed via bounded bitvectors. -/
def encodeBits (a : Γ) : List.Vector Bool (bits symbols) :=
  List.Vector.ofFn fun i ↦ (BitVec.ofNat (bits symbols) (rank symbols a)).getLsbD i

include cover in
theorem encodeBits_injective : Function.Injective (encodeBits symbols) := by
  intro a b h
  apply rank_injective symbols cover
  have hb : BitVec.ofNat (bits symbols) (rank symbols a) =
      BitVec.ofNat (bits symbols) (rank symbols b) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hv := congrArg (fun v : List.Vector Bool (bits symbols) ↦ v.get ⟨i, hi⟩) h
    simpa only [encodeBits, List.Vector.get_ofFn] using hv
  have hn := congrArg BitVec.toNat hb
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rank_lt_pow symbols cover a),
    Nat.mod_eq_of_lt (rank_lt_pow symbols cover b)] using hn

theorem encodeBits_blank : encodeBits symbols default =
    List.Vector.replicate (bits symbols) false := by
  apply List.Vector.ext
  intro i
  simp [encodeBits, rank, alphabet]

/-- Finite lookup decoder; unused bit patterns decode to the blank symbol. -/
def decodeBits (v : List.Vector Bool (bits symbols)) : Γ :=
  ((alphabet symbols).find? fun a ↦ decide (encodeBits symbols a = v)).getD default

include cover in
theorem decodeBits_encode (a : Γ) : decodeBits symbols (encodeBits symbols a) = a := by
  cases he : (alphabet symbols).find? (fun b ↦ decide (encodeBits symbols b =
      encodeBits symbols a)) with
  | none =>
    have hn := List.find?_eq_none.mp he a (mem_alphabet symbols cover a)
    simp at hn
  | some b =>
    have hb0 := List.find?_some he
    have hb : encodeBits symbols b = encodeBits symbols a := by simpa using hb0
    have hba := encodeBits_injective symbols cover hb
    simpa only [decodeBits, he, Option.getD_some] using hba

/-- Computable compact code from any explicitly listed finite alphabet. -/
def ofList : BlockCode Γ where
  width := bits symbols
  encode := encodeBits symbols
  decode := decodeBits symbols
  blank := encodeBits_blank symbols
  roundtrip := decodeBits_encode symbols cover
end Enumerated
end BlockCode

section BinaryInput
variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable (C : BlockCode Γ) (M : Λ → TM1.Stmt Γ Λ σ)

/-- Each tape symbol becomes a fixed-width block, with the same left-to-right ordering. -/
def blockInput (l : List Γ) : List Bool := l.flatMap fun a ↦ (C.encode a).toList

theorem blockCfg_init (l : List Γ) :
    TM1to1.trCfg C.encode C.blank (TM1.init l : TM1.Cfg Γ Λ σ) =
      TM1.init (blockInput C l) := by
  simp only [TM1to1.trCfg, TM1.init, Option.map_some]
  congr 1
  simp only [TM1to1.trTape, Tape.mk₁, Tape.mk₂, Tape.mk'_left, Tape.mk'_right₀,
    TM1to1.trTape', ListBlank.flatMap_mk,
    List.flatMap_nil]
  rfl

/-- Binary alphabet reduction preserves termination for the actual finite input tape. -/
theorem blockMachine_dom (l : List Γ) :
    (TM1.eval (TM1to1.tr C.encode C.decode M) (blockInput C l)).Dom ↔
      (TM1.eval M l).Dom :=
  StateTransition.tr_eval_dom (TM1to1.tr_respects C.decode M C.roundtrip)
    (blockCfg_init C l)
end BinaryInput

/-- A fully executable binary Post machine together with its finite starting tape. -/
structure CompiledStack where
  State : Type
  states : Fintype State
  stateEq : DecidableEq State
  initial : Inhabited State
  machine : @TM0.Machine Bool State initial
  input : List Bool

/-- Termination of the compiled machine on its supplied tape. -/
def CompiledStack.Halts (P : CompiledStack) : Prop :=
  (@TM0.eval Bool _ P.initial _ P.machine P.input).Dom

/-- A binary Post program with literal states `Fin (extraStates + 1)` and initial state zero. -/
structure NumberedPost where
  extraStates : ℕ
  machine : TM0.Machine Bool (Fin (extraStates + 1))
  input : List Bool

/-- Halting on the supplied finite input. -/
def NumberedPost.Halts (P : NumberedPost) : Prop := (TM0.eval P.machine P.input).Dom

section StackCompiler
variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)]
variable [Fintype σ] [DecidableEq σ] [DecidableEq Λ] [Inhabited Λ] [Inhabited σ]
variable (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ) (ss : TM2.Supports M S)
variable (C : BlockCode (TM2to1.Γ' K Γ))

/-- The actual binary TM1 produced by the two Mathlib simulators. -/
def stackBinary := TM1to1.tr C.encode C.decode (TM2to1.tr M)

/-- The actual binary Post machine, before restricting its infinite syntax label type. -/
def stackPost := TM1to0.tr (stackBinary M C)

/-- Explicit computable finite support for the generated Post machine. -/
def stackPostSupport : Finset (TM1to0.Λ' (stackBinary M C)) :=
  postSupport (stackBinary M C) (binarySupport (TM2to1.tr M) (stackSupport M S))

include ss in
/-- All reachable generated labels belong to the computed finite support. -/
theorem stackPost_supported : TM0.Supports (stackPost M C) ↑(stackPostSupport M S C) := by
  have h1 : TM1.Supports (TM2to1.tr M) (stackSupport M S) := by
    rw [stackSupport_eq]
    exact TM2to1.tr_supports M ss
  have h2 : TM1.Supports (stackBinary M C)
      (binarySupport (TM2to1.tr M) (stackSupport M S)) := by
    rw [binarySupport_eq]
    exact TM1to1.tr_supports C.encode C.decode (TM2to1.tr M) h1
  rw [stackPostSupport, postSupport_eq]
  exact TM1to0.tr_supports (stackBinary M C) h2

/-- Compile a supported TM2 program. Source labels may be infinite; only `S` is enumerated. -/
def compileStack (k : K) : CompiledStack where
  State := stackPostSupport M S C
  states := inferInstance
  stateEq := @Subtype.instDecidableEq _ _ (postLabelDecidableEq (stackBinary M C))
  initial := restrictedInhabited (stackPost M C) (stackPostSupport M S C)
    (stackPost_supported M S ss C)
  machine := restrictMachine (stackPost M C) (stackPostSupport M S C)
    (stackPost_supported M S ss C)
  input := blockInput C (TM2to1.trInit k [])

/-- Generic both-direction halting equivalence, starting with all source stacks empty. -/
theorem compileStack_halts (k : K) :
    (compileStack M S ss C k).Halts ↔ (TM2.eval M k []).Dom := by
  have hr := restrictMachine_dom (stackPost M C) (stackPostSupport M S C)
    (stackPost_supported M S ss C) (blockInput C (TM2to1.trInit k []))
  have hp : (TM0.eval (stackPost M C) (blockInput C (TM2to1.trInit k []))).Dom ↔
      (TM2.eval M k []).Dom := by
    rw [stackPost, TM1to0.tr_eval]
    exact (blockMachine_dom C (TM2to1.tr M) (TM2to1.trInit k [])).trans
      (TM2to1.tr_eval_dom M k [])
  exact hr.trans hp
/-- Ordered generated control labels, using explicit alphabet and store enumerations. -/
def stackNumberLabels (sourceLabels : List Λ) (symbols : List (TM2to1.Γ' K Γ))
    (stores : List σ) : List (TM1to0.Λ' (stackBinary M C)) :=
  postSupportList (stackBinary M C)
    (binarySupportList (TM2to1.tr M) (stackSupportList M sourceLabels) symbols) stores

omit [Inhabited Λ] [Inhabited σ] in
/-- Ordered support traversal covers exactly the finset support. -/
theorem stackNumberLabels_mem (sourceLabels : List Λ)
    (symbols : List (TM2to1.Γ' K Γ)) (symbolCover : ∀ a, a ∈ symbols)
    (stores : List σ) (storeCover : ∀ v, v ∈ stores)
    (q : TM1to0.Λ' (stackBinary M C)) :
    q ∈ stackNumberLabels M C sourceLabels symbols stores ↔
      q ∈ stackPostSupport M sourceLabels.toFinset C := by
  have hs : (stackSupportList M sourceLabels).toFinset = stackSupport M sourceLabels.toFinset := by
    ext r
    simp only [List.mem_toFinset, mem_stackSupportList, stackSupport_eq]
  have hb : (binarySupportList (TM2to1.tr M) (stackSupportList M sourceLabels) symbols).toFinset =
      binarySupport (TM2to1.tr M) (stackSupport M sourceLabels.toFinset) := by
    ext r
    simp only [List.mem_toFinset, mem_binarySupportList _ _ _ symbolCover,
      binarySupport_eq, hs]
  simp only [stackNumberLabels, mem_postSupportList _ _ _ storeCover,
    stackPostSupport, postSupport_eq, hb]

/-- Fully numbered executable compiler. Data arguments are explicit finite enumerations. -/
def numberedStack (sourceLabels : List Λ) (symbols : List (TM2to1.Γ' K Γ))
    (stores : List σ) (k : K) : NumberedPost where
  extraStates := (stackNumberLabels M C sourceLabels symbols stores).length
  machine := numberMachine (stackPost M C) (stackNumberLabels M C sourceLabels symbols stores)
  input := blockInput C (TM2to1.trInit k [])

/-- Literal finite numbering retains both halting directions of the stack compilation. -/
theorem numberedStack_halts (sourceLabels : List Λ)
    (sourceSupport : TM2.Supports M sourceLabels.toFinset)
    (symbols : List (TM2to1.Γ' K Γ)) (symbolCover : ∀ a, a ∈ symbols)
    (stores : List σ) (storeCover : ∀ v, v ∈ stores) (k : K) :
    (numberedStack M C sourceLabels symbols stores k).Halts ↔ (TM2.eval M k []).Dom := by
  have hn := numberMachine_dom (stackPost M C)
    (stackNumberLabels M C sourceLabels symbols stores)
    (stackPostSupport M sourceLabels.toFinset C)
    (stackPost_supported M sourceLabels.toFinset sourceSupport C)
    (by
      intro q hq
      exact List.mem_cons_of_mem _ ((stackNumberLabels_mem M C sourceLabels symbols
        symbolCover stores storeCover q).mpr hq))
    (blockInput C (TM2to1.trInit k []))
  have hp : (TM0.eval (stackPost M C) (blockInput C (TM2to1.trInit k []))).Dom ↔
      (TM2.eval M k []).Dom := by
    rw [stackPost, TM1to0.tr_eval]
    exact (blockMachine_dom C (TM2to1.tr M) (TM2to1.trInit k [])).trans
      (TM2to1.tr_eval_dom M k [])
  exact hn.trans hp
end StackCompiler

namespace Adequacy
open PartrecToTM2

/-- The four explicit stacks of Mathlib's partial-recursive interpreter. -/
instance partrecStacksFintype : Fintype K' :=
  Fintype.ofList [.main, .rev, .aux, .stack] (by intro k; cases k <;> simp)

/-- The binary tape alphabet of the existing partial-recursive multi-stack interpreter. -/
abbrev PartrecAlphabet := TM2to1.Γ' K' (fun _ ↦ PartrecToTM2.Γ')

/-- Compile any closed partial-recursive list program via its finite supported TM2 interpreter. -/
def compileClosedCode (c : ToPartrec.Code) (C : BlockCode PartrecAlphabet) : CompiledStack :=
  letI : Inhabited PartrecToTM2.Λ' := ⟨trNormal c .halt⟩
  compileStack PartrecToTM2.tr (codeSupp c .halt) (tr_supports c .halt) C K'.main

/-- This backend handles the existing arithmetic/list/fixpoint language on empty input. -/
theorem compileClosedCode_halts (c : ToPartrec.Code) (C : BlockCode PartrecAlphabet) :
    (compileClosedCode c C).Halts ↔ (ToPartrec.Code.eval c []).Dom := by
  let : Inhabited PartrecToTM2.Λ' := ⟨trNormal c .halt⟩
  have hc := compileStack_halts PartrecToTM2.tr (codeSupp c .halt)
    (tr_supports c .halt) C K'.main
  have hi : (TM2.init K'.main [] : TM2.Cfg (fun _ ↦ PartrecToTM2.Γ')
      PartrecToTM2.Λ' (Option PartrecToTM2.Γ')) = PartrecToTM2.init c [] := by
    change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
    congr 1
    funext k
    cases k <;> simp [trList]
  have hp : (TM2.eval PartrecToTM2.tr K'.main []).Dom ↔
      (ToPartrec.Code.eval c []).Dom := by
    change (StateTransition.eval (TM2.step PartrecToTM2.tr) (TM2.init K'.main [])).Dom ↔ _
    rw [hi, PartrecToTM2.tr_eval]
    rfl
  exact hc.trans hp
end Adequacy

end ConjectureMachines.Compilation
