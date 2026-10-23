/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.AssemblyFast
public import Cryptids.Compilation.Binary
public import Cryptids.Compilation.Init

/-! # Constructive ordered compilation of partial-recursive list programs

The support lists below mirror Mathlib's finite support proof, retaining duplicates until the
existing numbered backend removes them. No conversion from a finset to a list is executed.
-/

@[expose] public section
namespace ConjectureMachines.Compilation.CodeBackend
open Turing PartrecToTM2 K'

/-- All five possible values of the interpreter's local store. -/
def stores : List (Option Γ') := [none, some .consₗ, some .cons, some .bit0, some .bit1]

@[simp] theorem mem_stores (s : Option Γ') : s ∈ stores := by
  cases s with
  | none => simp [stores]
  | some s => cases s <;> simp [stores]

/-- Downward control-label traversal, including every branch of a store read. -/
def trStmtsList : Λ' → List Λ'
  | q@(.move _ _ _ next) => q :: trStmtsList next
  | q@(.push _ _ next) => q :: trStmtsList next
  | q@(.read next) => q :: stores.flatMap (fun s ↦ trStmtsList (next s))
  | q@(.clear _ _ next) => q :: trStmtsList next
  | q@(.copy next) => q :: trStmtsList next
  | q@(.succ next) => q :: unrev next :: trStmtsList next
  | q@(.pred zero succ) => q :: (trStmtsList zero ++ unrev succ :: trStmtsList succ)
  | q@(.ret _) => [q]

theorem trStmtsList_toFinset (q : Λ') : (trStmtsList q).toFinset = trStmts₁ q := by
  induction q <;> ext r <;> simp_all [trStmtsList, trStmts₁]
  simp_all only [← List.mem_toFinset]

/-- Labels visited while evaluating a code expression, before evaluating its continuation. -/
def codeSuppList' : ToPartrec.Code → Cont' → List Λ'
  | c@.zero', k => trStmtsList (trNormal c k)
  | c@.succ, k => trStmtsList (trNormal c k)
  | c@.tail, k => trStmtsList (trNormal c k)
  | c@(.cons f fs), k =>
    trStmtsList (trNormal c k) ++
      (codeSuppList' f (.cons₁ fs k) ++
        (trStmtsList
          (move₂ (fun _ ↦ false) main aux <|
            move₂ (fun s ↦ s = Γ'.consₗ) stack main <|
              move₂ (fun _ ↦ false) aux stack <| trNormal fs (.cons₂ k)) ++
          (codeSuppList' fs (.cons₂ k) ++ trStmtsList (head stack <| .ret k))))
  | c@(.comp f g), k =>
    trStmtsList (trNormal c k) ++
      (codeSuppList' g (.comp f k) ++ (trStmtsList (trNormal f k) ++ codeSuppList' f k))
  | c@(.case f g), k =>
    trStmtsList (trNormal c k) ++ (codeSuppList' f k ++ codeSuppList' g k)
  | c@(.fix f), k =>
    trStmtsList (trNormal c k) ++
      (codeSuppList' f (.fix f k) ++
        (trStmtsList (.clear natEnd main <| trNormal f (.fix f k)) ++ [.ret k]))

theorem codeSuppList'_toFinset (c : ToPartrec.Code) (k : Cont') :
    (codeSuppList' c k).toFinset = codeSupp' c k := by
  induction c generalizing k <;>
    simp_all only [codeSuppList', codeSupp', List.toFinset_append, trStmtsList_toFinset,
      List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]

/-- Labels used by a data-free continuation, excluding the initial return label. -/
def contSuppList : Cont' → List Λ'
  | .cons₁ fs k =>
    trStmtsList
      (move₂ (fun _ ↦ false) main aux <|
        move₂ (fun s ↦ s = Γ'.consₗ) stack main <|
          move₂ (fun _ ↦ false) aux stack <| trNormal fs (.cons₂ k)) ++
      (codeSuppList' fs (.cons₂ k) ++ (trStmtsList (head stack <| .ret k) ++ contSuppList k))
  | .cons₂ k => trStmtsList (head stack <| .ret k) ++ contSuppList k
  | .comp f k => codeSuppList' f k ++ contSuppList k
  | .fix f k => codeSuppList' (.fix f) k ++ contSuppList k
  | .halt => []

theorem contSuppList_toFinset (k : Cont') : (contSuppList k).toFinset = contSupp k := by
  induction k <;>
    simp_all only [contSuppList, contSupp, List.toFinset_append, trStmtsList_toFinset,
      codeSuppList'_toFinset, List.toFinset_nil]

/-- The complete finite control support, in deterministic traversal order. -/
def codeSuppList (c : ToPartrec.Code) (k : Cont') : List Λ' :=
  codeSuppList' c k ++ contSuppList k

theorem codeSuppList_toFinset (c : ToPartrec.Code) (k : Cont') :
    (codeSuppList c k).toFinset = codeSupp c k := by
  simp only [codeSuppList, codeSupp, List.toFinset_append, codeSuppList'_toFinset,
    contSuppList_toFinset]

/-- The simultaneous tape symbol for four stacks and one bottom marker. -/
def symbol (bottom : Bool) (a b c d : Option Γ') : Adequacy.PartrecAlphabet :=
  (bottom, fun | .main => a | .rev => b | .aux => c | .stack => d)

/-- Explicit enumeration of all `2 * 5^4 = 1250` simultaneous tape symbols. -/
def symbols : List Adequacy.PartrecAlphabet :=
  [false, true].flatMap fun bottom ↦ stores.flatMap fun a ↦ stores.flatMap fun b ↦
    stores.flatMap fun c ↦ stores.map fun d ↦ symbol bottom a b c d

theorem symbols_cover (s : Adequacy.PartrecAlphabet) : s ∈ symbols := by
  obtain ⟨bottom, values⟩ := s
  have reconstruct : symbol bottom (values main) (values rev) (values aux) (values stack) =
      (bottom, values) := by
    apply Prod.ext
    · rfl
    · funext k
      cases k <;> rfl
  rw [← reconstruct]
  exact List.mem_flatMap.mpr ⟨bottom, by cases bottom <;> simp,
    List.mem_flatMap.mpr ⟨values main, mem_stores _,
      List.mem_flatMap.mpr ⟨values rev, mem_stores _,
        List.mem_flatMap.mpr ⟨values aux, mem_stores _,
          List.mem_map.mpr ⟨values stack, mem_stores _, rfl⟩⟩⟩⟩⟩

set_option maxRecDepth 32768 in
theorem symbols_length : symbols.length = 1250 := by decide

/-- Base-five digit for one stack coordinate; the absent symbol is digit zero. -/
def wordRank : Option Γ' → Nat
  | none => 0
  | some .consₗ => 1
  | some .cons => 2
  | some .bit0 => 3
  | some .bit1 => 4

def wordUnrank : Nat → Option Γ'
  | 1 => some .consₗ
  | 2 => some .cons
  | 3 => some .bit0
  | 4 => some .bit1
  | _ => none

theorem wordRank_lt (s : Option Γ') : wordRank s < 5 := by
  cases s with
  | none => decide
  | some s => cases s <;> decide

@[simp] theorem wordUnrank_rank (s : Option Γ') : wordUnrank (wordRank s) = s := by
  cases s with
  | none => rfl
  | some s => cases s <;> rfl

/-- Constant-time mixed-radix rank, agreeing with the explicit enumeration's order. -/
def symbolRank (s : Adequacy.PartrecAlphabet) : Nat :=
  (if s.1 then 625 else 0) + 125 * wordRank (s.2 main) + 25 * wordRank (s.2 rev) +
    5 * wordRank (s.2 aux) + wordRank (s.2 stack)

theorem symbolRank_lt (s : Adequacy.PartrecAlphabet) : symbolRank s < 1250 := by
  have := wordRank_lt (s.2 main)
  have := wordRank_lt (s.2 rev)
  have := wordRank_lt (s.2 aux)
  have := wordRank_lt (s.2 stack)
  cases hb : s.1 <;> simp only [symbolRank, hb, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Division recovers each coordinate directly; unused binary words still decode to a symbol. -/
def symbolUnrank (n : Nat) : Adequacy.PartrecAlphabet :=
  symbol (decide (625 ≤ n)) (wordUnrank (n / 125 % 5)) (wordUnrank (n / 25 % 5))
    (wordUnrank (n / 5 % 5)) (wordUnrank (n % 5))

theorem symbolUnrank_rank (s : Adequacy.PartrecAlphabet) :
    symbolUnrank (symbolRank s) = s := by
  obtain ⟨b, v⟩ := s
  have h0 := wordRank_lt (v main)
  have h1 := wordRank_lt (v rev)
  have h2 := wordRank_lt (v aux)
  have h3 := wordRank_lt (v stack)
  apply Prod.ext
  · change decide (625 ≤ symbolRank (b, v)) = b
    cases b <;> simp [symbolRank] <;> omega
  · funext k
    cases k <;> simp only [symbolUnrank, symbol]
    all_goals
      conv_rhs => rw [← wordUnrank_rank (v _)]
      congr 1
      cases b <;> simp [symbolRank] <;> omega

/-- Little-endian eleven-bit encoding, using arithmetic rather than alphabet lookup. -/
def encodeSymbol (s : Adequacy.PartrecAlphabet) : List.Vector Bool 11 :=
  List.Vector.ofFn fun i ↦ (BitVec.ofNat 11 (symbolRank s)).getLsbD i

/-- Read eleven bits without enumerating or comparing candidate alphabet symbols. -/
def readBits (v : List.Vector Bool 11) : BitVec 11 :=
  BitVec.cast v.2 (BitVec.ofBoolListLE v.toList)

set_option backward.isDefEq.respectTransparency false in
theorem readBits_encodeSymbol (s : Adequacy.PartrecAlphabet) :
    readBits (encodeSymbol s) = BitVec.ofNat 11 (symbolRank s) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [readBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, encodeSymbol,
    List.Vector.toList_ofFn]
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

def decodeSymbol (v : List.Vector Bool 11) : Adequacy.PartrecAlphabet :=
  symbolUnrank (readBits v).toNat

theorem encodeSymbol_blank : encodeSymbol default = List.Vector.replicate 11 false := by
  have h : symbolRank default = 0 := rfl
  apply List.Vector.ext
  intro i
  simp only [encodeSymbol, List.Vector.get_ofFn, h, BitVec.getLsbD_zero,
    List.Vector.get_replicate]

theorem decode_encodeSymbol (s : Adequacy.PartrecAlphabet) :
    decodeSymbol (encodeSymbol s) = s := by
  have h : symbolRank s < 2 ^ 11 := (symbolRank_lt s).trans (by decide)
  simpa only [decodeSymbol, readBits_encodeSymbol, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h] using symbolUnrank_rank s

/-- Direct arithmetic codec for the complete alphabet; no search table is executed. -/
def blockCode : BlockCode Adequacy.PartrecAlphabet :=
  ⟨11, encodeSymbol, decodeSymbol, encodeSymbol_blank, decode_encodeSymbol⟩

theorem blockCode_width : blockCode.width = 11 := rfl

instance stackSymbolHashable : Hashable Γ' where
  hash
    | .consₗ => 0
    | .cons => 1
    | .bit0 => 2
    | .bit1 => 3

/-- Hashing is constant in alphabet size; exact equality still compares all four stacks. -/
instance alphabetHashable : Hashable Adequacy.PartrecAlphabet :=
  ⟨fun s ↦ mixHash (hash s.1) (mixHash (hash (s.2 main))
    (mixHash (hash (s.2 rev)) (mixHash (hash (s.2 aux)) (hash (s.2 stack)))))⟩

/-- Closed partial-recursive code compiled to an explicitly numbered binary Post machine. -/
def post (c : ToPartrec.Code) : NumberedPost :=
  letI : Inhabited Λ' := ⟨trNormal c .halt⟩
  fastStack tr blockCode (codeSuppList c .halt) symbols stores main

theorem post_halts (c : ToPartrec.Code) : (post c).Halts ↔ (c.eval []).Dom := by
  let : Inhabited Λ' := ⟨trNormal c .halt⟩
  have support : TM2.Supports tr (codeSuppList c .halt).toFinset := by
    rw [codeSuppList_toFinset]
    exact tr_supports c .halt
  have hc := fastStack_halts tr blockCode (codeSuppList c .halt) support
    symbols symbols_cover stores mem_stores main
  have hi : (TM2.init main [] : TM2.Cfg (fun _ ↦ Γ') Λ' (Option Γ')) =
      PartrecToTM2.init c [] := by
    change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
    congr 1
    funext k
    cases k <;> simp [trList]
  have hp : (TM2.eval tr main []).Dom ↔ (c.eval []).Dom := by
    change (StateTransition.eval (TM2.step tr) (TM2.init main [])).Dom ↔ _
    rw [hi, PartrecToTM2.tr_eval]
    rfl
  exact hc.trans hp

/-- The input to a closed code is just the encoded simultaneous stack-bottom marker. -/
theorem post_input_length (c : ToPartrec.Code) : (post c).input.length = 11 := by
  simp [post, fastStack, blockInput, TM2to1.trInit, blockCode_width]
  rfl

/-- Write-and-move conversion, with one main and one bounce state per Post state. -/
def body (p : NumberedPost) : BundledMachine 2 :=
  ⟨(p.extraStates + 1) + (p.extraStates + 1), Binary.compile p.machine⟩

/-- A closed code with its complete finite input initialized from the blank tape. -/
def generated (c : ToPartrec.Code) : BundledMachine 2 :=
  let p := post c
  Init.initialise (p.input.map Binary.encodeSymbol) (body p)

/-- Both halting directions hold for arbitrary closed code, without deciding its value. -/
theorem generated_halts (c : ToPartrec.Code) : (generated c).Halts ↔ (c.eval []).Dom :=
  (Init.initialise_halts _ _).trans
    ((Binary.compile_halts_input _ _).trans (post_halts c))

/-- All 22 initializer states are included in the total binary-machine state count. -/
theorem generated_states (c : ToPartrec.Code) :
    (generated c).states = 2 * ((post c).extraStates + 1) + 22 := by
  simp only [generated, Init.initialise_states, body, List.length_map, post_input_length]
  omega

/-- Small halting code exercises the full generic theorem, including blank initialization. -/
theorem zero_halts : (generated .zero').Halts := by
  apply (generated_halts .zero').mpr
  exact trivial

/-- A positive continuation flag forever is preserved as genuine target nontermination. -/
theorem spin_not_halts : ¬ (generated (.fix (.cons .succ .nil))).Halts := by
  intro h
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp ((generated_halts _).mp h)
  rw [ToPartrec.Code.fix_eval] at hv
  apply PFun.fixInduction' (C := fun _ ↦ False) hv
  · intro w hw
    simp [ToPartrec.Code.cons_eval, ToPartrec.Code.succ_eval, ToPartrec.Code.nil_eval,
      Bind.bind] at hw
  · exact fun _ _ _ _ ih ↦ ih

end ConjectureMachines.Compilation.CodeBackend
