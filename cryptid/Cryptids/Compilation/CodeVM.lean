/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Compilation.CodeDAG

/-! # Runtime program counters and data continuations for shared Code tables

The transition function reads only finite table rows, natural-number PCs, and data frames.
Semantic decoding below is used only in the correspondence proofs.
-/

@[expose] public section
namespace ConjectureMachines.Compilation.CodeVM
open Turing.ToPartrec
open CodeDAG (Node DAG)
open StateTransition

set_option backward.isDefEq.respectTransparency false
attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some

/-- The table is acyclic in its explicit row order. -/
def Topological (rows : Array Node) : Prop :=
  ∀ (i : Nat) (node : Node), rows[i]? = some node → node.Below i

/-- Runtime continuations contain row IDs and data, never recursive `Code` values. -/
inductive Frame where
  | halt
  | cons1 (right : Nat) (saved : List Nat) (next : Frame)
  | cons2 (head : Nat) (next : Frame)
  | comp (left : Nat) (next : Frame)
  | fix (body : Nat) (next : Frame)
  deriving DecidableEq, Repr

/-- Evaluation, return, and successful termination are explicit control modes. -/
inductive Config where
  | eval (pc : Nat) (frame : Frame) (values : List Nat)
  | ret (frame : Frame) (values : List Nat)
  | halt (values : List Nat)
  deriving DecidableEq, Repr

/-- One table instruction or one data-continuation instruction. Malformed PCs reject. -/
def step (rows : Array Node) : Config → Option Config
  | .eval pc k v => do
    let node ← rows[pc]?
    return match node with
      | .zero => .ret k (0 :: v)
      | .succ => .ret k [v.headI + 1]
      | .tail => .ret k v.tail
      | .cons left right => .eval left (.cons1 right v k) v
      | .comp left right => .eval right (.comp left k) v
      | .branch left right => if v.headI = 0 then .eval left k v.tail
          else .eval right k ((v.headI - 1) :: v.tail)
      | .fix body => .eval body (.fix body k) v
  | .ret .halt v => some (.halt v)
  | .ret (.cons1 right saved k) v => some (.eval right (.cons2 v.headI k) saved)
  | .ret (.cons2 head k) v => some (.ret k (head :: v))
  | .ret (.comp left k) v => some (.eval left k v)
  | .ret (.fix body k) v => some (if v.headI = 0 then .ret k v.tail
      else .eval body (.fix body k) v.tail)
  | .halt _ => none

def Frame.WF (bound : Nat) : Frame → Prop
  | .halt => True
  | .cons1 pc _ k | .comp pc k | .fix pc k => pc < bound ∧ k.WF bound
  | .cons2 _ k => k.WF bound

def Config.WF (bound : Nat) : Config → Prop
  | .eval pc k _ => pc < bound ∧ k.WF bound
  | .ret k _ => k.WF bound
  | .halt _ => True

theorem step_wf (rows : Array Node) (topology : Topological rows) (c d : Config)
    (wf : c.WF rows.size) (move : step rows c = some d) : d.WF rows.size := by
  cases c with
  | halt v => simp [step] at move
  | ret k v =>
    cases k <;> simp only [step, Config.WF, Frame.WF] at *
    all_goals (try split_ifs at move) <;> cases move <;> simp_all [Frame.WF]
  | eval pc k v =>
    cases row : rows[pc]? with
    | none => simp [step, row] at move
    | some node =>
      have below := topology pc node row
      cases node <;> simp only [step, row, Bind.bind, Option.bind_some] at move
      all_goals (try split_ifs at move) <;> cases move <;>
        simp_all [Node.Below, Config.WF, Frame.WF] <;> omega

/-- Interpret runtime frames only for specification and proof. -/
def Frame.decode (rows : Array Node) : Frame → Cont
  | .halt => .halt
  | .cons1 pc saved k => .cons₁ (CodeDAG.decode rows pc) saved (k.decode rows)
  | .cons2 head k => .cons₂ [head] (k.decode rows)
  | .comp pc k => .comp (CodeDAG.decode rows pc) (k.decode rows)
  | .fix pc k => .fix (CodeDAG.decode rows pc) (k.decode rows)

/-- Proof-only partial denotation of a runtime configuration. -/
def meaning (rows : Array Node) : Config → Part (List Nat)
  | .eval pc k v => (CodeDAG.decode rows pc).eval v >>= (k.decode rows).eval
  | .ret k v => (k.decode rows).eval v
  | .halt v => pure v

private theorem pfun_fix_unfold {α β : Type} (f : α →. β ⊕ α) (a : α) :
    PFun.fix f a = f a >>= fun | .inl b => pure b | .inr next => PFun.fix f next := by
  apply Part.ext
  intro b
  rw [PFun.mem_fix_iff]
  simp only [Bind.bind, Part.mem_bind_iff]
  constructor
  · rintro (stop | ⟨next, forward, result⟩)
    · exact ⟨.inl b, stop, Part.mem_some _⟩
    · exact ⟨.inr next, forward, result⟩
  · rintro ⟨value, atValue, result⟩
    cases value with
    | inl out =>
      have equal : b = out := Part.mem_some_iff.mp result
      exact Or.inl (equal ▸ atValue)
    | inr next => exact Or.inr ⟨next, atValue, result⟩

private theorem code_fix_unfold (f : Code) (v : List Nat) :
    (Code.fix f).eval v = f.eval v >>= fun w ↦
      if w.headI = 0 then pure w.tail else (Code.fix f).eval w.tail := by
  rw [Code.fix_eval, pfun_fix_unfold]
  simp only [Bind.bind, Part.bind_map]
  congr 1
  funext w
  split_ifs <;> rfl

private theorem code_fix_bind (f : Code) (k : Cont) (v : List Nat) :
    ((Code.fix f).eval v >>= k.eval) = f.eval v >>= (Cont.fix f k).eval := by
  rw [code_fix_unfold, bind_assoc]
  congr 1
  funext w
  by_cases h : w.headI = 0 <;> simp [h, Cont.eval, Bind.bind, Part.bind_some]

private theorem code_case_eval (f g : Code) (v : List Nat) :
    (Code.case f g).eval v = if v.headI = 0 then f.eval v.tail
      else g.eval ((v.headI - 1) :: v.tail) := by
  rw [Code.case_eval]
  dsimp only
  cases v.headI <;> rfl

theorem step_meaning (rows : Array Node) (topology : Topological rows) (c d : Config)
    (move : step rows c = some d) : meaning rows c = meaning rows d := by
  cases c with
  | halt v => simp [step] at move
  | ret k v =>
    cases k <;> simp only [step] at move
    all_goals (try split_ifs at move) <;> cases move <;>
      simp_all only [meaning, Frame.decode, Cont.eval, List.headI_cons,
        ite_eq_left, ite_false]
    all_goals exact code_fix_bind _ _ _
  | eval pc k v =>
    cases row : rows[pc]? with
    | none => simp [step, row] at move
    | some node =>
      have decoded := CodeDAG.decode_row rows topology pc node row
      cases node <;> simp only [step, row, Bind.bind, Option.bind_some] at move
      all_goals (try split_ifs at move) <;> cases move <;>
        simp_all only [meaning, Node.build, Code.zero'_eval, Code.succ_eval, Code.tail_eval,
          Code.cons_eval, Code.comp_eval, code_case_eval, Frame.decode, Cont.eval,
          Bind.bind, Part.bind_assoc, Part.pure_eq_some, Part.bind_some,
          ite_eq_left, ite_false]
      all_goals exact code_fix_bind _ _ _

private theorem fix_reaches (rows : Array Node) (body : Nat)
    (complete : ∀ (v out : List Nat) (k : Frame), out ∈ (CodeDAG.decode rows body).eval v →
      Reaches (step rows) (.eval body k v) (.ret k out))
    (v out : List Nat) (k : Frame) (result : out ∈ (Code.fix (CodeDAG.decode rows body)).eval v) :
    Reaches (step rows) (.eval body (.fix body k) v) (.ret k out) := by
  rw [Code.fix_eval] at result
  apply PFun.fixInduction (C := fun v ↦
    Reaches (step rows) (.eval body (.fix body k) v) (.ret k out)) result
  intro current hc ih
  rcases PFun.mem_fix_iff.mp hc with stop | ⟨next, forward, again⟩
  · obtain ⟨value, bodyResult, flag⟩ := (Part.mem_map_iff _).mp stop
    split_ifs at flag with exit
    cases flag
    exact (complete current value (.fix body k) bodyResult).tail (by simp [step, exit])
  · obtain ⟨value, bodyResult, flag⟩ := (Part.mem_map_iff _).mp forward
    split_ifs at flag with exit
    cases flag
    exact (complete current value (.fix body k) bodyResult).trans
      ((Relation.ReflTransGen.single (by simp [step, exit])).trans (ih _ forward))

/-- Every terminating decoded evaluation has a finite runtime path to the same return frame. -/
theorem eval_reaches (rows : Array Node) (topology : Topological rows) (pc : Nat) :
    ∀ (_bound : pc < rows.size) (v out : List Nat) (k : Frame),
      out ∈ (CodeDAG.decode rows pc).eval v →
      Reaches (step rows) (.eval pc k v) (.ret k out) := by
  induction pc using Nat.strong_induction_on with
  | h pc ih =>
    intro bound v out k result
    cases row : rows[pc]? with
    | none =>
      have present := Array.getElem?_eq_getElem bound
      rw [row] at present
      contradiction
    | some node =>
      have below := topology pc node row
      rw [CodeDAG.decode_row rows topology pc node row] at result
      cases node with
      | zero =>
        have equal : out = 0 :: v := by simpa [Node.build] using result
        subst out
        exact .single (by simp [step, row])
      | succ =>
        have equal : out = [v.headI + 1] := by simpa [Node.build] using result
        subst out
        exact .single (by simp [step, row])
      | tail =>
        have equal : out = v.tail := by simpa [Node.build] using result
        subst out
        exact .single (by simp [step, row])
      | cons left right =>
        obtain ⟨head, hh, tail, ht, equal⟩ :
            ∃ head ∈ (CodeDAG.decode rows left).eval v,
              ∃ tail ∈ (CodeDAG.decode rows right).eval v, out = head.headI :: tail := by
          simpa [Node.build, Bind.bind, Part.mem_bind_iff] using result
        subst out
        have first := ih left below.1 (below.1.trans bound) v head (.cons1 right v k) hh
        have second := ih right below.2 (below.2.trans bound) v tail (.cons2 head.headI k) ht
        have bridge : Reaches (step rows) (.ret (.cons1 right v k) head)
            (.eval right (.cons2 head.headI k) v) := .single rfl
        exact (Relation.ReflTransGen.single (by simp [step, row])).trans
          (first.trans (bridge.trans (second.tail rfl)))
      | comp left right =>
        obtain ⟨middle, hm, ho⟩ : ∃ middle ∈ (CodeDAG.decode rows right).eval v,
            out ∈ (CodeDAG.decode rows left).eval middle := by
          simpa [Node.build, Bind.bind, Part.mem_bind_iff] using result
        have first := ih right below.2 (below.2.trans bound) v middle (.comp left k) hm
        have second := ih left below.1 (below.1.trans bound) middle out k ho
        have bridge : Reaches (step rows) (.ret (.comp left k) middle)
            (.eval left k middle) := .single rfl
        exact (Relation.ReflTransGen.single (by simp [step, row])).trans
          (first.trans (bridge.trans second))
      | branch left right =>
        simp only [Node.build, code_case_eval] at result
        by_cases exit : v.headI = 0
        · rw [ite_eq_left exit] at result
          exact (Relation.ReflTransGen.single (by simp [step, row, exit])).trans
            (ih left below.1 (below.1.trans bound) v.tail out k result)
        · rw [ite_eq_right exit] at result
          exact (Relation.ReflTransGen.single (by simp [step, row, exit])).trans
            (ih right below.2 (below.2.trans bound) ((v.headI - 1) :: v.tail) out k result)
      | fix body =>
        have bodyComplete := ih body below (below.trans bound)
        exact (Relation.ReflTransGen.single (by simp [step, row])).trans
          (fix_reaches rows body bodyComplete v out k result)

/-- A finite successful run ends in an explicit output, rather than a rejected malformed PC. -/
def Runs (rows : Array Node) (c : Config) (out : List Nat) : Prop :=
  Reaches (step rows) c (.halt out)

theorem reaches_meaning (rows : Array Node) (topology : Topological rows)
    {c d : Config} (path : Reaches (step rows) c d) : meaning rows c = meaning rows d := by
  induction path with
  | refl => rfl
  | tail _ move ih => exact ih.trans (step_meaning rows topology _ _ move)

theorem reaches_wf (rows : Array Node) (topology : Topological rows)
    {c d : Config} (wf : c.WF rows.size) (path : Reaches (step rows) c d) :
    d.WF rows.size := by
  induction path with
  | refl => exact wf
  | tail _ move ih => exact step_wf rows topology _ _ ih move

/-- Exact output correspondence in both directions, with no hypothesis about a runtime callee. -/
theorem runs_eval_iff (rows : Array Node) (topology : Topological rows) (pc : Nat)
    (bound : pc < rows.size) (v out : List Nat) :
    Runs rows (.eval pc .halt v) out ↔ out ∈ (CodeDAG.decode rows pc).eval v := by
  constructor
  · intro path
    have equal := reaches_meaning rows topology path
    have result : out ∈ meaning rows (.halt out) := Part.mem_some _
    rw [← equal] at result
    simpa only [meaning, Frame.decode, Cont.eval, bind_pure] using result
  · intro result
    exact (eval_reaches rows topology pc bound v out .halt result).tail rfl

/-- Initial configuration has only a natural root PC, data input, and an empty runtime frame. -/
def init (dag : DAG) (input : List Nat) : Config := .eval dag.root .halt input

theorem init_wf (dag : DAG) (valid : dag.Valid) (input : List Nat) :
    (init dag input).WF dag.rows.size := ⟨valid.1, trivial⟩

theorem step_none_iff (rows : Array Node) (c : Config) (wf : c.WF rows.size) :
    step rows c = none ↔ ∃ out, c = .halt out := by
  cases c with
  | eval pc k v =>
    have present := Array.getElem?_eq_getElem wf.1
    simp [step, present]
  | ret k v => cases k <;> simp [step]
  | halt v => simp [step]

theorem runs_iff (dag : DAG) (valid : dag.Valid) (input out : List Nat) :
    Runs dag.rows (init dag input) out ↔ out ∈ dag.decode.eval input :=
  runs_eval_iff dag.rows valid.2 dag.root valid.1 input out

/-- Compiled original programs have exactly the same successful finite runtime runs. -/
theorem runs_compile_iff (code : Code) (input out : List Nat) :
    Runs (CodeDAG.compile code).rows (init (CodeDAG.compile code) input) out ↔
      out ∈ code.eval input := by
  simpa only [CodeDAG.compile_correct] using
    runs_iff (CodeDAG.compile code) (CodeDAG.compile_valid code) input out

/-- Actual transition-system termination is equivalent, with malformed-PC stopping excluded. -/
theorem halts_iff (dag : DAG) (valid : dag.Valid) (input : List Nat) :
    (StateTransition.eval (step dag.rows) (init dag input)).Dom ↔
      (dag.decode.eval input).Dom := by
  constructor
  · intro terminated
    obtain ⟨last, result⟩ := Part.dom_iff_mem.mp terminated
    obtain ⟨path, stop⟩ := StateTransition.mem_eval.mp result
    have wf := reaches_wf dag.rows valid.2 (init_wf dag valid input) path
    obtain ⟨out, rfl⟩ := (step_none_iff dag.rows last wf).mp stop
    exact Part.dom_iff_mem.mpr ⟨out, (runs_iff dag valid input out).mp path⟩
  · intro terminated
    obtain ⟨out, result⟩ := Part.dom_iff_mem.mp terminated
    exact Part.dom_iff_mem.mpr ⟨.halt out, StateTransition.mem_eval.mpr
      ⟨(runs_iff dag valid input out).mpr result, rfl⟩⟩

theorem halts_compile_iff (code : Code) (input : List Nat) :
    (StateTransition.eval (step (CodeDAG.compile code).rows)
      (init (CodeDAG.compile code) input)).Dom ↔ (code.eval input).Dom := by
  simpa only [CodeDAG.compile_correct] using
    halts_iff (CodeDAG.compile code) (CodeDAG.compile_valid code) input

end ConjectureMachines.Compilation.CodeVM
