import CatchUp.Machine.Lowering.Source
import CatchUp.Machine.Comp.Partial

/-! Whole pinned DAG lowering. Four bank operations have concrete binary bodies
in Library, but their source simulation proofs are not asserted by this file. -/
namespace CatchUp.Machine.Lowering
open ConjectureMachines Compilation
set_option backward.isDefEq.respectTransparency false

inductive Bank where
  | save | switch | finish | sourceSucc
  deriving DecidableEq, Repr

inductive Op where
  | core (instruction : Cases.Instruction)
  | bank (kind : Bank) (next : Nat)
  deriving DecidableEq, Repr

def width : CodeDAG.Node → Nat
  | .comp _ _ => 7 | .cons _ _ => 10 | .fix _ => 7 | _ => 1

def entries : List Nat :=
  ((Source.rows.toList.scanl (fun pc node ↦ pc+width node) 7).take Source.rows.size)
def address (node : Nat) : Nat := entries[node]?.getD 0

def block (node : CodeDAG.Node) (q : Nat) : List Op :=
  match node with
  | .zero => [.core (.push 0 4)]
  | .tail => [.core .tail]
  | .succ => [.bank .sourceSucc 6]
  | .branch f g => [.core (.caseOf (address f) (address g))]
  | .comp f g =>
    [.core (.push (address g) (q+1)),.core (.push (q+3) (q+2)),.core .call,
      .core (.push (address f) (q+4)),.core (.push (q+6) (q+5)),.core .call,.core .ret]
  | .cons f g =>
    [.bank .save (q+1),.core (.push (address f) (q+2)),.core (.push (q+4) (q+3)),
      .core .call,.bank .switch (q+5),.core (.push (address g) (q+6)),
      .core (.push (q+8) (q+7)),.core .call,.bank .finish (q+9),.core .ret]
  | .fix f =>
    [.core (.push (address f) (q+1)),.core (.push (q+3) (q+2)),.core .call,
      .core (.caseOf 4 (q+4)),.core (.push (address 1) (q+5)),
      .core (.push q (q+6)),.core .call]

def program : List Op :=
  [.core (.push (address Source.dag.root) 1),.core (.push 3 2),.core .call,
    .core .halt,.core .ret,.core (.push 0 6),.core .succ]++
  Source.rows.toList.zipIdx.flatMap (fun (node,i) ↦ block node (address i))

/-- A unique paid literal entry is intercepted by each bank body. Its unused
push-zero pool cells remain allocated and counted. This is allocation only. -/
def project : Op → Cases.Instruction
  | .core op => op | .bank _ next => .push 0 next

def projection : Cases.Program := program.map project

def literalSize : Cases.Instruction → Nat
  | .push n _ => n+2 | _ => 0

theorem pool_length (p : Cases.Program) :
    (Cases.pool p).length=(p.map literalSize).sum := by
  induction p with
  | nil => rfl
  | cons op rest ih =>
    change (Cases.chunk op++Cases.pool rest).length=(literalSize op::rest.map literalSize).sum
    rw [List.length_append,ih,List.sum_cons]
    congr 1
    cases op <;> simp [Cases.chunk,literalSize,Cases.fragment_length]

/-- This imports the already checked literal source identity, not the
unfinished Catch-Up conjecture theorem. No compiler correctness is inferred. -/
theorem source_identity : Source.dag.decode=CatchUp.Machine.Program.program := Source.correct

theorem instruction_count : projection.length=1555 := by decide +kernel

theorem literal_count : (projection.map literalSize).sum=436700 := by decide +kernel

end CatchUp.Machine.Lowering
