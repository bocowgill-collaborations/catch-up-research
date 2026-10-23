import CatchUp.Machine.Lowering.Library

/-! A complete provisional binary transition generator for the actual DAG.
Only its source identity, allocation and initialization are certified here.
The new bank-body and full source simulation proofs remain open. -/
namespace CatchUp.Machine.Lowering
open Turing ConjectureMachines Compilation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

structure Site where
  pc : Nat
  kind : Bank
  next : Nat

def sites : List Site := program.zipIdx.filterMap fun (op,pc) ↦
  match op with
  | .bank kind next => some ⟨pc,kind,next⟩
  | _ => none

def extraSize : Nat := (sites.map (fun s ↦ (bankBody s.kind).size+1)).sum

theorem site_count : sites.length=277 := by decide +kernel

theorem library_counts : saveBody.size=3723 ∧ switchBody.size=15387 ∧
    finishBody.size=3855 ∧ sourceSuccBody.size=8643 := by decide +kernel

theorem extra_count : extraSize=2121700 := by decide +kernel

theorem base_formula (p : Cases.Program) :
    Cases.states p=11288+4638*p.length+462*(Cases.pool p).length := by
  have h := Cases.state_count p []
  change Cases.states p+4=4638*p.length+462*(Cases.pool p).length+4*0+11292 at h
  omega

theorem base_count : Cases.states projection=208978778 := by
  rw [base_formula,pool_length,instruction_count,literal_count]


abbrev totalSize : Nat := 211100478

instance : NeZero totalSize := ⟨by decide +kernel⟩

theorem allocation_count : Cases.states projection+extraSize=totalSize := by
  rw [base_count,extra_count]


def hook (pc : Nat) : Nat :=
  10362+4638*projection.length+462*((projection.take pc).map literalSize).sum+40

structure Placement where
  site : Site
  base : Nat

def place : List Site → Nat → List Placement
  | [],_ => []
  | s::ss,n => ⟨s,n⟩::place ss (n+(bankBody s.kind).size+1)
def placements : List Placement := place sites (Cases.states projection)

def pack (cell : Separate.Bit × Dir × Nat) : Option (Separate.Bit × Dir × Fin totalSize) :=
  let (w,d,n) := cell
  if h : n<totalSize then some (w,d,⟨n,h⟩) else none

/-- Every new operation uses its own full binary body and one entry bridge.
The unique paid push-zero entry is redirected; all unused pool cells stay paid. -/
def transition (q : Fin totalSize) (a : Separate.Bit) :
    Option (Separate.Bit × Dir × Fin totalSize) :=
  if h : q.val<Cases.states projection then
    match placements.find? (fun p ↦ q.val=hook p.site.pc) with
    | some p => pack (a,.right,p.base+(bankBody p.site.kind).size)
    | none => (Cases.machine projection).transition ⟨q.val,h⟩ a |>.bind
        (fun (w,d,n) ↦ pack (w,d,n.val))
  else
    match placements.find? (fun p ↦ p.base≤q.val ∧ q.val≤p.base+(bankBody p.site.kind).size) with
    | none => none
    | some p =>
      let micro := bankBody p.site.kind
      if q.val=p.base+micro.size then pack (a,.left,p.base+micro.entry)
      else (micro.cell (q.val-p.base) a).bind fun (w,d,n) ↦
        pack (w,d,if n<0 then (Cases.entry projection p.site.next).val else p.base+n.toNat)

def machine : Machine totalSize 2 := ⟨transition⟩
abbrev body : BundledMachine 2 := ⟨totalSize,machine⟩
abbrev bits : Array Separate.Bit := #[0,0]
abbrev generated := FlatInit.initialise bits body

theorem body_count : totalSize=211100478 := by
  rfl

theorem generated_count : generated.states=211100482 := by
  rfl

/-- The count is kernel checked. No Halts(M) equivalence is claimed for this
provisional full-program candidate until the listed simulation gaps are closed. -/
def M : Machine 211100482 2 :=
  generated.toMachine

theorem initializes : FlatInit.runFrom M 4 ConjectureMachines.init=
    some (FlatInit.embed bits body ⟨0,Tape.mk₁ bits.toList⟩) :=
  FlatInit.initialise_run bits body

theorem saving : 211100482+177719230=388819712 := by decide +kernel

theorem beats_baseline : generated.states<388819712 := by rw [generated_count];decide

end CatchUp.Machine.Lowering
