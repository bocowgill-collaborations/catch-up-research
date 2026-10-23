import CatchUp.Machine.Lowering.Switch.Finite

/-! Local equations for the existing two extraction-shift blocks. Every equation
is checked against switchBody; these definitions do not replace its cells. -/
namespace CatchUp.Machine.Lowering.Switch.Extract
open Turing ConjectureMachines Compilation Separate Words
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

def S (flag : Bit) (i : Nat) : Nat := 1423+43*flag.val+i

def shiftRow (flag : Bit) (i : Nat) (a : Bit) : Option Cell :=
  let go (w : Bit) (d : Dir) (k : Nat) := some (w,d,Int.ofNat (S flag k))
  match i with
  | 0 => go a .left 1
  | 1 => go a .left 2
  | 2 => if a=0 then go flag .left 3 else go 1 .left 6
  | 3 => go 0 .right 4
  | 4 => go a .right 5
  | 5 => some (a,.right,15384)
  | 6 => go a .left 7
  | 7 => if a=0 then go 0 .left 8 else go 1 .left 19
  | 8 => if a=0 then go 0 .right 9 else go 1 .right 13
  | 9 => go a .right 10
  | 10 => go 0 .right 11
  | 11 => go 0 .right 12
  | 12 => go a .right 32
  | 13 => go a .right 14
  | 14 => go 1 .right 15
  | 15 => go 0 .left 16
  | 16 => go a .left 17
  | 17 => go a .left 18
  | 18 => go a .left 7
  | 19 => if a=0 then go 0 .right 20 else go 1 .right 26
  | 20 => go a .right 21
  | 21 => go 0 .right 22
  | 22 => go 1 .left 23
  | 23 => go a .left 24
  | 24 => go a .left 25
  | 25 => go a .left 7
  | 26 => go a .right 27
  | 27 => go 1 .right 28
  | 28 => go 1 .left 29
  | 29 => go a .left 30
  | 30 => go a .left 31
  | 31 => go a .left 7
  | 32 => if a=0 then go 0 .left 34 else go 1 .right 33
  | 33 => go a .right 32
  | 34 => if a=0 then go 0 .right 0 else go 1 .right 35
  | 35 => go a .right 36
  | 36 => go a .right 32
  | _ => none

theorem shift_cell (flag : Bit) (i : Nat) (hi : i<37) (a : Bit) :
    switchBody.cell (S flag i) a=shiftRow flag i a := by
  interval_cases i <;> fin_cases flag <;> fin_cases a <;> rfl

abbrev Kind := Fin 3
def B (k : Kind) : Bit := if k.val=1 then 1 else 0
def O (k : Kind) : Nat := 1+461*k.val
def P (k : Kind) : Nat := O k+50+5*(B k).val
def R (k : Kind) : Nat := 1383+4*k.val
def N (k : Kind) : Nat := if k.val=2 then 1416 else 1398
def C (k : Kind) : Nat := 1401+5*k.val
def Q (k : Kind) (i : Nat) : Nat := if i<4 then R k+i else C k+(i-4)

def copyRow (k : Kind) (i : Nat) (a : Bit) : Option Cell :=
  let go (w : Bit) (d : Dir) (j : Nat) := some (w,d,Int.ofNat (Q k j))
  match i with
  | 0 => go a .left 1
  | 1 => go a .left 2
  | 2 => if a=0 then go 1 .left 3 else go 1 .left 1
  | 3 => some (a,.left,Int.ofNat (N k))
  | 4 => go a .right 5
  | 5 => go a .right 6
  | 6 => if a=0 then go a .right 7 else go a .right 8
  | 7 => some (a,.left,Int.ofNat (P k))
  | 8 => go a .right 6
  | _ => none

theorem copy_cell (k : Kind) (i : Nat) (hi : i<9) (a : Bit) :
    switchBody.cell (Q k i) a=copyRow k i a := by
  interval_cases i <;> fin_cases k <;> fin_cases a <;> rfl

def startRow (i : Nat) (a : Bit) : Option Cell :=
  match i with
  | 0 => some (a,.left,1396)
  | 1 => some (a,.left,1397)
  | 2 => if a=0 then none else some (0,.left,1399)
  | 3 => if a=0 then none else some (0,.left,1400)
  | 4 => if a=0 then some (0,.right,1401) else none
  | 5 => if a=0 then some (0,.right,1411) else some (1,.right,1406)
  | _ => none

theorem start_cell (i : Nat) (hi : i<6) (a : Bit) :
    switchBody.cell (1395+i) a=startRow i a := by
  interval_cases i <;> fin_cases a <;> rfl

def M (flag : Bit) (i : Nat) : Nat := 1417+43*flag.val+i

def markRow (flag : Bit) (i : Nat) (a : Bit) : Option Cell :=
  let go (w : Bit) (j : Nat) := some (w,.right,Int.ofNat (M flag j))
  match i with
  | 0 => go 1 1
  | 1 => go a 2
  | 2 => go a 3
  | 3 => if a=0 then go a 4 else go a 5
  | 4 => some (a,.left,Int.ofNat (S flag 0))
  | 5 => go a 3
  | _ => none

theorem mark_cell (flag : Bit) (i : Nat) (hi : i<6) (a : Bit) :
    switchBody.cell (M flag i) a=markRow flag i a := by
  interval_cases i <;> fin_cases flag <;> fin_cases a <;> rfl

theorem mark_entry_cell (a : Bit) :
    switchBody.cell 1416 a=some (0,.left,Int.ofNat (M a 0)) := by
  fin_cases a <;> rfl

end CatchUp.Machine.Lowering.Switch.Extract
