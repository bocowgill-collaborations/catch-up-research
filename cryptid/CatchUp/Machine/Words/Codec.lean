import CatchUp.Machine.Separate.Encoding

namespace CatchUp.Machine.Words
open Separate

/-- Palindromic unary framing. The terminators delimit a word from either end. -/
def word (n : Nat) : List Bit := 0 :: (List.replicate n 1 ++ [0])
def encode (ns : List Nat) : List Bit := ns.flatMap word

def readRun : List Bit → Option (Nat × List Bit)
  | [] => none
  | b::rest => if b=0 then some (0,rest)
    else (readRun rest).map fun (n,tail) ↦ (n+1,tail)

def readWord : List Bit → Option (Nat × List Bit)
  | [] => none
  | b::rest => if b=0 then readRun rest else none

theorem read_run (n : Nat) (rest : List Bit) :
    readRun (List.replicate n 1 ++ 0::rest) = some (n,rest) := by
  induction n with
  | zero => simp [readRun]
  | succ n ih => simp [List.replicate_succ,readRun,ih]

theorem read_word (n : Nat) (rest : List Bit) :
    readWord (word n ++ rest) = some (n,rest) := by
  simpa [word,readWord,List.append_assoc] using read_run n rest

@[simp] theorem word_length (n : Nat) : (word n).length = n+2 := by simp [word]

theorem word_reverse (n : Nat) : (word n).reverse = word n := by
  simp [word,List.reverse_append]

theorem word_cancel (m n : Nat) (u v : List Bit)
    (h : word m++u = word n++v) : m=n ∧ u=v := by
  have hd := congrArg readWord h
  simpa only [read_word,Option.some.injEq,Prod.mk.injEq] using hd

theorem encode_injective : Function.Injective encode := by
  intro ns
  induction ns with
  | nil =>
    intro ms h
    cases ms with
    | nil => rfl
    | cons m ms =>
      have hd := congrArg readWord h
      change none = readWord (word m ++ encode ms) at hd
      rw [read_word] at hd
      cases hd
  | cons n ns ih =>
    intro ms h
    cases ms with
    | nil =>
      have hd := congrArg readWord h
      change readWord (word n ++ encode ns) = none at hd
      rw [read_word] at hd
      cases hd
    | cons m ms =>
      obtain ⟨head,tail⟩ := word_cancel n m (encode ns) (encode ms) h
      exact congrArg₂ List.cons head (ih tail)

end CatchUp.Machine.Words
