import CatchUp.Machine.Words.Transfer

namespace CatchUp.Machine.Words
open Turing ConjectureMachines Compilation Separate
set_option backward.isDefEq.respectTransparency false

def natBanks (data frames : List Nat) := banks (encode data) (encode frames)

theorem push_nat (data frames : List Nat) (n : Nat) :
    run (transferCost (encode data) (encode frames) n)
      ⟨start false false,natBanks (data++[n]) frames⟩ =
      some ⟨doneState (ctx false true true),natBanks data (frames++[n])⟩ := by
  simpa [natBanks,encode,List.flatMap_append,home_swap] using
    word_transfer false (encode data) (encode frames) n

theorem pop_nat (data frames : List Nat) (n : Nat) :
    run (transferCost (encode frames) (encode data) n)
      ⟨start true false,natBanks data (frames++[n])⟩ =
      some ⟨doneState (ctx true true true),natBanks (data++[n]) frames⟩ := by
  simpa [natBanks,banks,encode,List.flatMap_append] using
    word_transfer true (encode frames) (encode data) n

theorem nat_banks_injective (data frames data' frames' : List Nat)
    (h : natBanks data frames=natBanks data' frames') : data=data' ∧ frames=frames' := by
  obtain ⟨hd,hf⟩ := Separate.banks_injective _ _ _ _ h
  exact ⟨encode_injective hd,encode_injective hf⟩

theorem done_transition (c : Fin 8) (a : Bit) :
    machine.transition (doneState c) a =
      if side c then none else some (a,.right,2) := by
  have off : 3+c.val*481+480-3=c.val*481+480 := by omega
  have div : (c.val*481+480)/481=c.val := by omega
  have rem : (c.val*481+480)%481=480 := by omega
  simp [machine,doneState,show ¬3+c.val*481+480<3 by omega,off,div,rem]

theorem transition_two (a : Bit) :
    machine.transition 2 a=some (a,.left,start true false) := rfl

theorem restart_return (T : Tape Bit) :
    run 2 ⟨doneState (ctx false true true),T⟩ = some ⟨start true false,T⟩ := by
  simp [run,FlatInit.runFrom,step,done_transition,ctx_side,transition_two]

/-- The target and return PC are ordinary unbounded natural words on data.
On call, the saved PC moves to the frame bank and target becomes the top PC.
This is the dispatch-ready boundary; no table lookup is hidden in the model. -/
theorem call_correct (data frames : List Nat) (target address : Nat) :
    run (transferCost (encode (data++[target])) (encode frames) address)
      ⟨start false false,natBanks (data++[target,address]) frames⟩ =
      some ⟨doneState (ctx false true true),natBanks (data++[target]) (frames++[address])⟩ := by
  simpa [List.append_assoc] using push_nat (data++[target]) frames address

/-- Return recovers the complete unbounded saved address as the next PC word. -/
theorem return_correct (data frames : List Nat) (address : Nat) :
    run (transferCost (encode frames) (encode data) address)
      ⟨start true false,natBanks data (frames++[address])⟩ =
      some ⟨doneState (ctx true true true),natBanks (data++[address]) frames⟩ :=
  pop_nat data frames address

/-- Actual machine execution of save followed by immediate return. The
controller's two-step return handoff is included, with arbitrary PC value. -/
theorem call_return_correct (data frames : List Nat) (address : Nat) :
    run (2*transferCost (encode data) (encode frames) address+2)
      ⟨start false false,natBanks (data++[address]) frames⟩ =
      some ⟨doneState (ctx true true true),natBanks (data++[address]) frames⟩ := by
  have swap : transferCost (encode frames) (encode data) address =
      transferCost (encode data) (encode frames) address := by
    simp [transferCost,Nat.add_comm]
  rw [show 2*transferCost (encode data) (encode frames) address+2 =
    transferCost (encode data) (encode frames) address+
      (2+transferCost (encode data) (encode frames) address) by omega,
    run_add,push_nat,Option.bind_some,run_add,restart_return,Option.bind_some,← swap]
  exact pop_nat data frames address

end CatchUp.Machine.Words
