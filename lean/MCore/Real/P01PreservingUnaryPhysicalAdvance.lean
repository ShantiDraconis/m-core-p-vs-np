import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.MachineRunLemmas

namespace MCore.Real.P01PreservingUnaryPhysicalAdvance

open CanonicalFinalProof
open CanonicalCircuitBits
open P01PreservingUnaryWitnessMachine
open MachineRunLemmas

/-- Exact seekBlanks state: `remaining` erased blanks are still to the left,
while `passed` erased blanks have already been crossed and sit to the right.
The current head is itself a blank. -/
def seekBlanksConfig
    (remaining passed : Nat)
    (traversed : BitString)
    (b : Bool) (tail : BitString)
    (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .seekBlanks
    tape :=
      { left :=
          List.replicate remaining none ++
            traversed.map some ++ none :: (b :: tail).map some
        head := none
        right :=
          List.replicate (passed + 1) none ++
            (encodeNat n).map some } }

@[simp] theorem seekBlanksConfig_state
    (remaining passed : Nat) (traversed : BitString)
    (b : Bool) (tail : BitString) (n : Nat) :
    (seekBlanksConfig remaining passed traversed b tail n).state =
      .seekBlanks := rfl

/-- One physical left move transfers one erased blank from remaining to passed. -/
theorem seekBlanks_step_succ
    (remaining passed : Nat) (traversed : BitString)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.step
      (seekBlanksConfig (remaining + 1) passed traversed b tail n) =
      seekBlanksConfig remaining (passed + 1) traversed b tail n := by
  simp [seekBlanksConfig, preservingUnaryReadMachine, TM.step,
    Tape.write, Tape.move, List.replicate_succ, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Scan all remaining erased blanks. -/
theorem seekBlanks_run
    (remaining passed : Nat) (traversed : BitString)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run remaining
      (seekBlanksConfig remaining passed traversed b tail n) =
      seekBlanksConfig 0 (passed + remaining) traversed b tail n := by
  induction remaining generalizing passed with
  | zero =>
      rfl
  | succ remaining ih =>
      simp only [TM.run, seekBlanksConfig_state]
      simp [preservingUnaryReadMachine]
      rw [seekBlanks_step_succ]
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ih (passed := passed + 1))

/-- With no erased blank left, the next step sees the first traversed bit. -/
def seekBitsEntryConfig
    (x : Bool) (xs : BitString)
    (passed : Nat)
    (b : Bool) (tail : BitString)
    (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .seekBlanks
    tape :=
      { left := xs.map some ++ none :: (b :: tail).map some
        head := some x
        right :=
          List.replicate (passed + 1) none ++ (encodeNat n).map some } }

theorem seekBlanks_zero_step_to_bits
    (x : Bool) (xs : BitString) (passed : Nat)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 1
      (seekBlanksConfig 0 passed (x :: xs) b tail n) =
      seekBitsEntryConfig x xs (passed + 1) b tail n := by
  simp [seekBlanksConfig, seekBitsEntryConfig, preservingUnaryReadMachine,
    TM.run, TM.step, Tape.write, Tape.move, List.replicate_succ,
    List.append_assoc, Nat.add_assoc]

/-- seekBits state after one traversed bit has been crossed. -/
def seekBitsConfig
    (remaining : BitString)
    (passedRev : BitString)
    (blankPad : Nat)
    (b : Bool) (tail : BitString)
    (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  match remaining with
  | [] =>
      { state := .seekBits
        tape :=
          { left := none :: (b :: tail).map some
            head := none
            right :=
              passedRev.map some ++
                List.replicate blankPad none ++ (encodeNat n).map some } }
  | y :: ys =>
      { state := .seekBits
        tape :=
          { left := ys.map some ++ none :: (b :: tail).map some
            head := some y
            right :=
              passedRev.map some ++
                List.replicate blankPad none ++ (encodeNat n).map some } }

theorem seekBits_entry_step
    (x : Bool) (xs : BitString) (passed : Nat)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 1
      (seekBitsEntryConfig x xs passed b tail n) =
      seekBitsConfig xs [x] (passed + 1) b tail n := by
  cases xs <;>
    simp [seekBitsEntryConfig, seekBitsConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move, List.append_assoc]

#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBlanks_step_succ
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBlanks_run
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBlanks_zero_step_to_bits
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBits_entry_step

end MCore.Real.P01PreservingUnaryPhysicalAdvance
