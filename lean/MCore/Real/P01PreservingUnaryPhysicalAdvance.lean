import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.MachineRunLemmas

namespace MCore.Real.P01PreservingUnaryPhysicalAdvance

open CanonicalFinalProof
open CanonicalCircuitBits
open P01PreservingUnaryWitnessMachine
open MachineRunLemmas

/-- State after consuming the next unary true and moving left into the erased
unary region.  The remaining blank count is explicit. -/
def seekBlanksConfig
    (blankCount : Nat)
    (traversed : BitString)
    (b : Bool) (tail : BitString)
    (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .seekBlanks
    tape :=
      { left :=
          List.replicate blankCount none ++
            traversed.map some ++ none :: (b :: tail).map some
        head := none
        right := none :: (encodeNat n).map some } }

/-- State after the erased unary blanks have been crossed. -/
def seekBitsConfig
    (remaining : BitString)
    (passed : BitString)
    (b : Bool) (tail : BitString)
    (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  match remaining with
  | [] =>
      { state := .seekBits
        tape :=
          { left := none :: (b :: tail).map some
            head := none
            right := passed.reverse.map some ++
              List.replicate passed.length none ++ none :: (encodeNat n).map some } }
  | x :: xs =>
      { state := .seekBits
        tape :=
          { left := xs.map some ++ none :: (b :: tail).map some
            head := some x
            right := passed.reverse.map some ++
              List.replicate (passed.length + 1) none ++ none :: (encodeNat n).map some } }

@[simp] theorem seekBlanksConfig_state
    (blankCount : Nat) (traversed : BitString)
    (b : Bool) (tail : BitString) (n : Nat) :
    (seekBlanksConfig blankCount traversed b tail n).state = .seekBlanks := rfl

/-- One blank is crossed by seekBlanks. -/
theorem seekBlanks_step_succ
    (k : Nat) (traversed : BitString)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.step
      (seekBlanksConfig (k + 1) traversed b tail n) =
      seekBlanksConfig k traversed b tail n := by
  simp [seekBlanksConfig, preservingUnaryReadMachine, TM.step,
    Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

/-- Crossing exactly the erased unary region leaves the head on the first
traversed witness bit (or the marker if traversed is empty). -/
theorem seekBlanks_run
    (k : Nat) (traversed : BitString)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run k
      (seekBlanksConfig k traversed b tail n) =
      seekBlanksConfig 0 traversed b tail n := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Nat.succ_eq_add_one]
      rw [TM.run]
      simp only [seekBlanksConfig_state]
      simp [preservingUnaryReadMachine]
      rw [seekBlanks_step_succ]
      exact ih

/-- Enter seekBits from the first traversed witness cell. -/
theorem seekBlanks_zero_to_seekBits
    (x : Bool) (xs : BitString)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 1
      (seekBlanksConfig 0 (x :: xs) b tail n) =
      seekBitsConfig (x :: xs) [] b tail n := by
  simp [seekBlanksConfig, seekBitsConfig, preservingUnaryReadMachine,
    TM.run, TM.step, Tape.write, Tape.move]

/-- This file intentionally stops at the first reusable material scan.
The remaining seekBits/return scans are derived in the next forward step. -/

#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBlanks_step_succ
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBlanks_run
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBlanks_zero_to_seekBits

end MCore.Real.P01PreservingUnaryPhysicalAdvance
