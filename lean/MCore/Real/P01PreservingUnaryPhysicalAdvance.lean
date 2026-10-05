import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.MachineRunLemmas

namespace MCore.Real.P01PreservingUnaryPhysicalAdvance

open CanonicalFinalProof
open CanonicalCircuitBits
open P01PreservingUnaryWitnessMachine
open MachineRunLemmas

/-- seekBlanks configuration with k additional erased unary blanks still to the
left of the blank currently under the head. -/
def seekBlanksConfig
    (k : Nat)
    (traversed : BitString)
    (b : Bool) (tail : BitString)
    (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .seekBlanks
    tape :=
      { left :=
          List.replicate k none ++
            traversed.map some ++ none :: (b :: tail).map some
        head := none
        right :=
          List.replicate (traversed.length - k) none ++
            none :: (encodeNat n).map some } }

@[simp] theorem seekBlanksConfig_state
    (k : Nat) (traversed : BitString)
    (b : Bool) (tail : BitString) (n : Nat) :
    (seekBlanksConfig k traversed b tail n).state = .seekBlanks := rfl

/-- One erased unary blank is crossed. -/
theorem seekBlanks_step_succ
    (k : Nat) (traversed : BitString)
    (b : Bool) (tail : BitString) (n : Nat)
    (hk : k < traversed.length) :
    preservingUnaryReadMachine.step
      (seekBlanksConfig (k + 1) traversed b tail n) =
      seekBlanksConfig k traversed b tail n := by
  simp [seekBlanksConfig, preservingUnaryReadMachine, TM.step,
    Tape.write, Tape.move, List.replicate_succ, List.append_assoc]
  omega

/-- After all erased unary blanks have been crossed, the head is on the first
traversed witness bit.  This representation is only used for a nonempty prefix. -/
def seekBitsEntryConfig
    (x : Bool) (xs : BitString)
    (b : Bool) (tail : BitString)
    (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .seekBlanks
    tape :=
      { left := xs.map some ++ none :: (b :: tail).map some
        head := some x
        right := List.replicate (xs.length + 2) none ++
          (encodeNat n).map some } }

/-- Concrete bridge from the final blank-crossing configuration to the first
traversed witness bit. -/
theorem seekBlanks_zero_step_to_bits
    (x : Bool) (xs : BitString)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 1
      (seekBlanksConfig 0 (x :: xs) b tail n) =
      seekBitsEntryConfig x xs b tail n := by
  simp [seekBlanksConfig, seekBitsEntryConfig, preservingUnaryReadMachine,
    TM.run, TM.step, Tape.write, Tape.move, List.replicate_succ,
    List.append_assoc]

/-- The seekBlanks state now sees a witness bit and enters seekBits in one
physical step. -/
def seekBitsConfig
    (xs : BitString)
    (passedHead : Bool)
    (b : Bool) (tail : BitString)
    (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  match xs with
  | [] =>
      { state := .seekBits
        tape :=
          { left := none :: (b :: tail).map some
            head := none
            right := some passedHead ::
              List.replicate 2 none ++ (encodeNat n).map some } }
  | y :: ys =>
      { state := .seekBits
        tape :=
          { left := ys.map some ++ none :: (b :: tail).map some
            head := some y
            right := some passedHead ::
              List.replicate 2 none ++ (encodeNat n).map some } }

theorem seekBits_entry_step
    (x : Bool) (xs : BitString)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 1
      (seekBitsEntryConfig x xs b tail n) =
      seekBitsConfig xs x b tail n := by
  cases xs <;>
    simp [seekBitsEntryConfig, seekBitsConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move, List.replicate_succ,
      List.append_assoc]

#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBlanks_step_succ
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBlanks_zero_step_to_bits
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBits_entry_step

end MCore.Real.P01PreservingUnaryPhysicalAdvance
