import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01PreservingUnarySuccessorCycle

open CanonicalFinalProof
open CanonicalCircuitBits
open P01WitnessIndexedRead
open P01PreservingUnaryWitnessMachine
open MachineRunLemmas

/-!
Material decomposition of one nonzero preserving-reader cycle.

These are concrete machine configurations.  They expose the four finite
phases needed for the universal successor proof:
erased-unary blanks, traversed prefix bits, witness-marker shift, and return.
No endpoint claim is introduced here.
-/

/-- After consuming the current unary true, the machine scans the erased
unary blanks to the left. -/
def seekBlanksConfig
    (pad : Nat) (pref : BitString) (b : Bool) (suffix : BitString)
    (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .seekBlanks
    tape :=
      { left :=
          List.replicate pad none ++
            pref.map some ++ none :: some b :: suffix.map some
        head := none
        right := none :: (encodeNat n).map some } }

/-- State reached after all erased unary blanks have been crossed and the
first traversed witness bit is at the head. -/
def seekPrefixHeadConfig
    (prefTail : BitString) (first : Bool)
    (b : Bool) (suffix : BitString) (pad : Nat) (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .seekBlanks
    tape :=
      { left :=
          prefTail.map some ++ none :: some b :: suffix.map some
        head := some first
        right := List.replicate (pad + 2) none ++ (encodeNat n).map some } }

/-- After consuming the first traversed bit, seekBits crosses the remaining
prefix and stops at the unique witness marker. -/
def seekBitsConfig
    (remaining : BitString) (processedRev : List (Option Bool))
    (b : Bool) (suffix : BitString) (rightTail : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  match remaining with
  | [] =>
      { state := .seekBits
        tape :=
          { left := some b :: suffix.map some
            head := none
            right := processedRev ++ rightTail } }
  | x :: xs =>
      { state := .seekBits
        tape :=
          { left := xs.map some ++ none :: some b :: suffix.map some
            head := some x
            right := processedRev ++ rightTail } }

/-- Crossing one erased blank preserves every Boolean payload cell. -/
theorem seekBlanks_step
    (pad : Nat) (pref : BitString) (b : Bool) (suffix : BitString)
    (n : Nat) :
    preservingUnaryReadMachine.step
      (seekBlanksConfig (pad + 1) pref b suffix n) =
      seekBlanksConfig pad pref b suffix n := by
  simp [seekBlanksConfig, preservingUnaryReadMachine, TM.step,
    Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

/-- Crossing all erased blanks reaches the first traversed Boolean without
changing the witness payload. -/
theorem seekBlanks_run
    (pad : Nat) (first : Bool) (prefTail : BitString)
    (b : Bool) (suffix : BitString) (n : Nat) :
    preservingUnaryReadMachine.run (pad + 1)
      (seekBlanksConfig pad (first :: prefTail) b suffix n) =
      seekPrefixHeadConfig prefTail first b suffix pad n := by
  induction pad with
  | zero =>
      simp [seekBlanksConfig, seekPrefixHeadConfig,
        preservingUnaryReadMachine, TM.run, TM.step,
        Tape.write, Tape.move]
  | succ pad ih =>
      rw [show Nat.succ pad + 1 = 1 + (pad + 1) by omega]
      rw [run_add]
      have h1 :
          preservingUnaryReadMachine.run 1
            (seekBlanksConfig (Nat.succ pad) (first :: prefTail) b suffix n) =
          seekBlanksConfig pad (first :: prefTail) b suffix n := by
        rw [TM.run]
        simp [seekBlanksConfig, preservingUnaryReadMachine,
          TM.step, Tape.write, Tape.move,
          List.replicate_succ, List.append_assoc]
      rw [h1]
      simpa using ih

#print axioms MCore.Real.P01PreservingUnarySuccessorCycle.seekBlanks_step
#print axioms MCore.Real.P01PreservingUnarySuccessorCycle.seekBlanks_run

end P01PreservingUnarySuccessorCycle
end Real
end MCore
