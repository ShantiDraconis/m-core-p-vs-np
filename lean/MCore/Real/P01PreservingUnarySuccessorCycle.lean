import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01PreservingUnarySuccessorCycle

open CanonicalFinalProof
open CanonicalCircuitBits
open MachineRunLemmas
open P01PreservingUnaryWitnessMachine

@[simp] theorem preserving_not_halt_seekBlanks :
    preservingUnaryReadMachine.halting .seekBlanks = false := rfl

@[simp] theorem preserving_not_halt_seekBits :
    preservingUnaryReadMachine.halting .seekBits = false := rfl

/-- Configuration while crossing erased unary blanks.
`pad` counts blanks still to the left of the blank currently under the head.
The right side is explicit because every left move pushes one blank onto it. -/
def seekBlanksConfig
    (pad : Nat) (pref suffix : BitString)
    (right : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .seekBlanks
    tape :=
      { left := List.replicate pad none ++ pref.map some ++ none :: suffix.map some
        head := none
        right := right } }

@[simp] theorem seekBlanksConfig_state
    (pad : Nat) (pref suffix : BitString)
    (right : List (Option Bool)) :
    (seekBlanksConfig pad pref suffix right).state = .seekBlanks := rfl

theorem replicate_none_push
    (pad : Nat) (right : List (Option Bool)) :
    List.replicate pad none ++ none :: right =
      none :: List.replicate pad none ++ right := by
  induction pad with
  | zero => rfl
  | succ pad ih =>
      simp [List.replicate_succ, ih, List.append_assoc]

theorem seekBlanks_step_succ
    (pad : Nat) (pref suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.step
      (seekBlanksConfig (pad + 1) pref suffix right) =
    seekBlanksConfig pad pref suffix (none :: right) := by
  simp [seekBlanksConfig, preservingUnaryReadMachine, TM.step,
    Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

/-- Crossing the current blank plus all `pad` blanks to its left reaches the
first traversed witness bit. -/
theorem seekBlanks_run_to_first_bit
    (pad : Nat) (c : Bool) (cs suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.run (pad + 1)
      (seekBlanksConfig pad (c :: cs) suffix right) =
    { state := .seekBlanks
      tape :=
        { left := cs.map some ++ none :: suffix.map some
          head := some c
          right := List.replicate (pad + 1) none ++ right } } := by
  induction pad generalizing right with
  | zero =>
      simp [seekBlanksConfig, preservingUnaryReadMachine, TM.run, TM.step,
        Tape.write, Tape.move]
  | succ pad ih =>
      rw [show Nat.succ pad + 1 = 1 + (pad + 1) by omega]
      rw [run_add]
      have h1 :
          preservingUnaryReadMachine.run 1
            (seekBlanksConfig (Nat.succ pad) (c :: cs) suffix right) =
          seekBlanksConfig pad (c :: cs) suffix (none :: right) := by
        rw [TM.run]
        simp only [seekBlanksConfig_state, preserving_not_halt_seekBlanks,
          Bool.false_eq_true, if_false]
        simpa [Nat.succ_eq_add_one] using
          seekBlanks_step_succ pad (c :: cs) suffix right
      rw [h1]
      have hih := ih (right := none :: right)
      rw [replicate_none_push (pad + 1) right] at hih
      simpa [List.replicate_succ, List.append_assoc, Nat.succ_eq_add_one] using hih

/-- Configuration while seekBits crosses the Boolean prefix toward the unique
witness marker. -/
def seekBitsConfig
    (remaining suffix : BitString)
    (right : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  match remaining with
  | [] =>
      { state := .seekBits
        tape := { left := suffix.map some, head := none, right := right } }
  | c :: cs =>
      { state := .seekBits
        tape :=
          { left := cs.map some ++ none :: suffix.map some
            head := some c
            right := right } }

@[simp] theorem seekBitsConfig_state
    (remaining suffix : BitString)
    (right : List (Option Bool)) :
    (seekBitsConfig remaining suffix right).state = .seekBits := by
  cases remaining <;> rfl

theorem seekBits_step_cons
    (c : Bool) (cs suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.step
      (seekBitsConfig (c :: cs) suffix right) =
    seekBitsConfig cs suffix (some c :: right) := by
  cases cs <;>
    simp [seekBitsConfig, preservingUnaryReadMachine, TM.step,
      Tape.write, Tape.move, List.append_assoc]

/-- Configuration with the selected next witness bit under shiftRead. -/
def shiftReadConfig
    (b : Bool) (suffix : BitString)
    (right : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .shiftRead
    tape := { left := suffix.map some, head := some b, right := none :: right } }

/-- Configuration after the marker has moved across b and the machine has
returned onto b, ready to scan right across the traversed bits. -/
def returnBitsConfig
    (b : Bool) (suffix : BitString)
    (right : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .returnBits
    tape := { left := none :: suffix.map some, head := some b, right := right } }

theorem seekBits_marker_step
    (b : Bool) (suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.step
      (seekBitsConfig [] (b :: suffix) right) =
    shiftReadConfig b suffix right := by
  simp [seekBitsConfig, shiftReadConfig, preservingUnaryReadMachine,
    TM.step, Tape.write, Tape.move]

theorem shift_carry_return_run_three
    (b : Bool) (suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.run 3
      (shiftReadConfig b suffix right) =
    returnBitsConfig b suffix right := by
  cases b <;>
    simp [shiftReadConfig, returnBitsConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move]

/-- Rightward scan configuration after the marker shift.  The list `bits`
is exactly the remaining Boolean segment to cross before the erased unary
blank region. -/
def returnBitsScanConfig
    (bits : BitString) (suffix : BitString)
    (rightTail : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  match bits with
  | [] =>
      { state := .returnBits
        tape := { left := none :: suffix.map some, head := none, right := rightTail } }
  | x :: xs =>
      { state := .returnBits
        tape :=
          { left := none :: suffix.map some
            head := some x
            right := xs.map some ++ rightTail } }

@[simp] theorem returnBitsScanConfig_state
    (bits suffix : BitString) (rightTail : List (Option Bool)) :
    (returnBitsScanConfig bits suffix rightTail).state = .returnBits := by
  cases bits <;> rfl

theorem returnBits_step_cons
    (x : Bool) (xs suffix : BitString)
    (rightTail : List (Option Bool)) :
    preservingUnaryReadMachine.step
      (returnBitsScanConfig (x :: xs) suffix rightTail) =
    returnBitsScanConfig xs suffix rightTail := by
  cases xs <;>
    simp [returnBitsScanConfig, preservingUnaryReadMachine, TM.step,
      Tape.write, Tape.move, List.append_assoc]

/-- Exact finite scan across all restored Boolean cells. -/
theorem returnBits_run
    (bits suffix : BitString)
    (rightTail : List (Option Bool)) :
    preservingUnaryReadMachine.run bits.length
      (returnBitsScanConfig bits suffix rightTail) =
    returnBitsScanConfig [] suffix rightTail := by
  induction bits with
  | nil => rfl
  | cons x xs ih =>
      rw [List.length_cons]
      simp only [TM.run, returnBitsScanConfig_state]
      simp [preservingUnaryReadMachine]
      rw [returnBits_step_cons]
      exact ih

/-- Exact finite scan of the traversed witness-prefix tail. -/
theorem seekBits_run
    (remaining suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.run remaining.length
      (seekBitsConfig remaining suffix right) =
    seekBitsConfig [] suffix (remaining.reverse.map some ++ right) := by
  induction remaining generalizing right with
  | nil =>
      rfl
  | cons c cs ih =>
      rw [List.length_cons]
      simp only [TM.run, seekBitsConfig_state, preserving_not_halt_seekBits,
        Bool.false_eq_true, if_false]
      rw [seekBits_step_cons]
      have hih := ih (right := some c :: right)
      rw [hih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

#print axioms MCore.Real.P01PreservingUnarySuccessorCycle.seekBlanks_run_to_first_bit
#print axioms MCore.Real.P01PreservingUnarySuccessorCycle.seekBits_marker_step
#print axioms MCore.Real.P01PreservingUnarySuccessorCycle.shift_carry_return_run_three
#print axioms MCore.Real.P01PreservingUnarySuccessorCycle.seekBits_run

end P01PreservingUnarySuccessorCycle
end Real
end MCore
