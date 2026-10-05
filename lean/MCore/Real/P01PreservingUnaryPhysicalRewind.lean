import MCore.Real.P01PreservingUnaryPhysicalFinal
import MCore.Real.MachineRunLemmas

namespace MCore.Real.P01PreservingUnaryPhysicalRewind

open P01PreservingUnaryWitnessMachine
open P01PreservingUnaryPhysicalFinal
open MachineRunLemmas

def rewindConfig
    (remaining restored : BitString)
    (selected : Bool) (tail : BitString)
    (blankPad : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  match remaining with
  | [] =>
      { state := if selected then .rewindInspectTrue else .rewindInspectFalse
        tape :=
          { left := none :: restored.map some ++ some selected :: tail.map some
            head := none
            right := List.replicate blankPad none ++ [some false] } }
  | x :: xs =>
      { state := if selected then .rewindInspectTrue else .rewindInspectFalse
        tape :=
          { left := none :: restored.map some ++ some selected :: tail.map some
            head := some x
            right := xs.map some ++ List.replicate blankPad none ++ [some false] } }

theorem selected_to_rewind
    (selected : Bool) (passedRev : BitString)
    (blankPad : Nat) (tail : BitString) :
    preservingUnaryReadMachine.run 1
      (selectedConfig selected passedRev blankPad tail) =
      rewindConfig passedRev [] selected tail blankPad := by
  cases selected <;> cases passedRev <;>
    simp [selectedConfig, rewindConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move, List.append_assoc]

theorem rewind_step_cons
    (x : Bool) (xs restored : BitString)
    (selected : Bool) (tail : BitString) (blankPad : Nat) :
    preservingUnaryReadMachine.run 3
      (rewindConfig (x :: xs) restored selected tail blankPad) =
      rewindConfig xs (x :: restored) selected tail blankPad := by
  cases selected <;> cases x <;> cases xs <;>
    simp [rewindConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move, List.append_assoc]

theorem rewind_run
    (remaining restored : BitString)
    (selected : Bool) (tail : BitString) (blankPad : Nat) :
    preservingUnaryReadMachine.run (3 * remaining.length)
      (rewindConfig remaining restored selected tail blankPad) =
      rewindConfig [] (remaining.reverse ++ restored) selected tail blankPad := by
  induction remaining generalizing restored with
  | nil => rfl
  | cons x xs ih =>
      rw [show 3 * (x :: xs).length = 3 + 3 * xs.length by simp [Nat.mul_add, Nat.add_assoc]]
      rw [run_add]
      rw [rewind_step_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

def cleanupConfig
    (selected : Bool) (witness : BitString)
    (remaining : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  match remaining with
  | 0 =>
      { state := if selected then .cleanupTrue else .cleanupFalse
        tape :=
          { left := none :: none :: witness.map some
            head := some false
            right := [] } }
  | k + 1 =>
      { state := if selected then .cleanupTrue else .cleanupFalse
        tape :=
          { left := List.replicate (k + 2) none ++ witness.map some
            head := none
            right := List.replicate k none ++ [some false] } }

theorem rewind_done_to_cleanup
    (restored : BitString) (selected : Bool)
    (tail : BitString) (blankPad : Nat) :
    preservingUnaryReadMachine.run 1
      (rewindConfig [] restored selected tail blankPad) =
      cleanupConfig selected (restored.reverse ++ selected :: tail) blankPad := by
  cases selected <;> cases blankPad <;>
    simp [rewindConfig, cleanupConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move,
      List.map_append, List.reverse_reverse, List.replicate_succ,
      List.append_assoc]

theorem cleanup_step_succ
    (selected : Bool) (witness : BitString) (k : Nat) :
    preservingUnaryReadMachine.step
      (cleanupConfig selected witness (k + 1)) =
      cleanupConfig selected witness k := by
  cases selected <;> cases k <;>
    simp [cleanupConfig, preservingUnaryReadMachine,
      TM.step, Tape.write, Tape.move, List.replicate_succ,
      List.append_assoc]

theorem cleanup_run
    (selected : Bool) (witness : BitString) (remaining : Nat) :
    preservingUnaryReadMachine.run remaining
      (cleanupConfig selected witness remaining) =
      cleanupConfig selected witness 0 := by
  induction remaining with
  | zero => rfl
  | succ k ih =>
      calc
        preservingUnaryReadMachine.run (Nat.succ k)
            (cleanupConfig selected witness (Nat.succ k)) =
          preservingUnaryReadMachine.run k
            (preservingUnaryReadMachine.step
              (cleanupConfig selected witness (k + 1))) := by
                cases selected <;> simp [TM.run, cleanupConfig,
                  preservingUnaryReadMachine, Nat.succ_eq_add_one]
        _ = preservingUnaryReadMachine.run k
            (cleanupConfig selected witness k) := by
              rw [cleanup_step_succ]
        _ = cleanupConfig selected witness 0 := ih

def haltConfig (selected : Bool) (witness : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  { state := if selected then .haltTrue else .haltFalse
    tape :=
      { left := none :: none :: witness.map some
        head := none
        right := [] } }

theorem cleanup_to_halt
    (selected : Bool) (witness : BitString) :
    preservingUnaryReadMachine.run 1
      (cleanupConfig selected witness 0) =
      haltConfig selected witness := by
  cases selected <;>
    simp [cleanupConfig, haltConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move]

#print axioms MCore.Real.P01PreservingUnaryPhysicalRewind.selected_to_rewind
#print axioms MCore.Real.P01PreservingUnaryPhysicalRewind.rewind_step_cons
#print axioms MCore.Real.P01PreservingUnaryPhysicalRewind.rewind_run
#print axioms MCore.Real.P01PreservingUnaryPhysicalRewind.rewind_done_to_cleanup
#print axioms MCore.Real.P01PreservingUnaryPhysicalRewind.cleanup_run
#print axioms MCore.Real.P01PreservingUnaryPhysicalRewind.cleanup_to_halt

end MCore.Real.P01PreservingUnaryPhysicalRewind
