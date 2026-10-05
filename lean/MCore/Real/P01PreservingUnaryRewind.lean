import MCore.Real.P01PreservingUnaryFinalRead

namespace MCore
namespace Real
namespace P01PreservingUnaryRewind

open CanonicalFinalProof
open P01PreservingUnaryWitnessMachine
open P01PreservingUnaryFinalRead
open MachineRunLemmas

/-- Canonical rewind state.  The selected bit is stored in control; the
remaining traversed prefix is physically on Tape.right in reverse order. -/
def rewindConfig
    (selected : Bool) (remaining suffix : BitString)
    (blanks : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  match remaining with
  | [] =>
      { state := if selected then .rewindInspectTrue else .rewindInspectFalse
        tape :=
          { left := suffix.map some
            head := none
            right := List.replicate blanks none ++ [some false] } }
  | x :: xs =>
      { state := if selected then .rewindInspectTrue else .rewindInspectFalse
        tape :=
          { left := none :: suffix.map some
            head := some x
            right := xs.map some ++ List.replicate blanks none ++ [some false] } }

@[simp] theorem rewindConfig_state_false
    (remaining suffix : BitString) (blanks : Nat) :
    (rewindConfig false remaining suffix blanks).state = .rewindInspectFalse := by
  cases remaining <;> rfl

@[simp] theorem rewindConfig_state_true
    (remaining suffix : BitString) (blanks : Nat) :
    (rewindConfig true remaining suffix blanks).state = .rewindInspectTrue := by
  cases remaining <;> rfl

/-- Enter the rewind scanner from the selected-bit state. -/
theorem selected_to_rewind
    (pref : BitString) (b : Bool) (suffix : BitString) :
    preservingUnaryReadMachine.run 1 (selectedConfig pref b suffix) =
      rewindConfig b pref.reverse suffix pref.length := by
  cases b <;> cases pref <;>
    simp [selectedConfig, rewindConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move,
      List.replicate_succ, List.append_assoc]

/-- One physical rewind cell restores the bit currently under the head and
moves the marker one cell right. -/
theorem rewind_one_cell
    (selected x : Bool) (xs suffix : BitString) (blanks : Nat) :
    preservingUnaryReadMachine.run 3
      (rewindConfig selected (x :: xs) suffix blanks) =
      rewindConfig selected xs (x :: suffix) blanks := by
  cases selected <;> cases x <;> cases xs <;>
    simp [rewindConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move,
      List.append_assoc]

/-- Rewind every traversed bit. -/
theorem rewind_all
    (selected : Bool) (remaining suffix : BitString) (blanks : Nat) :
    preservingUnaryReadMachine.run (3 * remaining.length)
      (rewindConfig selected remaining suffix blanks) =
      rewindConfig selected [] (remaining.reverse ++ suffix) blanks := by
  induction remaining generalizing suffix with
  | nil => rfl
  | cons x xs ih =>
      rw [List.length_cons]
      rw [show 3 * (xs.length + 1) = 3 + 3 * xs.length by omega]
      rw [run_add]
      rw [rewind_one_cell]
      have h := ih (suffix := x :: suffix)
      simpa [List.reverse_cons, List.append_assoc] using h

def cleanupStartConfig
    (selected : Bool) (witness : BitString) (blanks : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := if selected then .cleanupTrue else .cleanupFalse
    tape :=
      { left := witness.map some
        head := none
        right := List.replicate blanks none ++ [some false] } }

theorem rewind_done_to_cleanup
    (selected : Bool) (witness : BitString) (blanks : Nat) :
    preservingUnaryReadMachine.run 1
      (rewindConfig selected [] witness blanks) =
      cleanupStartConfig selected witness blanks := by
  cases selected <;>
    simp [rewindConfig, cleanupStartConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move]

def haltedConfig
    (selected : Bool) (witness : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  { state := if selected then .haltTrue else .haltFalse
    tape :=
      { left := List.replicate witness.length none ++ witness.map some
        head := none
        right := [] } }

/-- Cleanup crosses all erased unary blanks and consumes the false terminator. -/
theorem cleanup_run
    (selected : Bool) (witness : BitString) (blanks : Nat) :
    preservingUnaryReadMachine.run (blanks + 1)
      (cleanupStartConfig selected witness blanks) =
      haltedConfig selected witness := by
  induction blanks with
  | zero =>
      cases selected <;>
        simp [cleanupStartConfig, haltedConfig, preservingUnaryReadMachine,
          TM.run, TM.step, Tape.write, Tape.move]
  | succ blanks ih =>
      cases selected <;>
        simp [cleanupStartConfig, haltedConfig, preservingUnaryReadMachine,
          TM.run, TM.step, Tape.write, Tape.move,
          List.replicate_succ, List.append_assoc] at ih ⊢

/-- Full physical rewind and cleanup from selectedConfig to a halting state. -/
theorem preservingRead_rewind_cleanup
    (pref : BitString) (b : Bool) (suffix : BitString) :
    preservingUnaryReadMachine.run (1 + 3 * pref.length + 1 + pref.length + 1)
      (selectedConfig pref b suffix) =
      haltedConfig b (pref ++ b :: suffix) := by
  rw [show 1 + 3 * pref.length + 1 + pref.length + 1 =
    1 + (3 * pref.length + (1 + (pref.length + 1))) by omega]
  rw [run_add]
  rw [selected_to_rewind]
  rw [show 3 * pref.length + (1 + (pref.length + 1)) =
    3 * pref.length + (1 + (pref.length + 1)) by rfl]
  rw [run_add]
  rw [rewind_all]
  rw [run_add]
  rw [rewind_done_to_cleanup]
  have hclean :=
    cleanup_run b (pref.reverse.reverse ++ suffix) pref.length
  simpa [List.reverse_reverse, List.append_assoc] using hclean

#print axioms MCore.Real.P01PreservingUnaryRewind.preservingRead_rewind_cleanup

end P01PreservingUnaryRewind
end Real
end MCore
