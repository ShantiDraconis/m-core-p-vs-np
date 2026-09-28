import MCore.Real.P01FullVerifierSourceRewind

namespace MCore
namespace Real
namespace P01SourceRewindGlobal

open CanonicalFinalProof
open P01WitnessPreservingPrep
open P01FullVerifierPhysicalShuttles
open P01FullVerifierSourceRewind

/-- Exact intermediate configuration while the rewind machine scans the
source from right to left.  `rev` contains the unread source symbols in
right-to-left order; `right` contains the already crossed cells. -/
def rewindScanConfig
    (witness : BitString)
    (rev : List Bool)
    (right : List (Option Bool)) :
    Configuration RewindState (Option Bool) :=
  match rev with
  | [] =>
      { state := scanLeft
        tape :=
          { left := witness.map some
            head := none
            right := right } }
  | b :: bs =>
      { state := scanLeft
        tape :=
          { left := bs.map some ++ none :: witness.map some
            head := some b
            right := right } }

/-- Scanning a finite reversed source reaches the witness/source separator and
then performs the certified one-cell right step.  This is a genuine global
execution theorem for the concrete three-state rewind TM. -/
theorem rewindScanConfig_run
    (witness rev : BitString)
    (right : List (Option Bool)) :
    sourceRewindMachine.run (rev.length + 1)
      (rewindScanConfig witness rev right) =
      { state := rewindHalt
        tape := Tape.move none .right
          { left := witness.map some
            head := none
            right := rev.reverse.map some ++ right } } := by
  induction rev generalizing right with
  | nil =>
      simp [rewindScanConfig, TM.run, sourceRewindMachine,
        scanLeft, rewindHalt, enterSource, Tape.write, Tape.move]
  | cons b bs ih =>
      rw [List.length_cons]
      rw [show bs.length + 1 + 1 = (bs.length + 1) + 1 by rfl]
      rw [TM.run, scanLeft_not_halted]
      change sourceRewindMachine.run (bs.length + 1)
        (rewindScanConfig witness bs (some b :: right)) = _
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- For every nonempty canonical source, the concrete rewind TM returns from
the source-end blank to exactly the witness-preserving prepared-tape layout.
The bound is source.length + 2 primitive TM steps. -/
theorem sourceRewind_run_prepared
    (witness : BitString)
    (b : Bool)
    (bs : BitString) :
    sourceRewindMachine.run ((b :: bs).length + 2)
      { state := enterSource
        tape := sourceEndTape witness (b :: bs) } =
      { state := rewindHalt
        tape := preparedTape witness (b :: bs) } := by
  rw [show (b :: bs).length + 2 =
      ((b :: bs).reverse.length + 1) + 1 by simp]
  rw [TM.run, enterSource_not_halted]
  rw [sourceRewind_enter_step]
  change sourceRewindMachine.run ((b :: bs).reverse.length + 1)
    (rewindScanConfig witness (b :: bs).reverse [none]) = _
  rw [rewindScanConfig_run]
  simp [preparedTape, List.map_append, List.append_assoc, Tape.move]

/-- The advertised linear rewind time bound dominates the exact run above. -/
theorem sourceRewind_nonempty_halts
    (witness : BitString)
    (b : Bool)
    (bs : BitString) :
    sourceRewindMachine.HaltsWithin
      (sourceRewindTimeBound (b :: bs).length)
      { state := enterSource
        tape := sourceEndTape witness (b :: bs) } := by
  unfold sourceRewindTimeBound TM.HaltsWithin
  rw [sourceRewind_run_prepared]
  exact rewindHalt_halted

#print axioms MCore.Real.P01SourceRewindGlobal.rewindScanConfig_run
#print axioms MCore.Real.P01SourceRewindGlobal.sourceRewind_run_prepared
#print axioms MCore.Real.P01SourceRewindGlobal.sourceRewind_nonempty_halts

end P01SourceRewindGlobal
end Real
end MCore
