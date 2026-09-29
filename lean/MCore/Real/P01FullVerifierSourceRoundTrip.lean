import MCore.Real.P01FullVerifierSourceRewind
import MCore.Real.P01WitnessPreservingPrep
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01FullVerifierSourceRoundTrip

open CanonicalFinalProof
open P01WitnessPreservingPrep
open P01FullVerifierPhysicalShuttles
open P01FullVerifierSourceRewind
open MachineRunLemmas

/-- Exact physical rewind invariant for every nonempty canonical source.
Starting at the source-end blank, the fixed rewind TM restores precisely the
prepared witness/source layout, preserving both bitstrings. -/
theorem sourceRewind_run_to_prepared_nonempty
    (witness : BitString) (b : Bool) (bs : BitString) :
    sourceRewindMachine.run ((b :: bs).length + 2)
      { state := enterSource,
        tape := sourceEndTape witness (b :: bs) } =
      { state := rewindHalt,
        tape := preparedTape witness (b :: bs) } := by
  rw [show (b :: bs).length + 2 =
      1 + ((b :: bs).length + 1) by omega]
  rw [MachineRunLemmas.run_add]
  rw [sourceRewind_run_one_enter]
  rw [show (b :: bs).length + 1 =
      (b :: bs).reverse.length + 1 by simp]
  rw [MachineRunLemmas.run_add]
  rw [rewind_scan_run]
  simp [rewindScanConfig, sourceRewindMachine, enterSource, scanLeft,
    rewindHalt, TM.run, TM.step, Tape.write, Tape.move,
    P01WitnessPreservingPrep.preparedTape]

/-- Together with the already-certified forward scanner, the nonempty source
cursor can shuttle source-start -> source-end -> source-start without changing
the witness/source payload. -/
theorem source_cursor_roundtrip_preserves_prepared
    (witness : BitString) (b : Bool) (bs : BitString) :
    let endConfig :=
      P01FullVerifierTraversal.sourceEndScanner.run
        ((b :: bs).length + 1)
        { state := P01FullVerifierTraversal.sourceEndScanner.initial,
          tape := preparedTape witness (b :: bs) }
    endConfig.tape = sourceEndTape witness (b :: bs) ∧
    sourceRewindMachine.run ((b :: bs).length + 2)
      { state := enterSource, tape := endConfig.tape } =
      { state := rewindHalt,
        tape := preparedTape witness (b :: bs) } := by
  dsimp
  have hscan :=
    P01FullVerifierTraversal.sourceEndScanner_run
      (none :: witness.map some) (b :: bs)
  have hprep :=
    P01FullVerifierTraversal.preparedTape_eq_scanConfig witness b bs
  have hend :
      (P01FullVerifierTraversal.sourceEndScanner.run
        ((b :: bs).length + 1)
        { state := P01FullVerifierTraversal.sourceEndScanner.initial,
          tape := preparedTape witness (b :: bs) }).tape =
        sourceEndTape witness (b :: bs) := by
    rw [hprep]
    rw [P01FullVerifierTraversal.sourceEndScanner_run]
    simp [sourceEndTape, List.append_assoc]
  constructor
  · exact hend
  · rw [hend]
    exact sourceRewind_run_to_prepared_nonempty witness b bs

#print axioms MCore.Real.P01FullVerifierSourceRoundTrip.sourceRewind_run_to_prepared_nonempty
#print axioms MCore.Real.P01FullVerifierSourceRoundTrip.source_cursor_roundtrip_preserves_prepared

end P01FullVerifierSourceRoundTrip
end Real
end MCore
