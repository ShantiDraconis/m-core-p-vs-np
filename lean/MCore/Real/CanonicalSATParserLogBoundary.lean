import MCore.Real.CanonicalSATParserMachine
import MCore.Real.CanonicalSATSlotLog

namespace MCore
namespace Real
namespace CanonicalSATParserLogBoundary

open CanonicalFinalProof
open CanonicalSATSlotLog
open CanonicalSATParserMachine

/-- Physical parser boundary with arbitrary tombstone slot log. -/
def logBoundaryTape
    (leftBlankCount : Nat)
    (unread : BitString)
    (log : SlotLog) :
    Tape (Option Bool) :=
  match unread with
  | [] =>
      { left := List.replicate leftBlankCount none
        head := none
        right := log.map some }
  | b :: bs =>
      { left := List.replicate leftBlankCount none
        head := some b
        right := bs.map some ++ none :: log.map some }

/-- Boundary configuration at READ_TAG_0. -/
def logBoundaryConfig
    (leftBlankCount : Nat)
    (unread : BitString)
    (log : SlotLog) :
    Configuration (Fin 31) (Option Bool) :=
  { state := 4
    tape := logBoundaryTape leftBlankCount unread log }

@[simp] theorem logBoundaryConfig_state
    (leftBlankCount : Nat)
    (unread : BitString)
    (log : SlotLog) :
    (logBoundaryConfig leftBlankCount unread log).state = (4 : Fin 31) := rfl

/-- Total initialization budget: one scan right, constant setup, one rewind. -/
def initSteps (n : Nat) : Nat :=
  n + (n + 4)

/-- State-0 scan configuration. -/
def initScanConfig
    (left : List (Option Bool))
    (bits : BitString) :
    Configuration (Fin 31) (Option Bool) :=
  match bits with
  | [] =>
      { state := 0
        tape := { left := left, head := none, right := [] } }
  | b :: bs =>
      { state := 0
        tape := { left := left, head := some b, right := bs.map some } }

@[simp] theorem initScanConfig_state
    (left : List (Option Bool))
    (bits : BitString) :
    (initScanConfig left bits).state = (0 : Fin 31) := by
  cases bits <;> rfl

@[simp] theorem parser_not_halted_0 :
    parserMachine.halting (0 : Fin 31) = false := by decide
@[simp] theorem parser_not_halted_3 :
    parserMachine.halting (3 : Fin 31) = false := by decide

theorem init_step_scan_cons
    (left : List (Option Bool))
    (b : Bool)
    (bs : BitString) :
    parserMachine.step (initScanConfig left (b :: bs)) =
      initScanConfig (some b :: left) bs := by
  cases bs <;>
    simp [parserMachine, initScanConfig, TM.step, Tape.write, Tape.move]

/-- Scanning a source prefix can be followed by arbitrary extra fuel. -/
theorem init_scan_all_extra
    (left : List (Option Bool))
    (bits : BitString)
    (extra : Nat) :
    parserMachine.run (bits.length + extra) (initScanConfig left bits) =
      parserMachine.run extra
        (initScanConfig (bits.reverse.map some ++ left) []) := by
  induction bits generalizing left with
  | nil =>
      rfl
  | cons b bs ih =>
      rw [List.length_cons]
      rw [show (bs.length + 1) + extra =
          (bs.length + extra) + 1 by
            exact Nat.add_right_comm bs.length 1 extra]
      rw [TM.run, initScanConfig_state, parser_not_halted_0]
      rw [init_step_scan_cons]
      rw [ih (some b :: left)]
      congr 2
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- State-3 rewind configuration. -/
def rewindConfig
    (remaining processed : BitString) :
    Configuration (Fin 31) (Option Bool) :=
  match remaining with
  | [] =>
      { state := 3
        tape :=
          { left := []
            head := none
            right := processed.map some ++ [none, some true] } }
  | b :: bs =>
      { state := 3
        tape :=
          { left := bs.map some
            head := some b
            right := processed.map some ++ [none, some true] } }

@[simp] theorem rewindConfig_state
    (remaining processed : BitString) :
    (rewindConfig remaining processed).state = (3 : Fin 31) := by
  cases remaining <;> rfl

theorem rewind_step_cons
    (b : Bool)
    (bs processed : BitString) :
    parserMachine.step (rewindConfig (b :: bs) processed) =
      rewindConfig bs (b :: processed) := by
  cases bs <;>
    simp [parserMachine, rewindConfig, TM.step, Tape.write, Tape.move,
      List.append_assoc]

/-- Rewind all source cells, then cross the left blank into READ_TAG_0. -/
theorem rewind_all
    (remaining processed : BitString) :
    parserMachine.run (remaining.length + 1)
      (rewindConfig remaining processed) =
    logBoundaryConfig 1 (remaining.reverse ++ processed) [true] := by
  induction remaining generalizing processed with
  | nil =>
      simp [rewindConfig, logBoundaryConfig, logBoundaryTape,
        parserMachine, TM.run, TM.step, Tape.write, Tape.move]
  | cons b bs ih =>
      rw [List.length_cons]
      rw [show bs.length + 1 + 1 = (bs.length + 1) + 1 by rfl]
      rw [TM.run, rewindConfig_state, parser_not_halted_3]
      rw [rewind_step_cons]
      rw [ih (b :: processed)]
      simp [List.reverse_cons, List.append_assoc]

/-- Three setup transitions from the input-end blank to state 3. -/
theorem setup_to_rewind
    (revBits : BitString) :
    parserMachine.run 3
      (initScanConfig (revBits.map some) []) =
    rewindConfig revBits [] := by
  cases revBits with
  | nil =>
      simp [initScanConfig, rewindConfig, parserMachine, TM.run,
        TM.step, Tape.write, Tape.move]
  | cons b bs =>
      simp [initScanConfig, rewindConfig, parserMachine, TM.run,
        TM.step, Tape.write, Tape.move]

/-- End-blank setup plus rewind. -/
theorem turnaround_from_reversed_source
    (revBits : BitString) :
    parserMachine.run (revBits.length + 4)
      (initScanConfig (revBits.map some) []) =
    logBoundaryConfig 1 revBits.reverse [true] := by
  cases revBits with
  | nil =>
      simp [initScanConfig, rewindConfig, logBoundaryConfig, logBoundaryTape,
        parserMachine, TM.run, TM.step, Tape.write, Tape.move]
  | cons b bs =>
      -- Unroll the three fixed setup transitions, then use rewind_all.
      rw [List.length_cons]
      simp [initScanConfig, parserMachine, TM.run, TM.step, Tape.write, Tape.move]
      simpa [rewindConfig, logBoundaryConfig, logBoundaryTape,
        List.reverse_cons, List.append_assoc] using
        (rewind_all (b :: bs) [])

/-- Exact canonical initialization theorem used by the parser simulation. -/
theorem parser_initializes_to_log_boundary
    (bits : BitString) :
    parserMachine.run (initSteps bits.length)
      (initialTMConfig parserMachine bits) =
    logBoundaryConfig 1 bits [true] := by
  have hInitial :
      initialTMConfig parserMachine bits = initScanConfig [] bits := by
    cases bits <;> rfl
  rw [hInitial]
  unfold initSteps
  rw [init_scan_all_extra [] bits (bits.length + 4)]
  have hLen : (bits.reverse).length = bits.length := by simp
  rw [← hLen]
  rw [turnaround_from_reversed_source]
  simp

#print axioms MCore.Real.CanonicalSATParserLogBoundary.init_step_scan_cons
#print axioms MCore.Real.CanonicalSATParserLogBoundary.init_scan_all_extra
#print axioms MCore.Real.CanonicalSATParserLogBoundary.rewind_all
#print axioms MCore.Real.CanonicalSATParserLogBoundary.parser_initializes_to_log_boundary

end CanonicalSATParserLogBoundary
end Real
end MCore
