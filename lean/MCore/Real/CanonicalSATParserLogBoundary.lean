import MCore.Real.CanonicalSATRecursiveParserMachine
import MCore.Real.CanonicalSATSlotLog

namespace MCore
namespace Real
namespace CanonicalSATParserLogBoundary

open CanonicalFinalProof
open CanonicalSATSlotLog
open CanonicalSATRecursiveParserMachine

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
    Configuration (Fin 25) (Option Bool) :=
  { state := 4
    tape := logBoundaryTape leftBlankCount unread log }

@[simp] theorem logBoundaryConfig_state
    (leftBlankCount : Nat)
    (unread : BitString)
    (log : SlotLog) :
    (logBoundaryConfig leftBlankCount unread log).state = (4 : Fin 25) := rfl

@[simp] theorem logBoundaryTape_initial_empty :
    logBoundaryTape 1 [] [true] =
      { left := [none], head := none, right := [some true] } := by
  rfl

@[simp] theorem logBoundaryTape_initial_cons
    (b : Bool) (bs : BitString) :
    logBoundaryTape 1 (b :: bs) [true] =
      { left := [none]
        head := some b
        right := bs.map some ++ [none, some true] } := by
  simp [logBoundaryTape]

/-- Initialization runtime. -/
def initSteps (n : Nat) : Nat :=
  2 * n + 4

/-- Scanning state 0 over a source suffix. -/
def initScanConfig
    (left : List (Option Bool))
    (bits : BitString) :
    Configuration (Fin 25) (Option Bool) :=
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
    (initScanConfig left bits).state = (0 : Fin 25) := by
  cases bits <;> rfl

@[simp] theorem parser_not_halted_0 :
    parserMachine.halting (0 : Fin 25) = false := by decide
@[simp] theorem parser_not_halted_1 :
    parserMachine.halting (1 : Fin 25) = false := by decide
@[simp] theorem parser_not_halted_2 :
    parserMachine.halting (2 : Fin 25) = false := by decide
@[simp] theorem parser_not_halted_3 :
    parserMachine.halting (3 : Fin 25) = false := by decide

theorem init_step_scan_cons
    (left : List (Option Bool))
    (b : Bool)
    (bs : BitString) :
    parserMachine.step (initScanConfig left (b :: bs)) =
      initScanConfig (some b :: left) bs := by
  cases bs <;>
    simp [parserMachine, initScanConfig, TM.step, Tape.write, Tape.move]

theorem init_step_scan_nil
    (left : List (Option Bool)) :
    parserMachine.step (initScanConfig left []) =
      { state := (1 : Fin 25)
        tape := { left := none :: left, head := none, right := [] } } := by
  simp [parserMachine, initScanConfig, TM.step, Tape.write, Tape.move]

/-- After scanning n source cells, state 0 is on the input-end blank. -/
theorem init_scan_all
    (left : List (Option Bool))
    (bits : BitString) :
    parserMachine.run bits.length (initScanConfig left bits) =
      initScanConfig (bits.reverse.map some ++ left) [] := by
  induction bits generalizing left with
  | nil =>
      rfl
  | cons b bs ih =>
      rw [List.length_cons, TM.run, initScanConfig_state, parser_not_halted_0]
      rw [init_step_scan_cons]
      rw [ih (some b :: left)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- Exact four-step turnaround after reaching the end blank. -/
theorem init_turnaround
    (sourceLeft : List (Option Bool)) :
    parserMachine.run (sourceLeft.length + 4)
      (initScanConfig sourceLeft []) =
    { state := (4 : Fin 25)
      tape :=
        match sourceLeft.reverse with
        | [] =>
            { left := [none], head := none, right := [some true] }
        | x :: xs =>
            { left := [none], head := x,
              right := xs ++ [none, some true] } } := by
  induction sourceLeft with
  | nil =>
      simp [TM.run, initScanConfig, parserMachine, TM.step,
        Tape.write, Tape.move]
  | cons x xs ih =>
      cases x with
      | none =>
          -- Source prefixes generated from canonical input never contain none.
          -- This generic branch is kept total; the exact canonical theorem below
          -- specializes to map some.
          simp [TM.run, initScanConfig, parserMachine, TM.step,
            Tape.write, Tape.move] at *
      | some b =>
          -- Rewinding one source cell adds one state-3 step.
          simp [List.length_cons, initScanConfig, parserMachine, TM.run,
            TM.step, Tape.write, Tape.move, ih, List.reverse_cons,
            List.append_assoc]

/-- Exact canonical initialization theorem used by the parser simulation. -/
theorem parser_initializes_to_log_boundary
    (bits : BitString) :
    parserMachine.run (initSteps bits.length)
      (initialTMConfig parserMachine bits) =
    logBoundaryConfig 1 bits [true] := by
  -- First scan the original input to its implicit right blank.
  have hInitial :
      initialTMConfig parserMachine bits = initScanConfig [] bits := by
    cases bits <;> rfl
  rw [hInitial]
  unfold initSteps
  -- Decompose total runtime into scan + turnaround.
  rw [show 2 * bits.length + 4 = bits.length + (bits.length + 4) by
    omega]
  rw [TM.run_add]
  rw [init_scan_all]
  -- The scanned prefix is reverse(bits.map some).
  have hLeft :
      (bits.reverse.map some).length = bits.length := by simp
  -- Finish by the concrete rewind theorem and normalize the tape shape.
  rw [show bits.length + 4 = (bits.reverse.map some).length + 4 by
    rw [hLeft]]
  rw [init_turnaround]
  cases bits with
  | nil =>
      rfl
  | cons b bs =>
      simp [logBoundaryConfig, logBoundaryTape, List.reverse_cons,
        List.map_append, List.append_assoc]

#print axioms MCore.Real.CanonicalSATParserLogBoundary.init_step_scan_cons
#print axioms MCore.Real.CanonicalSATParserLogBoundary.init_scan_all
#print axioms MCore.Real.CanonicalSATParserLogBoundary.parser_initializes_to_log_boundary

end CanonicalSATParserLogBoundary
end Real
end MCore
