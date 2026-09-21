import MCore.Real.CanonicalSATParserMachine
import MCore.Real.CanonicalSATSlotLog
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace CanonicalSATRecursiveParserInitProof

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATSlotLog

def forwardConfig
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

@[simp] theorem forwardConfig_state
    (left : List (Option Bool))
    (bits : BitString) :
    (forwardConfig left bits).state = (0 : Fin 25) := by
  cases bits <;> rfl

@[simp] theorem parserMachine_not_halted_0 :
    parserMachine.halting (0 : Fin 25) = false := by decide

theorem forward_step_cons
    (left : List (Option Bool))
    (b : Bool)
    (bs : BitString) :
    parserMachine.step (forwardConfig left (b :: bs)) =
      forwardConfig (some b :: left) bs := by
  cases bs <;>
    simp [parserMachine, forwardConfig, TM.step, Tape.write, Tape.move]

theorem forward_scan_run
    (left : List (Option Bool))
    (bits : BitString) :
    parserMachine.run bits.length (forwardConfig left bits) =
      { state := (0 : Fin 25)
        tape :=
          { left := (bits.map some).reverse ++ left
            head := none
            right := [] } } := by
  induction bits generalizing left with
  | nil =>
      rfl
  | cons b bs ih =>
      rw [List.length_cons, TM.run]
      rw [forwardConfig_state, parserMachine_not_halted_0]
      rw [forward_step_cons]
      rw [ih (some b :: left)]
      simp [List.reverse_cons, List.append_assoc]

/-- Configuration used while state 3 rewinds the original input. -/
def rewindConfig
    (remaining : List Bool)
    (right : List (Option Bool)) :
    Configuration (Fin 25) (Option Bool) :=
  match remaining with
  | [] =>
      { state := 3
        tape := { left := [], head := none, right := right } }
  | b :: bs =>
      { state := 3
        tape := { left := bs.map some, head := some b, right := right } }

@[simp] theorem rewindConfig_state
    (remaining : List Bool)
    (right : List (Option Bool)) :
    (rewindConfig remaining right).state = (3 : Fin 25) := by
  cases remaining <;> rfl

@[simp] theorem parserMachine_not_halted_3 :
    parserMachine.halting (3 : Fin 25) = false := by decide

theorem rewind_step_cons
    (b : Bool)
    (bs : List Bool)
    (right : List (Option Bool)) :
    parserMachine.step (rewindConfig (b :: bs) right) =
      rewindConfig bs (some b :: right) := by
  cases bs <;>
    simp [parserMachine, rewindConfig, TM.step, Tape.write, Tape.move]

theorem rewind_run
    (remaining : List Bool)
    (right : List (Option Bool)) :
    parserMachine.run remaining.length (rewindConfig remaining right) =
      rewindConfig [] ((remaining.reverse.map some) ++ right) := by
  induction remaining generalizing right with
  | nil =>
      rfl
  | cons b bs ih =>
      rw [List.length_cons, TM.run]
      rw [rewindConfig_state, parserMachine_not_halted_3]
      rw [rewind_step_cons]
      rw [ih (some b :: right)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- Canonical q4 parser boundary. -/
def boundaryConfig
    (leftBlankCount : Nat)
    (unread : BitString)
    (log : SlotLog) :
    Configuration (Fin 25) (Option Bool) :=
  match unread with
  | [] =>
      { state := 4
        tape :=
          { left := List.replicate leftBlankCount none
            head := none
            right := log.map some } }
  | b :: bs =>
      { state := 4
        tape :=
          { left := List.replicate leftBlankCount none
            head := some b
            right := bs.map some ++ none :: log.map some } }

@[simp] theorem boundaryConfig_state
    (leftBlankCount : Nat)
    (unread : BitString)
    (log : SlotLog) :
    (boundaryConfig leftBlankCount unread log).state = (4 : Fin 25) := by
  cases unread <;> rfl

/-- Exact initial transformation: scan input, create one active slot, rewind. -/
theorem parser_initializes
    (bits : BitString) :
    parserMachine.run (2 * bits.length + 4)
      (initialTMConfig parserMachine bits) =
    boundaryConfig 1 bits initialSlotLog := by
  have hInitial :
      initialTMConfig parserMachine bits = forwardConfig [] bits := by
    cases bits <;> rfl
  rw [hInitial]
  rw [show 2 * bits.length + 4 =
      bits.length + (bits.length + 4) by omega]
  rw [MachineRunLemmas.run_add]
  rw [forward_scan_run]
  -- Three fixed setup transitions: cross end blank, write initial slot,
  -- cross delimiter, then rewind the source.
  cases bits using List.reverseRecOn with
  | nil =>
      simp [parserMachine, TM.run, TM.step, Tape.write, Tape.move,
        rewindConfig, boundaryConfig, initialSlotLog]
  | append_singleton xs b =>
      simp [parserMachine, TM.run, TM.step, Tape.write, Tape.move,
        rewindConfig, boundaryConfig, initialSlotLog, rewind_run,
        List.map_append, List.append_assoc]
      omega

/-- Initialization fits easily inside the global quadratic parser budget. -/
theorem parser_initialization_within_global_bound
    (bits : BitString) :
    2 * bits.length + 4 ≤ parserTimeBound bits.length := by
  unfold parserTimeBound
  omega

#print axioms MCore.Real.CanonicalSATRecursiveParserInitProof.forward_scan_run
#print axioms MCore.Real.CanonicalSATRecursiveParserInitProof.rewind_run
#print axioms MCore.Real.CanonicalSATRecursiveParserInitProof.parser_initializes
#print axioms MCore.Real.CanonicalSATRecursiveParserInitProof.parser_initialization_within_global_bound

end CanonicalSATRecursiveParserInitProof
end Real
end MCore
