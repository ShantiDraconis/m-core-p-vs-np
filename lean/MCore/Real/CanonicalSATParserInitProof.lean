import MCore.Real.CanonicalSATParserMachine
import MCore.Real.CanonicalSATSlotLog

namespace MCore
namespace Real
namespace CanonicalSATParserInitProof

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATSlotLog

theorem run_add_local
    {State Symbol : Type}
    (machine : TM State Symbol)
    (m n : Nat)
    (config : Configuration State Symbol) :
    machine.run (m + n) config =
      machine.run n (machine.run m config) := by
  induction m generalizing config with
  | zero =>
      rfl
  | succ m ih =>
      rw [Nat.succ_add]
      rw [TM.run]
      by_cases h : machine.halting config.state
      · simp [h, TM.run]
      · simp [h, ih]

def forwardConfig
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

@[simp] theorem forwardConfig_state
    (left : List (Option Bool))
    (bits : BitString) :
    (forwardConfig left bits).state = (0 : Fin 31) := by
  cases bits <;> rfl

@[simp] theorem parserMachine_not_halted_0 :
    parserMachine.halting (0 : Fin 31) = false := by decide

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
      { state := (0 : Fin 31)
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

/-- State-3 rewind configuration. remaining is ordered from the current head
toward the left boundary: head first, then successive cells to the left. -/
def rewindConfig
    (remaining : List Bool)
    (right : List (Option Bool)) :
    Configuration (Fin 31) (Option Bool) :=
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
    (rewindConfig remaining right).state = (3 : Fin 31) := by
  cases remaining <;> rfl

@[simp] theorem parserMachine_not_halted_3 :
    parserMachine.halting (3 : Fin 31) = false := by decide

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
      rewindConfig []
        ((remaining.reverse.map some) ++ right) := by
  induction remaining generalizing right with
  | nil =>
      rfl
  | cons b bs ih =>
      rw [List.length_cons, TM.run]
      rw [rewindConfig_state, parserMachine_not_halted_3]
      rw [rewind_step_cons]
      rw [ih (some b :: right)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

def boundaryConfig
    (leftBlankCount : Nat)
    (unread : BitString)
    (log : SlotLog) :
    Configuration (Fin 31) (Option Bool) :=
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
    (boundaryConfig leftBlankCount unread log).state = (4 : Fin 31) := by
  cases unread <;> rfl

/-- The first 2*|bits|+4 steps deterministically create exactly one active
slot, rewind to the beginning, and enter TAG_0. -/
theorem parser_initializes
    (bits : BitString) :
    parserMachine.run (2 * bits.length + 4)
      (initialTMConfig parserMachine bits) =
    boundaryConfig 1 bits initialSlotLog := by
  have hInitial :
      initialTMConfig parserMachine bits = forwardConfig [] bits := by
    cases bits <;> rfl
  rw [hInitial]
  cases bits using List.reverseRecOn with
  | nil =>
      simp [TM.run, parserMachine, forwardConfig, rewindConfig,
        boundaryConfig, initialSlotLog, TM.step, Tape.write, Tape.move]
  | append_singleton xs b =>
      rw [show 2 * (xs ++ [b]).length + 4 =
          (xs ++ [b]).length + (3 + ((xs ++ [b]).reverse.length + 1)) by
            simp
            omega]
      rw [run_add_local]
      rw [forward_scan_run]
      simp [TM.run, parserMachine, TM.step, Tape.write, Tape.move,
        rewindConfig, boundaryConfig, initialSlotLog, rewind_run,
        List.map_append, List.append_assoc]

#print axioms MCore.Real.CanonicalSATParserInitProof.forward_scan_run
#print axioms MCore.Real.CanonicalSATParserInitProof.rewind_run
#print axioms MCore.Real.CanonicalSATParserInitProof.parser_initializes

end CanonicalSATParserInitProof
end Real
end MCore
