import MCore.Real.CanonicalSATParserInitProof
import MCore.Real.CanonicalSATSlotParserSpec
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace CanonicalSATParserHeadProof

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATParserMachine
open CanonicalSATParserInitProof
open CanonicalSATSlotParserSpec
open CanonicalSATSlotLog

def phaseConfig
    (q : Fin 31)
    (leftBlankCount : Nat)
    (unread : BitString)
    (log : SlotLog) :
    Configuration (Fin 31) (Option Bool) :=
  match unread with
  | [] =>
      { state := q
        tape :=
          { left := List.replicate leftBlankCount none
            head := none
            right := log.map some } }
  | b :: bs =>
      { state := q
        tape :=
          { left := List.replicate leftBlankCount none
            head := some b
            right := bs.map some ++ none :: log.map some } }

@[simp] theorem phaseConfig_state
    (q : Fin 31)
    (leftBlankCount : Nat)
    (unread : BitString)
    (log : SlotLog) :
    (phaseConfig q leftBlankCount unread log).state = q := by
  cases unread <;> rfl

@[simp] theorem phaseConfig_tag :
    phaseConfig 4 = boundaryConfig := by
  funext pad unread log
  cases unread <;> rfl

theorem step_erase_right
    (q q' : Fin 31)
    (pad : Nat)
    (b : Bool)
    (rest : BitString)
    (log : SlotLog)
    (htrans : parserMachine.transition q (some b) = (q', none, .right)) :
    parserMachine.step (phaseConfig q pad (b :: rest) log) =
      phaseConfig q' (pad + 1) rest log := by
  cases rest <;>
    simp [phaseConfig, parserMachine, TM.step, Tape.write, Tape.move,
      htrans, List.replicate_add]

@[simp] theorem not_halted_4 :
    parserMachine.halting (4 : Fin 31) = false := by decide
@[simp] theorem not_halted_5 :
    parserMachine.halting (5 : Fin 31) = false := by decide
@[simp] theorem not_halted_6 :
    parserMachine.halting (6 : Fin 31) = false := by decide
@[simp] theorem not_halted_7 :
    parserMachine.halting (7 : Fin 31) = false := by decide
@[simp] theorem not_halted_8 :
    parserMachine.halting (8 : Fin 31) = false := by decide
@[simp] theorem not_halted_9 :
    parserMachine.halting (9 : Fin 31) = false := by decide
@[simp] theorem not_halted_10 :
    parserMachine.halting (10 : Fin 31) = false := by decide

theorem tag_input_run
    (pad : Nat) (payload : BitString) (log : SlotLog) :
    parserMachine.run 3
      (phaseConfig 4 pad
        (false :: false :: false :: payload) log) =
      phaseConfig 10 (pad + 3) payload log := by
  simp [TM.run, parserMachine, phaseConfig, TM.step, Tape.write, Tape.move,
    List.replicate_add, Nat.add_assoc]

theorem tag_const_false_run
    (pad : Nat) (tail : BitString) (log : SlotLog) :
    parserMachine.run 3
      (phaseConfig 4 pad
        (false :: false :: true :: tail) log) =
      phaseConfig 11 (pad + 3) tail log := by
  simp [TM.run, parserMachine, phaseConfig, TM.step, Tape.write, Tape.move,
    List.replicate_add, Nat.add_assoc]

theorem tag_const_true_run
    (pad : Nat) (tail : BitString) (log : SlotLog) :
    parserMachine.run 3
      (phaseConfig 4 pad
        (false :: true :: false :: tail) log) =
      phaseConfig 11 (pad + 3) tail log := by
  simp [TM.run, parserMachine, phaseConfig, TM.step, Tape.write, Tape.move,
    List.replicate_add, Nat.add_assoc]

theorem tag_not_run
    (pad : Nat) (tail : BitString) (log : SlotLog) :
    parserMachine.run 3
      (phaseConfig 4 pad
        (false :: true :: true :: tail) log) =
      phaseConfig 12 (pad + 3) tail log := by
  simp [TM.run, parserMachine, phaseConfig, TM.step, Tape.write, Tape.move,
    List.replicate_add, Nat.add_assoc]

theorem tag_and_run
    (pad : Nat) (tail : BitString) (log : SlotLog) :
    parserMachine.run 3
      (phaseConfig 4 pad
        (true :: false :: false :: tail) log) =
      phaseConfig 13 (pad + 3) tail log := by
  simp [TM.run, parserMachine, phaseConfig, TM.step, Tape.write, Tape.move,
    List.replicate_add, Nat.add_assoc]

theorem tag_or_run
    (pad : Nat) (tail : BitString) (log : SlotLog) :
    parserMachine.run 3
      (phaseConfig 4 pad
        (true :: false :: true :: tail) log) =
      phaseConfig 13 (pad + 3) tail log := by
  simp [TM.run, parserMachine, phaseConfig, TM.step, Tape.write, Tape.move,
    List.replicate_add, Nat.add_assoc]

theorem var_payload_run
    (pad i : Nat)
    (tail : BitString)
    (log : SlotLog) :
    parserMachine.run (i + 1)
      (phaseConfig 10 pad (encodeNat i ++ tail) log) =
      phaseConfig 11 (pad + (i + 1)) tail log := by
  induction i generalizing pad with
  | zero =>
      cases tail <;>
        simp [encodeNat, TM.run, parserMachine, phaseConfig, TM.step,
          Tape.write, Tape.move, List.replicate_add, Nat.add_assoc]
  | succ i ih =>
      rw [show Nat.succ i + 1 = (i + 1) + 1 by omega]
      simp only [encodeNat, List.cons_append]
      rw [TM.run]
      rw [phaseConfig_state, not_halted_10]
      have hstep :
          parserMachine.step
            (phaseConfig 10 pad (true :: (encodeNat i ++ tail)) log) =
          phaseConfig 10 (pad + 1) (encodeNat i ++ tail) log := by
        cases (encodeNat i ++ tail) <;>
          simp [parserMachine, phaseConfig, TM.step, Tape.write, Tape.move,
            List.replicate_add, Nat.add_assoc]
      rw [hstep]
      rw [ih (pad + 1)]
      congr 1
      omega

def continuationState : Head → Fin 31
  | .input _ => 11
  | .const _ => 11
  | .not => 12
  | .and => 13
  | .or => 13

/-- Exact operational consumption of one parsed head. -/
theorem consumeHead_run
    (pad : Nat)
    (h : Head)
    (tail : BitString)
    (log : SlotLog) :
    parserMachine.run h.encode.length
      (phaseConfig 4 pad (h.encode ++ tail) log) =
      phaseConfig (continuationState h)
        (pad + h.encode.length) tail log := by
  cases h with
  | input i =>
      rw [show Head.encode (.input i) =
          false :: false :: false :: encodeNat i by rfl]
      rw [show (false :: false :: false :: encodeNat i).length =
          3 + (i + 1) by
            simp [encodeNat_length]]
      rw [MachineRunLemmas.run_add]
      rw [tag_input_run]
      rw [var_payload_run]
      simp [continuationState, Head.encode, encodeNat_length]
      omega
  | const b =>
      cases b <;>
        simp [Head.encode, continuationState, tag_const_false_run,
          tag_const_true_run]
  | not =>
      simp [Head.encode, continuationState, tag_not_run]
  | and =>
      simp [Head.encode, continuationState, tag_and_run]
  | or =>
      simp [Head.encode, continuationState, tag_or_run]

#print axioms MCore.Real.CanonicalSATParserHeadProof.tag_input_run
#print axioms MCore.Real.CanonicalSATParserHeadProof.var_payload_run
#print axioms MCore.Real.CanonicalSATParserHeadProof.consumeHead_run

end CanonicalSATParserHeadProof
end Real
end MCore
