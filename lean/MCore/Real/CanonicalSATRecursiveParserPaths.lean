import MCore.Real.CanonicalSATRecursiveParserMachine
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace CanonicalSATRecursiveParserPaths

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATRecursiveParserMachine

/-- Configuration whose head is the first source bit and whose suffix contains
all non-source work data (delimiter + slot log). -/
def sourceConfig
    (q : Fin 25)
    (left : List (Option Bool))
    (bits : BitString)
    (suffix : List (Option Bool)) :
    Configuration (Fin 25) (Option Bool) :=
  match bits with
  | [] =>
      { state := q
        tape := { left := left, head := none, right := suffix } }
  | b :: bs =>
      { state := q
        tape := { left := left, head := some b,
          right := bs.map some ++ suffix } }

@[simp] theorem sourceConfig_state
    (q : Fin 25)
    (left : List (Option Bool))
    (bits : BitString)
    (suffix : List (Option Bool)) :
    (sourceConfig q left bits suffix).state = q := by
  cases bits <;> rfl

@[simp] theorem parser_not_halted_4 :
    parserMachine.halting (4 : Fin 25) = false := by decide
@[simp] theorem parser_not_halted_5 :
    parserMachine.halting (5 : Fin 25) = false := by decide
@[simp] theorem parser_not_halted_6 :
    parserMachine.halting (6 : Fin 25) = false := by decide
@[simp] theorem parser_not_halted_7 :
    parserMachine.halting (7 : Fin 25) = false := by decide
@[simp] theorem parser_not_halted_8 :
    parserMachine.halting (8 : Fin 25) = false := by decide
@[simp] theorem parser_not_halted_9 :
    parserMachine.halting (9 : Fin 25) = false := by decide
@[simp] theorem parser_not_halted_10 :
    parserMachine.halting (10 : Fin 25) = false := by decide

theorem step_tag_4_false
    (left : List (Option Bool))
    (rest : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.step
      (sourceConfig 4 left (false :: rest) suffix) =
    sourceConfig 5 (none :: left) rest suffix := by
  cases rest <;>
    simp [parserMachine, sourceConfig, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem step_tag_4_true
    (left : List (Option Bool))
    (rest : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.step
      (sourceConfig 4 left (true :: rest) suffix) =
    sourceConfig 6 (none :: left) rest suffix := by
  cases rest <;>
    simp [parserMachine, sourceConfig, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem step_tag_5_false
    (left : List (Option Bool))
    (rest : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.step
      (sourceConfig 5 left (false :: rest) suffix) =
    sourceConfig 7 (none :: left) rest suffix := by
  cases rest <;>
    simp [parserMachine, sourceConfig, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem step_tag_5_true
    (left : List (Option Bool))
    (rest : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.step
      (sourceConfig 5 left (true :: rest) suffix) =
    sourceConfig 8 (none :: left) rest suffix := by
  cases rest <;>
    simp [parserMachine, sourceConfig, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem step_tag_6_false
    (left : List (Option Bool))
    (rest : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.step
      (sourceConfig 6 left (false :: rest) suffix) =
    sourceConfig 9 (none :: left) rest suffix := by
  cases rest <;>
    simp [parserMachine, sourceConfig, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem step_tag_7_false
    (left : List (Option Bool))
    (rest : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.step
      (sourceConfig 7 left (false :: rest) suffix) =
    sourceConfig 10 (none :: left) rest suffix := by
  cases rest <;>
    simp [parserMachine, sourceConfig, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem step_tag_7_true
    (left : List (Option Bool))
    (rest : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.step
      (sourceConfig 7 left (true :: rest) suffix) =
    sourceConfig 11 (none :: left) rest suffix := by
  cases rest <;>
    simp [parserMachine, sourceConfig, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem step_tag_8_false
    (left : List (Option Bool))
    (rest : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.step
      (sourceConfig 8 left (false :: rest) suffix) =
    sourceConfig 11 (none :: left) rest suffix := by
  cases rest <;>
    simp [parserMachine, sourceConfig, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem step_tag_8_true
    (left : List (Option Bool))
    (rest : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.step
      (sourceConfig 8 left (true :: rest) suffix) =
    sourceConfig 4 (none :: left) rest suffix := by
  cases rest <;>
    simp [parserMachine, sourceConfig, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem step_tag_9_bit
    (left : List (Option Bool))
    (third : Bool)
    (rest : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.step
      (sourceConfig 9 left (third :: rest) suffix) =
    sourceConfig 18 (none :: left) rest suffix := by
  cases third <;> cases rest <;>
    simp [parserMachine, sourceConfig, TM.step, Tape.write, Tape.move,
      List.append_assoc]

/-- NOT consumes exactly its three-bit tag and immediately resumes tag parsing
on the child, with no semantic payload in control. -/
theorem run_not_tag
    (left : List (Option Bool))
    (childAndTail : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.run 3
      (sourceConfig 4 left
        (false :: true :: true :: childAndTail) suffix) =
    sourceConfig 4 ([none, none, none] ++ left) childAndTail suffix := by
  rw [TM.run, sourceConfig_state, parser_not_halted_4, step_tag_4_false]
  rw [TM.run, sourceConfig_state, parser_not_halted_5, step_tag_5_true]
  rw [TM.run, sourceConfig_state, parser_not_halted_8, step_tag_8_true]
  rfl

theorem run_const_false_tag
    (left : List (Option Bool))
    (tail : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.run 3
      (sourceConfig 4 left (false :: false :: true :: tail) suffix) =
    sourceConfig 11 ([none, none, none] ++ left) tail suffix := by
  rw [TM.run, sourceConfig_state, parser_not_halted_4, step_tag_4_false]
  rw [TM.run, sourceConfig_state, parser_not_halted_5, step_tag_5_false]
  rw [TM.run, sourceConfig_state, parser_not_halted_7, step_tag_7_true]
  rfl

theorem run_const_true_tag
    (left : List (Option Bool))
    (tail : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.run 3
      (sourceConfig 4 left (false :: true :: false :: tail) suffix) =
    sourceConfig 11 ([none, none, none] ++ left) tail suffix := by
  rw [TM.run, sourceConfig_state, parser_not_halted_4, step_tag_4_false]
  rw [TM.run, sourceConfig_state, parser_not_halted_5, step_tag_5_true]
  rw [TM.run, sourceConfig_state, parser_not_halted_8, step_tag_8_false]
  rfl

theorem run_and_tag
    (left : List (Option Bool))
    (tail : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.run 3
      (sourceConfig 4 left (true :: false :: false :: tail) suffix) =
    sourceConfig 18 ([none, none, none] ++ left) tail suffix := by
  rw [TM.run, sourceConfig_state, parser_not_halted_4, step_tag_4_true]
  rw [TM.run, sourceConfig_state, parser_not_halted_6, step_tag_6_false]
  rw [TM.run, sourceConfig_state, parser_not_halted_9, step_tag_9_bit]
  rfl

theorem run_or_tag
    (left : List (Option Bool))
    (tail : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.run 3
      (sourceConfig 4 left (true :: false :: true :: tail) suffix) =
    sourceConfig 18 ([none, none, none] ++ left) tail suffix := by
  rw [TM.run, sourceConfig_state, parser_not_halted_4, step_tag_4_true]
  rw [TM.run, sourceConfig_state, parser_not_halted_6, step_tag_6_false]
  rw [TM.run, sourceConfig_state, parser_not_halted_9, step_tag_9_bit]
  rfl

theorem step_var_true
    (left : List (Option Bool))
    (rest : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.step
      (sourceConfig 10 left (true :: rest) suffix) =
    sourceConfig 10 (none :: left) rest suffix := by
  cases rest <;>
    simp [parserMachine, sourceConfig, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem step_var_false
    (left : List (Option Bool))
    (rest : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.step
      (sourceConfig 10 left (false :: rest) suffix) =
    sourceConfig 11 (none :: left) rest suffix := by
  cases rest <;>
    simp [parserMachine, sourceConfig, TM.step, Tape.write, Tape.move,
      List.append_assoc]

/-- Unary INPUT payload is consumed without storing its Nat value in state. -/
theorem run_var_payload
    (left : List (Option Bool))
    (n : Nat)
    (tail : BitString)
    (suffix : List (Option Bool)) :
    parserMachine.run (n + 1)
      (sourceConfig 10 left (encodeNat n ++ tail) suffix) =
    sourceConfig 11
      (List.replicate (n + 1) none ++ left) tail suffix := by
  induction n generalizing left with
  | zero =>
      simp only [encodeNat, List.cons_append]
      rw [TM.run, sourceConfig_state, parser_not_halted_10, step_var_false]
      rfl
  | succ n ih =>
      simp only [encodeNat, List.cons_append]
      rw [show Nat.succ n + 1 = (n + 1) + 1 by omega]
      rw [TM.run, sourceConfig_state, parser_not_halted_10, step_var_true]
      rw [ih (none :: left)]
      congr 2
      induction n with
      | zero => rfl
      | succ k hk =>
          simp [List.replicate_succ, hk, List.append_assoc]

#print axioms MCore.Real.CanonicalSATRecursiveParserPaths.run_not_tag
#print axioms MCore.Real.CanonicalSATRecursiveParserPaths.run_const_false_tag
#print axioms MCore.Real.CanonicalSATRecursiveParserPaths.run_const_true_tag
#print axioms MCore.Real.CanonicalSATRecursiveParserPaths.run_and_tag
#print axioms MCore.Real.CanonicalSATRecursiveParserPaths.run_or_tag
#print axioms MCore.Real.CanonicalSATRecursiveParserPaths.run_var_payload

end CanonicalSATRecursiveParserPaths
end Real
end MCore
