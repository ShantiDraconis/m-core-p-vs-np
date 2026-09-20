import MCore.Real.CanonicalSATNTMAttack

namespace MCore
namespace Real
namespace CanonicalSATParserAttack

open CanonicalFinalProof

/-- Final states for the six constructor tags in CanonicalCircuitBits.encodeCircuit.
    State 12 is the malformed/truncated-tag sink. -/
def tagMachine : TM (Fin 13) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some false => (1, symbol, .right)
        | some true  => (2, symbol, .right)
        | none       => (12, none, .stay)
      else if q = 1 then
        match symbol with
        | some false => (3, symbol, .right)
        | some true  => (4, symbol, .right)
        | none       => (12, none, .stay)
      else if q = 2 then
        match symbol with
        | some false => (5, symbol, .right)
        | _          => (12, symbol, .stay)
      else if q = 3 then
        match symbol with
        | some false => (6, symbol, .right)
        | some true  => (7, symbol, .right)
        | none       => (12, none, .stay)
      else if q = 4 then
        match symbol with
        | some false => (8, symbol, .right)
        | some true  => (9, symbol, .right)
        | none       => (12, none, .stay)
      else if q = 5 then
        match symbol with
        | some false => (10, symbol, .right)
        | some true  => (11, symbol, .right)
        | none       => (12, none, .stay)
      else
        (q, symbol, .stay)
    halting := fun q => decide (6 ≤ q.val) }

@[simp] theorem tagMachine_initial_not_halted :
    tagMachine.halting (0 : Fin 13) = false := by
  decide

def tagInput (prefix : List Bool) (tail : BitString) : BitString :=
  prefix ++ tail

theorem tag_input_state
    (tail : BitString) :
    (tagMachine.run 3
      (initialTMConfig tagMachine
        (tagInput [false, false, false] tail))).state = (6 : Fin 13) := by
  simp [tagInput, tagMachine, initialTMConfig, inputTape,
    TM.run, TM.step, Tape.write, Tape.move]

theorem tag_false_const_state
    (tail : BitString) :
    (tagMachine.run 3
      (initialTMConfig tagMachine
        (tagInput [false, false, true] tail))).state = (7 : Fin 13) := by
  simp [tagInput, tagMachine, initialTMConfig, inputTape,
    TM.run, TM.step, Tape.write, Tape.move]

theorem tag_true_const_state
    (tail : BitString) :
    (tagMachine.run 3
      (initialTMConfig tagMachine
        (tagInput [false, true, false] tail))).state = (8 : Fin 13) := by
  simp [tagInput, tagMachine, initialTMConfig, inputTape,
    TM.run, TM.step, Tape.write, Tape.move]

theorem tag_not_state
    (tail : BitString) :
    (tagMachine.run 3
      (initialTMConfig tagMachine
        (tagInput [false, true, true] tail))).state = (9 : Fin 13) := by
  simp [tagInput, tagMachine, initialTMConfig, inputTape,
    TM.run, TM.step, Tape.write, Tape.move]

theorem tag_and_state
    (tail : BitString) :
    (tagMachine.run 3
      (initialTMConfig tagMachine
        (tagInput [true, false, false] tail))).state = (10 : Fin 13) := by
  simp [tagInput, tagMachine, initialTMConfig, inputTape,
    TM.run, TM.step, Tape.write, Tape.move]

theorem tag_or_state
    (tail : BitString) :
    (tagMachine.run 3
      (initialTMConfig tagMachine
        (tagInput [true, false, true] tail))).state = (11 : Fin 13) := by
  simp [tagInput, tagMachine, initialTMConfig, inputTape,
    TM.run, TM.step, Tape.write, Tape.move]

theorem tag_invalid_11_rejects
    (third : Bool)
    (tail : BitString) :
    (tagMachine.run 2
      (initialTMConfig tagMachine
        (tagInput [true, true, third] tail))).state = (12 : Fin 13) := by
  simp [tagInput, tagMachine, initialTMConfig, inputTape,
    TM.run, TM.step, Tape.write, Tape.move]

/-- The finite tag decoder is now concrete. The remaining parser obligation is
    unbounded recursive syntax bookkeeping on the same single tape. -/
structure RecursiveParserMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

def RecursiveParserOperationalGap : Prop :=
  Nonempty RecursiveParserMachineCertificate

#print axioms MCore.Real.CanonicalSATParserAttack.tag_input_state
#print axioms MCore.Real.CanonicalSATParserAttack.tag_false_const_state
#print axioms MCore.Real.CanonicalSATParserAttack.tag_true_const_state
#print axioms MCore.Real.CanonicalSATParserAttack.tag_not_state
#print axioms MCore.Real.CanonicalSATParserAttack.tag_and_state
#print axioms MCore.Real.CanonicalSATParserAttack.tag_or_state
#print axioms MCore.Real.CanonicalSATParserAttack.tag_invalid_11_rejects

end CanonicalSATParserAttack
end Real
end MCore
