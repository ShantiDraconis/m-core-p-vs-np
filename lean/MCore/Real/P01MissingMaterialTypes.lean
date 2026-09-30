import MCore.Real.P01FinalCertificate
import MCore.Real.P01EvalCursorMachine
import MCore.Real.P01EncodedStackEvaluator
import MCore.Real.P01EncodedFrameTape
import MCore.Real.CanonicalSATWitness

namespace MCore
namespace Real
namespace P01MissingMaterialTypes

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open P01FinalCertificate
open P01EvalCursorMachine
open P01EncodedStackEvaluator
open P01EncodedFrameTape

/-- Concrete witness assignment induced by the physical witness bitstring. -/
def witnessAssignment (witness : BitString) : Assignment :=
  fun i => witness.getD i false

/-- Exact remaining local P01 input-node producer.
A valid inhabitant must read 000 ++ encodeNat(i), return witness[i],
restore the witness exactly, preserve the frame stack, preserve the unread tail,
and advance only the source cursor. -/
structure PreservingUnaryWitnessReadCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none

  result : Fin (stateCount + 1) → Option Bool

  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

  halts :
    ∀ (witness : BitString)
      (consumed : Nat)
      (rest : BitString)
      (frames : List EvalFrame)
      (padding i : Nat),
      i < witness.length →
      let source := [false, false, false] ++ encodeNat i ++ rest
      let frameBits := encodeEvalFrames frames
      let inputSize :=
        witness.length + source.length + frameBits.length + padding
      machine.HaltsWithin (timeBound inputSize)
        { state := machine.initial,
          tape :=
            evalCursorStackEndTape
              witness consumed source frameBits padding }

  correct :
    ∀ (witness : BitString)
      (consumed : Nat)
      (rest : BitString)
      (frames : List EvalFrame)
      (padding i : Nat),
      i < witness.length →
      let source := [false, false, false] ++ encodeNat i ++ rest
      let frameBits := encodeEvalFrames frames
      let inputSize :=
        witness.length + source.length + frameBits.length + padding
      let final :=
        machine.run (timeBound inputSize)
          { state := machine.initial,
            tape :=
              evalCursorStackEndTape
                witness consumed source frameBits padding }
      result final.state = some (witness.getD i false) ∧
        final.tape =
          evalCursorStackEndTape
            witness
            (consumed + 3 + (encodeNat i).length)
            rest
            frameBits
            padding

/-- OPEN implementation target for the single remaining local evalStep case. -/
def PreservingUnaryWitnessReadGap : Prop :=
  Nonempty PreservingUnaryWitnessReadCertificate

/-- Exact global physical-verifier producer after all local evalStep cases are
refined.  A valid inhabitant must execute the frozen evaluator semantics with
one fixed TM, preserve the witness, consume exactly the encoded circuit, empty
the continuation stack, and return the exact Boolean circuit value. -/
structure PhysicalEvalRunCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none

  result : Fin (stateCount + 1) → Option Bool

  padding : BitString → CircuitK1.Circuit → Nat

  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

  halts :
    ∀ (witness : BitString) (c : CircuitK1.Circuit),
      let source := encodeCircuit c
      let pad := padding witness c
      let inputSize := witness.length + source.length + pad
      machine.HaltsWithin (timeBound inputSize)
        { state := machine.initial,
          tape :=
            evalCursorStackEndTape witness 0 source [] pad }

  refines_evalRun :
    ∀ (witness : BitString) (c : CircuitK1.Circuit),
      let source := encodeCircuit c
      let pad := padding witness c
      let inputSize := witness.length + source.length + pad
      let final :=
        machine.run (timeBound inputSize)
          { state := machine.initial,
            tape :=
              evalCursorStackEndTape witness 0 source [] pad }
      result final.state =
          some (CircuitK1.evalCircuit (witnessAssignment witness) c) ∧
        final.tape =
          evalCursorStackEndTape
            witness source.length [] [] pad

/-- OPEN implementation target for the one-machine global verifier simulation. -/
def PhysicalEvalRunGap : Prop :=
  Nonempty PhysicalEvalRunCertificate

end P01MissingMaterialTypes
end Real
end MCore
