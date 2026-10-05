import MCore.Real.P01FullVerifierPhysical
import MCore.Real.P01FullVerifierPhysicalControl
import MCore.Real.P01PhysicalVerifierBudget

namespace MCore.Real.P01FullVerifierPhysical

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open CanonicalSATVerifier
open P01FullVerifierMachine
open P01FullVerifierPhysicalControl
open P01PhysicalVerifierBudget

abbrev FixedVerifierState := P01FullVerifierPhysicalControl.VerifierState

def fixedVerifierAccepting : FixedVerifierState → Bool :=
  fun q => q == P01FullVerifierPhysicalControl.halt

def FixedVerifierHalts : Prop :=
  ∀ (phi : CircuitK1.Circuit) (w : SATWitness phi),
    P01FullVerifierPhysicalControl.decoderEvaluatorMachine.HaltsWithin
      (physicalVerifierTimeBound (encodeCircuit phi).length)
      { state := P01FullVerifierPhysicalControl.decoderEvaluatorMachine.initial,
        tape := verifierInputTape (witnessBits w) (encodeCircuit phi) }

def FixedVerifierCorrect : Prop :=
  ∀ (phi : CircuitK1.Circuit) (w : SATWitness phi),
    fixedVerifierAccepting
      (P01FullVerifierPhysicalControl.decoderEvaluatorMachine.run
        (physicalVerifierTimeBound (encodeCircuit phi).length)
        { state := P01FullVerifierPhysicalControl.decoderEvaluatorMachine.initial,
          tape := verifierInputTape (witnessBits w) (encodeCircuit phi) }).state = true ↔
      verifyWitness phi w = true

def fixedVerifierResiduals_close
    (hhalts : FixedVerifierHalts)
    (hcorrect : FixedVerifierCorrect) :
    PhysicalVerifierRealization := by
  refine {
    stateCount := 7
    machine := P01FullVerifierPhysicalControl.decoderEvaluatorMachine
    blank_none := P01FullVerifierPhysicalControl.decoderEvaluatorMachine_blank
    accepting := fixedVerifierAccepting
    timeBound := physicalVerifierTimeBound
    time_poly := physicalVerifierTimeBound_poly
    halts := ?_
    physical_eq_logical := ?_
  }
  · exact hhalts
  · exact hcorrect

#print axioms MCore.Real.P01FullVerifierPhysical.fixedVerifierResiduals_close

end MCore.Real.P01FullVerifierPhysical
