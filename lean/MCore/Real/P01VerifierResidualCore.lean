import MCore.Real.P01CanonicalPolynomialClose
import MCore.Real.P01DirectVerifierInhabitant

namespace MCore.Real.P01VerifierResidual

open CanonicalFinalProof CircuitK1 CanonicalCircuitBits CanonicalSATVerifier
open P01CNFMode P01WitnessPreservingPrep
open P01CheckedVerifierCompositeNTM
open P01CanonicalPolynomialClose
open P01DirectVerifierInhabitant
open P01NTMRunLaws

def verifierStart (witness source : BitString) : CheckedVerifierConfig :=
  { state := checkedVerifierMachine.initial,
    tape := preparedTape witness source }

structure PhysicalRejectResidual : Prop where
  invalidCanonical :
    ∀ (witness : BitString) (phi : Circuit),
      varBound phi ≤ witness.length →
      modeCheck .cnf phi = false →
      checkedVerifierMachine.HaltsWithin
        (canonicalVerifierTimeBound (encodeCircuit phi).length)
        (verifierStart witness (encodeCircuit phi)) ∧
      ¬ checkedVerifierMachine.AcceptsWithin
        (canonicalVerifierTimeBound (encodeCircuit phi).length)
        (verifierStart witness (encodeCircuit phi))
  malformedRaw :
    ∀ (witness source : BitString),
      witness.length = source.length →
      decodeCircuit source = none →
      checkedVerifierMachine.HaltsWithin
        (canonicalVerifierTimeBound source.length)
        (verifierStart witness source) ∧
      ¬ checkedVerifierMachine.AcceptsWithin
        (canonicalVerifierTimeBound source.length)
        (verifierStart witness source)

theorem validCanonical_halts_accepts_iff
    (witness : BitString) (phi : Circuit)
    (hlen : varBound phi ≤ witness.length)
    (hmode : modeCheck .cnf phi = true) :
    checkedVerifierMachine.HaltsWithin
        (canonicalVerifierTimeBound (encodeCircuit phi).length)
        (verifierStart witness (encodeCircuit phi)) ∧
      (checkedVerifierMachine.AcceptsWithin
          (canonicalVerifierTimeBound (encodeCircuit phi).length)
          (verifierStart witness (encodeCircuit phi))
        ↔ VerifyBits (encodeCircuit phi) witness) := by
  obtain ⟨terminal, hmem, hhalt, hacc⟩ :=
    valid_cnf_reaches_terminal_within witness phi hmode hlen
  constructor
  · exact haltsWithin_of_reaches_halted
      (canonicalVerifierTimeBound (encodeCircuit phi).length)
      (verifierStart witness (encodeCircuit phi))
      terminal
      (by simpa [verifierStart] using hmem) hhalt
  · rw [acceptsWithin_iff_of_reached_terminal
      (canonicalVerifierTimeBound (encodeCircuit phi).length)
      (verifierStart witness (encodeCircuit phi))
      terminal
      (by simpa [verifierStart] using hmem)]
    exact hacc

end MCore.Real.P01VerifierResidual
