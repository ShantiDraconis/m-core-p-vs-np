import MCore.Real.P01VerifierResidualCore
import MCore.Real.P01WitnessPrepGlobal
import MCore.Real.P01IntegratedAssembly
import MCore.Real.P01CheckedVerifierFiniteState

namespace MCore.Real.P01VerifierResidual

open CanonicalFinalProof CircuitK1 CanonicalCircuitBits CanonicalSATVerifier
open P01CNFMode P01WitnessPreservingPrep
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierFiniteState
open P01CanonicalPolynomialClose
open P01IntegratedAssembly
open P01WitnessPrepGlobal
open P01NTMRunLaws

theorem rawVerifier_halts_accepts_iff
    (R : PhysicalRejectResidual)
    (witness source : BitString)
    (hw : witness.length = source.length) :
    checkedVerifierMachine.HaltsWithin
        (canonicalVerifierTimeBound source.length)
        (verifierStart witness source) ∧
      (checkedVerifierMachine.AcceptsWithin
          (canonicalVerifierTimeBound source.length)
          (verifierStart witness source)
        ↔ VerifyBits source witness) := by
  cases hdec : decodeCircuit source with
  | none =>
      rcases R.malformedRaw witness source hw hdec with ⟨hh, hna⟩
      refine ⟨hh, ?_⟩
      constructor
      · exact fun ha => False.elim (hna ha)
      · intro hv
        rcases hv with ⟨phi, hphi, _, _⟩
        rw [hdec] at hphi
        contradiction
  | some phi =>
      have hsrc : source = encodeCircuit phi :=
        decodeCircuit_sound source phi hdec
      have hlen : varBound phi ≤ witness.length := by
        have hv := varBound_le_of_decode source phi hdec
        rw [← hw]
        exact hv
      cases hmode : modeCheck .cnf phi with
      | true =>
          simpa [hsrc, verifierStart] using
            validCanonical_halts_accepts_iff witness phi hlen hmode
      | false =>
          rcases R.invalidCanonical witness phi hlen hmode with ⟨hh, hna⟩
          rw [hsrc]
          refine ⟨hh, ?_⟩
          constructor
          · exact fun ha => False.elim (hna ha)
          · intro hv
            rcases hv with ⟨psi, hd, hcnf, _⟩
            rw [decodeCircuit_encode] at hd
            cases hd
            have hm := (modeCheck_cnf_iff phi).2 hcnf
            rw [hmode] at hm
            contradiction

noncomputable def verifierPhase_of_residual
    (R : PhysicalRejectResidual) :
    P01VerifierPhase prepPhase.layout := by
  refine {
    stateCount := checkedVerifierStateCount
    machine := checkedVerifierFinMachine
    blank_none := checkedVerifierFinMachine_blank
    timeBound := canonicalVerifierTimeBound
    time_poly := canonicalVerifierTimeBound_poly
    halts := ?_
    correct := ?_
  }
  · intro source witness hw
    have h := (rawVerifier_halts_accepts_iff R witness source hw).1
    exact (checkedVerifierFinMachine_haltsWithin_iff
      (canonicalVerifierTimeBound source.length)
      (verifierStart witness source)).2 (by
        simpa [verifierStart, prepPhase_layout] using h)
  · intro source witness hw
    have h := (rawVerifier_halts_accepts_iff R witness source hw).2
    exact (checkedVerifierFinMachine_acceptsWithin_iff
      (canonicalVerifierTimeBound source.length)
      (verifierStart witness source)).2 (by
        simpa [verifierStart, prepPhase_layout] using h)

theorem p01ConstructionGap_of_physicalRejectResidual
    (R : PhysicalRejectResidual) :
    P01FinalCertificate.P01ConstructionGap :=
  p01_of_verifier (verifierPhase_of_residual R)

#print axioms MCore.Real.P01VerifierResidual.rawVerifier_halts_accepts_iff
#print axioms MCore.Real.P01VerifierResidual.verifierPhase_of_residual
#print axioms MCore.Real.P01VerifierResidual.p01ConstructionGap_of_physicalRejectResidual

end MCore.Real.P01VerifierResidual
