import MCore.Real.P01WitnessPrepGlobal
import MCore.Real.P01CheckedVerifierFiniteState
import MCore.Real.P01ExactVerifierCanonicalRun
import MCore.Real.P01RawSourceSplit
import MCore.Real.P01ExactVerifierGlobalBudget

namespace MCore
namespace Real
namespace P01VerifierPhaseMinCut

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01GuessedWitnessRelation
open P01IntegratedAssembly
open P01WitnessPrepGlobal
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierFiniteState
open P01ExactVerifierCanonicalRun
open P01ExactVerifierGlobalBudget
open P01RawSourceSplit
open P01WitnessPreservingPrep
open P01NTMRunLaws

abbrev CheckedVerifierConfig :=
  Configuration CheckedVerifierState (Option Bool)

/-- Canonical start configuration handed to the physical checked verifier. -/
def checkedVerifierStart
    (bs w : BitString) : CheckedVerifierConfig :=
  { state := checkedVerifierMachine.initial,
    tape := preparedTape w bs }

/--
The exact residual P01 mechanical min-cut.

All canonical sources are already covered by
`prepared_canonical_halts_within_exact_global` and
`prepared_canonical_accepts_iff_exact_global`.
Therefore only raw strings rejected by the canonical decoder remain.

This proposition asks for no SAT/P-vs-NP endpoint fact.  It requires only that
such noncanonical strings fail closed under the same fixed cubic verifier fuel.
-/
def RawSourceClosure : Prop :=
  ∀ (bs w : BitString),
    w.length = bs.length →
    decodeCircuit bs = none →
      checkedVerifierMachine.HaltsWithin
          (checkedVerifierExactTimeBound bs.length)
          (checkedVerifierStart bs w) ∧
        ¬ checkedVerifierMachine.AcceptsWithin
          (checkedVerifierExactTimeBound bs.length)
          (checkedVerifierStart bs w)

/-- The canonical and raw cases together give total verifier semantics. -/
theorem checked_total_of_raw_source_closure
    (H : RawSourceClosure)
    (bs w : BitString)
    (hw : w.length = bs.length) :
    checkedVerifierMachine.HaltsWithin
        (checkedVerifierExactTimeBound bs.length)
        (checkedVerifierStart bs w) ∧
      (checkedVerifierMachine.AcceptsWithin
          (checkedVerifierExactTimeBound bs.length)
          (checkedVerifierStart bs w) ↔
        VerifyBits bs w) := by
  rcases exact_encoding_or_decode_none bs with hcanonical | hraw
  · rcases hcanonical with ⟨phi, rfl⟩
    have hlen : varBound phi ≤ w.length := by
      rw [hw]
      exact varBound_le_encoded_length phi
    constructor
    · simpa [checkedVerifierStart] using
        prepared_canonical_halts_within_exact_global w phi hlen
    · simpa [checkedVerifierStart] using
        prepared_canonical_accepts_iff_exact_global w phi hlen
  · have h := H bs w hw hraw
    constructor
    · exact h.1
    · constructor
      · intro hacc
        exact False.elim (h.2 hacc)
      · intro hver
        exact False.elim ((verifyBits_false_of_decode_none bs w hraw) hver)

/--
Package the checked verifier as the unique remaining `P01VerifierPhase`.
The finite-state relabelling is already proved semantics-preserving.
-/
noncomputable def verifierPhaseOfRawSourceClosure
    (H : RawSourceClosure) :
    P01VerifierPhase prepPhase.layout where
  stateCount := checkedVerifierStateCount
  machine := checkedVerifierFinMachine
  blank_none := checkedVerifierFinMachine_blank
  timeBound := checkedVerifierExactTimeBound
  time_poly := checkedVerifierExactTimeBound_poly
  halts := by
    intro bs w hw
    have h :=
      (checked_total_of_raw_source_closure H bs w hw).1
    have hfin :=
      (checkedVerifierFinMachine_haltsWithin_iff
        (checkedVerifierExactTimeBound bs.length)
        (checkedVerifierStart bs w)).2 h
    change checkedVerifierFinMachine.HaltsWithin
      (checkedVerifierExactTimeBound bs.length)
      (liftConfig checkedVerifierStateEncode (checkedVerifierStart bs w))
    exact hfin
  correct := by
    intro bs w hw
    have h :=
      (checked_total_of_raw_source_closure H bs w hw).2
    have hfin :=
      checkedVerifierFinMachine_acceptsWithin_iff
        (checkedVerifierExactTimeBound bs.length)
        (checkedVerifierStart bs w)
    change
      (checkedVerifierFinMachine.AcceptsWithin
          (checkedVerifierExactTimeBound bs.length)
          (liftConfig checkedVerifierStateEncode (checkedVerifierStart bs w)) ↔
        VerifyBits bs w)
    exact hfin.trans h

/-- One raw fail-closed theorem closes the entire P01 construction gap. -/
theorem p01ConstructionGap_of_rawSourceClosure
    (H : RawSourceClosure) :
    P01FinalCertificate.P01ConstructionGap :=
  p01_of_verifier (verifierPhaseOfRawSourceClosure H)

#print axioms MCore.Real.P01VerifierPhaseMinCut.checked_total_of_raw_source_closure
#print axioms MCore.Real.P01VerifierPhaseMinCut.verifierPhaseOfRawSourceClosure
#print axioms MCore.Real.P01VerifierPhaseMinCut.p01ConstructionGap_of_rawSourceClosure

end P01VerifierPhaseMinCut
end Real
end MCore
