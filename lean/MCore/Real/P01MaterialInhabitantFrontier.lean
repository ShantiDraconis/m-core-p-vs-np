import MCore.Real.P01WitnessPrepGlobal
import MCore.Real.P01RawVerifierMaterialCore
import MCore.Real.P01CheckedVerifierFiniteState
import MCore.Real.P01IntegratedAssembly
import MCore.Real.P01MaterialGlobalBudget

namespace MCore
namespace Real
namespace P01MaterialInhabitantFrontier

open CanonicalFinalProof
open P01WitnessPreservingPrep
open P01WitnessPrepGlobal
open P01IntegratedAssembly
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierFiniteState
open P01MaterialGlobalBudget
open P01RawVerifierMaterialCore
open P01GuessedWitnessRelation

/-- The preparation half is a concrete existing inhabitant. -/
theorem prep_phase_inhabited :
    Nonempty P01PrepPhase :=
  ⟨prepPhase⟩

/-- Relabel a raw material verifier core into the exact Fin-indexed verifier
phase expected by the already-certified sequential assembly. -/
def verifierPhaseOfRawCore
    (K : RawVerifierMaterialCore) :
    P01VerifierPhase prepPhase.layout where
  stateCount := checkedVerifierStateCount
  machine := checkedVerifierFinMachine
  blank_none := checkedVerifierFinMachine_blank
  timeBound := materialVerifierGlobalTimeBound
  time_poly := materialVerifierGlobalTimeBound_poly
  halts := by
    intro bs w hw
    let cRaw : Configuration CheckedVerifierState (Option Bool) :=
      { state := checkedVerifierMachine.initial,
        tape := preparedTape w bs }
    have hRaw := K.halts bs w hw
    have hFin :=
      (checkedVerifierFinMachine_haltsWithin_iff
        (materialVerifierGlobalTimeBound bs.length) cRaw).2 hRaw
    simpa [cRaw, P01NTMRunLaws.liftConfig, prepPhase_layout] using hFin
  correct := by
    intro bs w hw
    let cRaw : Configuration CheckedVerifierState (Option Bool) :=
      { state := checkedVerifierMachine.initial,
        tape := preparedTape w bs }
    have hRel :=
      checkedVerifierFinMachine_acceptsWithin_iff
        (materialVerifierGlobalTimeBound bs.length) cRaw
    have hRaw := K.correct bs w hw
    calc
      checkedVerifierFinMachine.AcceptsWithin
          (materialVerifierGlobalTimeBound bs.length)
          { state := checkedVerifierFinMachine.initial,
            tape := prepPhase.layout bs w }
        ↔ checkedVerifierMachine.AcceptsWithin
            (materialVerifierGlobalTimeBound bs.length) cRaw := by
              simpa [cRaw, P01NTMRunLaws.liftConfig, prepPhase_layout] using hRel
      _ ↔ VerifyBits bs w := hRaw

/-- Once the raw physical verifier core is inhabited, the full P01 machine
construction follows with no additional mathematical premise. -/
theorem p01_of_raw_material_core
    (K : RawVerifierMaterialCore) :
    P01FinalCertificate.P01ConstructionGap :=
  p01_of_phases prepPhase (verifierPhaseOfRawCore K)

/-- Exact current P01 reduction. -/
theorem p01_reduced_to_raw_core :
    RawVerifierMaterialCore →
      P01FinalCertificate.P01ConstructionGap :=
  p01_of_raw_material_core

#print axioms MCore.Real.P01MaterialInhabitantFrontier.prep_phase_inhabited
#print axioms MCore.Real.P01MaterialInhabitantFrontier.verifierPhaseOfRawCore
#print axioms MCore.Real.P01MaterialInhabitantFrontier.p01_of_raw_material_core
#print axioms MCore.Real.P01MaterialInhabitantFrontier.p01_reduced_to_raw_core

end P01MaterialInhabitantFrontier
end Real
end MCore
