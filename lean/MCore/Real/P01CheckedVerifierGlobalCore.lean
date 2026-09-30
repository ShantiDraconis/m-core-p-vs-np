import MCore.Real.P01CheckedVerifierFiniteState
import MCore.Real.P01WitnessPrepGlobal

namespace MCore
namespace Real
namespace P01CheckedVerifierGlobalCore

open CanonicalFinalProof
open CanonicalCircuitBits
open P01IntegratedAssembly
open P01WitnessPrepGlobal
open P01WitnessPreservingPrep
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierFiniteState
open P01NTMRunLaws

/--
Smallest concrete P01 mechanical target after fixing all wiring.

The machine, alphabet, state encoding and handoff layout are fixed.  A producer
must supply only one polynomial time bound and the two global execution facts
for the existing checked verifier.
-/
structure CheckedVerifierGlobalCore where
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  halts : ∀ (bs w : BitString), w.length = bs.length →
    checkedVerifierMachine.HaltsWithin
      (timeBound bs.length)
      { state := checkedVerifierMachine.initial,
        tape := preparedTape w bs }
  correct : ∀ (bs w : BitString), w.length = bs.length →
    (checkedVerifierMachine.AcceptsWithin
        (timeBound bs.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape w bs } ↔
      P01GuessedWitnessRelation.VerifyBits bs w)

/-- The fixed-machine core packages directly as the already-reduced verifier phase. -/
noncomputable def CheckedVerifierGlobalCore.toVerifierPhase
    (C : CheckedVerifierGlobalCore) :
    P01VerifierPhase prepPhase.layout where
  stateCount := checkedVerifierStateCount
  machine := checkedVerifierFinMachine
  blank_none := checkedVerifierFinMachine_blank
  timeBound := C.timeBound
  time_poly := C.time_poly
  halts := by
    intro bs w hw
    have h := C.halts bs w hw
    have hfin :
        checkedVerifierFinMachine.HaltsWithin (C.timeBound bs.length)
          (liftConfig checkedVerifierStateEncode
            { state := checkedVerifierMachine.initial,
              tape := preparedTape w bs }) :=
      (checkedVerifierFinMachine_haltsWithin_iff
        (C.timeBound bs.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape w bs }).2 h
    simpa [prepPhase_layout, checkedVerifierFinMachine,
      P01IntegratedAssembly.relabel, liftConfig] using hfin
  correct := by
    intro bs w hw
    have h := C.correct bs w hw
    have hfin :
        (checkedVerifierFinMachine.AcceptsWithin (C.timeBound bs.length)
            (liftConfig checkedVerifierStateEncode
              { state := checkedVerifierMachine.initial,
                tape := preparedTape w bs }) ↔
          P01GuessedWitnessRelation.VerifyBits bs w) :=
      (checkedVerifierFinMachine_acceptsWithin_iff
        (C.timeBound bs.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape w bs }).trans h
    simpa [prepPhase_layout, checkedVerifierFinMachine,
      P01IntegratedAssembly.relabel, liftConfig] using hfin

/-- No further P01 wiring remains after this core. -/
theorem p01ConstructionGap_of_core
    (C : CheckedVerifierGlobalCore) :
    P01FinalCertificate.P01ConstructionGap :=
  p01_of_verifier C.toVerifierPhase

#print axioms MCore.Real.P01CheckedVerifierGlobalCore.CheckedVerifierGlobalCore.toVerifierPhase
#print axioms MCore.Real.P01CheckedVerifierGlobalCore.p01ConstructionGap_of_core

end P01CheckedVerifierGlobalCore
end Real
end MCore
