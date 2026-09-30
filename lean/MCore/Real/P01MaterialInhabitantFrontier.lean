import MCore.Real.P01WitnessPrepGlobal
import MCore.Real.P01CheckedVerifierFiniteState
import MCore.Real.P01CheckedVerifierGlobalBudget
import MCore.Real.P01ExactBoundedCircuitProducer
import MCore.Real.P01ExactBoundedBinary
import MCore.Real.P01GuessedWitnessRelation

namespace MCore
namespace Real
namespace P01MaterialInhabitantFrontier

open CanonicalFinalProof
open CanonicalCircuitBits
open P01GuessedWitnessRelation
open P01WitnessPreservingPrep
open P01WitnessPrepGlobal
open P01IntegratedAssembly
open P01FinalCertificate
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierFiniteState
open P01CheckedVerifierGlobalBudget
open P01ExactBoundedCircuitProducer
open P01ExactBoundedBinary
open P01CNFMode

/-- The preparation half of P01 is already genuinely inhabited. -/
theorem prep_phase_inhabited :
    Nonempty P01PrepPhase :=
  ⟨prepPhase⟩

/--
Smallest remaining machine-level object for P01 after reusing the certified
preparation phase, the concrete checked verifier, its Fin relabelling, and the
global cubic time bound.

No SAT endpoint or P-vs-NP endpoint is stored as a field.
-/
structure VerifierMaterialCore : Prop where
  halts :
    ∀ (bs w : BitString), w.length = bs.length →
      checkedVerifierFinMachine.HaltsWithin
        (checkedVerifierGlobalTimeBound bs.length)
        { state := checkedVerifierFinMachine.initial,
          tape := preparedTape w bs }
  correct :
    ∀ (bs w : BitString), w.length = bs.length →
      (checkedVerifierFinMachine.AcceptsWithin
          (checkedVerifierGlobalTimeBound bs.length)
          { state := checkedVerifierFinMachine.initial,
            tape := preparedTape w bs } ↔
        VerifyBits bs w)

/-- A material core gives the exact verifier phase expected by the already
proved two-phase assembly theorem. -/
noncomputable def verifierPhaseOfCore
    (K : VerifierMaterialCore) :
    P01VerifierPhase prepPhase.layout where
  stateCount := checkedVerifierStateCount
  machine := checkedVerifierFinMachine
  blank_none := checkedVerifierFinMachine_blank
  timeBound := checkedVerifierGlobalTimeBound
  time_poly := checkedVerifierGlobalTimeBound_poly
  halts := by
    intro bs w hw
    simpa [prepPhase_layout] using K.halts bs w hw
  correct := by
    intro bs w hw
    simpa [prepPhase_layout] using K.correct bs w hw

/-- Therefore P01 is now reduced to exactly VerifierMaterialCore. -/
theorem p01_of_material_core
    (K : VerifierMaterialCore) :
    P01ConstructionGap :=
  p01_of_verifier (verifierPhaseOfCore K)

/--
The exact bounded recursive evaluator already has material producers for
input, constants and negation.  The only recursive constructors not yet
supplied by P01ExactBoundedCircuitProducer are the two binary constructors.
-/
structure BinaryExactCore : Prop where
  and_compose :
    ∀ (sigma : CircuitK1.Assignment)
      (witness : BitString)
      (mode : SyntaxMode)
      (left right : CircuitK1.Circuit),
      ExactBoundedCheckedCircuitRunCertificate sigma witness .cnf left →
      ExactBoundedCheckedCircuitRunCertificate sigma witness .cnf right →
      ExactBoundedCheckedCircuitRunCertificate sigma witness mode (.and left right)
  or_compose :
    ∀ (sigma : CircuitK1.Assignment)
      (witness : BitString)
      (mode : SyntaxMode)
      (left right : CircuitK1.Circuit),
      ExactBoundedCheckedCircuitRunCertificate sigma witness .clause left →
      ExactBoundedCheckedCircuitRunCertificate sigma witness .clause right →
      ExactBoundedCheckedCircuitRunCertificate sigma witness mode (.or left right)

/-- Once the two binary composers are supplied, structural recursion produces
the exact bounded certificate for every circuit and every requested syntax
mode.  All leaf/unary cases are already theorem-backed. -/
theorem exact_bounded_all_of_binary_core
    (K : BinaryExactCore)
    (sigma : CircuitK1.Assignment)
    (witness : BitString) :
    ∀ (phi : CircuitK1.Circuit) (mode : SyntaxMode),
      ExactBoundedCheckedCircuitRunCertificate sigma witness mode phi := by
  intro phi
  induction phi with
  | input i =>
      intro mode
      exact input_exact_bounded_certificate sigma witness mode i
  | const v =>
      intro mode
      exact const_exact_bounded_certificate sigma witness mode v
  | not child ih =>
      intro mode
      exact neg_exact_bounded_certificate
        sigma witness mode child (ih (childMode mode .neg))
  | and left right ihLeft ihRight =>
      intro mode
      exact K.and_compose sigma witness mode left right
        (ihLeft .cnf) (ihRight .cnf)
  | or left right ihLeft ihRight =>
      intro mode
      exact K.or_compose sigma witness mode left right
        (ihLeft .clause) (ihRight .clause)

/-- Mechanical frontier summary:
1. prove the two binary exact composers;
2. derive a global bounded checked-verifier run;
3. discharge VerifierMaterialCore.halts/correct;
4. P01ConstructionGap follows with no new endpoint hypothesis.
-/
theorem p01_reduced_frontier :
    (VerifierMaterialCore → P01ConstructionGap) ∧
    (BinaryExactCore →
      ∀ (sigma : CircuitK1.Assignment) (witness : BitString)
        (phi : CircuitK1.Circuit) (mode : SyntaxMode),
        ExactBoundedCheckedCircuitRunCertificate sigma witness mode phi) := by
  constructor
  · exact p01_of_material_core
  · intro K sigma witness phi mode
    exact exact_bounded_all_of_binary_core K sigma witness phi mode

#print axioms MCore.Real.P01MaterialInhabitantFrontier.prep_phase_inhabited
#print axioms MCore.Real.P01MaterialInhabitantFrontier.verifierPhaseOfCore
#print axioms MCore.Real.P01MaterialInhabitantFrontier.p01_of_material_core
#print axioms MCore.Real.P01MaterialInhabitantFrontier.binaryExactCore
#print axioms MCore.Real.P01MaterialInhabitantFrontier.exact_bounded_all
#print axioms MCore.Real.P01MaterialInhabitantFrontier.exact_bounded_all_of_binary_core
#print axioms MCore.Real.P01MaterialInhabitantFrontier.p01_reduced_frontier

end P01MaterialInhabitantFrontier
end Real
end MCore
