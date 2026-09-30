import MCore.Real.FinalProof
import MCore.Real.CanonicalSATNTMAttack
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace FinalExternalCanonical

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATNTMAttack

/-- Deterministic polynomial-time candidate with a fixed canonical input map.
The candidate cannot choose an input encoder and therefore cannot precompute
language membership outside the machine runtime. -/
structure CanonicalPolyDTMCandidate where
  State : Type
  machine : TM State (Option Bool)
  accepting : State → Bool
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

def CanonicalPolyDTMCandidate.encode
    (candidate : CanonicalPolyDTMCandidate)
    (φ : Circuit) :
    Configuration candidate.State (Option Bool) :=
  initialTMConfig candidate.machine (encodeCircuit φ)

def CanonicalPolyDTMCandidate.CorrectAt
    (candidate : CanonicalPolyDTMCandidate)
    (language : CircuitLanguage)
    (φ : Circuit) : Prop :=
  candidate.machine.HaltsWithin
      (candidate.timeBound (CircuitK1.size φ))
      (candidate.encode φ) ∧
    (candidate.accepting
        (candidate.machine.run
          (candidate.timeBound (CircuitK1.size φ))
          (candidate.encode φ)).state = true ↔ language φ)

structure CanonicalPolyDTMRealization
    (language : CircuitLanguage) where
  candidate : CanonicalPolyDTMCandidate
  decides : ∀ φ : Circuit, candidate.CorrectAt language φ

def CanonicalInP (language : CircuitLanguage) : Prop :=
  Nonempty (CanonicalPolyDTMRealization language)

def CanonicalSATNotInP : Prop :=
  ¬ CanonicalInP SATLanguage

def CanonicalUniversalSATFailure : Prop :=
  ∀ candidate : CanonicalPolyDTMCandidate,
    ∃ φ : Circuit, ¬ candidate.CorrectAt SATLanguage φ

theorem canonical_universal_failure_implies_not_in_p
    (h : CanonicalUniversalSATFailure) :
    CanonicalSATNotInP := by
  intro hp
  rcases hp with ⟨R⟩
  rcases h R.candidate with ⟨φ, hbad⟩
  exact hbad (R.decides φ)

theorem canonical_not_in_p_implies_universal_failure
    (h : CanonicalSATNotInP) :
    CanonicalUniversalSATFailure := by
  intro candidate
  apply Classical.byContradiction
  intro hnone
  apply h
  refine ⟨{ candidate := candidate, decides := ?_ }⟩
  intro φ
  apply Classical.byContradiction
  intro hbad
  exact hnone ⟨φ, hbad⟩

structure CanonicalSATLowerBoundCertificate : Prop where
  fail_proof : CanonicalUniversalSATFailure

def FINAL_EXTERNAL : Prop :=
  CanonicalSATMachineClosure ∧ CanonicalSATLowerBoundCertificate

def FINAL_ROOT : Prop :=
  CanonicalSATMachineClosure ∧ CanonicalSATNotInP

theorem final_external_to_root
    (h : FINAL_EXTERNAL) :
    FINAL_ROOT :=
  ⟨h.1, canonical_universal_failure_implies_not_in_p h.2.fail_proof⟩

#print axioms MCore.Real.FinalExternalCanonical.canonical_universal_failure_implies_not_in_p
#print axioms MCore.Real.FinalExternalCanonical.canonical_not_in_p_implies_universal_failure
#print axioms MCore.Real.FinalExternalCanonical.final_external_to_root

end FinalExternalCanonical
end Real
end MCore
