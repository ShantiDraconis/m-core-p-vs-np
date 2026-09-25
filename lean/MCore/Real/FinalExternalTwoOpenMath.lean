import MCore.Real.P01FinalCertificate
import MCore.Real.P02SemanticSelfEmbeddingClose
import MCore.Real.CookNormalizedG3Contract
import MCore.Real.FinalExternalCertificate

namespace MCore
namespace Real
namespace FinalExternalTwoOpenMath

open CanonicalCircuitBits
open CanonicalSATBoundary
open P01FinalCertificate
open P02SemanticSelfEmbeddingClose
open CookNormalizedG3Contract
open FinalExternalCertificate

/-- Exact terminal mathematical payload after all reusable infrastructure is closed. -/
structure TwoOpenMathInputs where
  p01 : P01MachineConstruction
  p02 : UniversalWitnessExists

def TwoOpenMathInputs.toFinalExternalInputs
    (I : TwoOpenMathInputs) :
    FinalExternalInputs where
  g1 := construction_closes_p01 ⟨I.p01⟩
  g2 := by
    have hP02 := universal_witness_closes_p02 I.p02
    rcases hP02 with ⟨G⟩
    exact G
  g3 := cookNormalizedExternalContract

theorem two_open_math_closes_external
    (I : TwoOpenMathInputs) :
    OfficialPneqNP
      cookNormalizedSelection.model.P
      cookNormalizedSelection.model.NP := by
  exact final_external_certificate I.toFinalExternalInputs

def FinalOpenMathBoundary : Prop :=
  Nonempty TwoOpenMathInputs

theorem final_open_math_boundary_closes
    (h : FinalOpenMathBoundary) :
    OfficialPneqNP
      cookNormalizedSelection.model.P
      cookNormalizedSelection.model.NP := by
  rcases h with ⟨I⟩
  exact two_open_math_closes_external I

#print axioms MCore.Real.FinalExternalTwoOpenMath.two_open_math_closes_external
#print axioms MCore.Real.FinalExternalTwoOpenMath.final_open_math_boundary_closes

end FinalExternalTwoOpenMath
end Real
end MCore
