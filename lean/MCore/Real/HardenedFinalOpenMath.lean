import MCore.Real.HardenedFinalExternal

namespace MCore.Real.HardenedFinal

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open FailProofAllGaps
open P01FinalCertificate

/-- Exact hardened P-vs-NP residual: construct the canonical NP machine and a
universal deterministic failure generator for the same SAT bit-language. -/
def OpenMathResidual : Prop :=
  P01ConstructionGap ∧
  Nonempty (FailureGenerator (SATBits circuitBitEncoding))

theorem residual_closes_final
    (h : OpenMathResidual) :
    FinalExternalCertificate := by
  rcases h with ⟨hp01, hfail⟩
  rcases hfail with ⟨fail⟩
  exact ⟨hp01, fail⟩

end MCore.Real.HardenedFinal
