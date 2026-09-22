import MCore.Real.FailProofAllGaps
import MCore.Real.EncodingNormalization

namespace MCore
namespace Real
namespace G3ModelMatch

open CanonicalFinalProof
open FailProofAllGaps
open OfficialModel
open EncodingNormalization

/-- Polynomial overhead attached to one simulation direction.  The cost is
indexed by source input length and must itself be polynomial. -/
structure PolySimulationOverhead where
  cost : TimeBound
  cost_poly : PolynomialTimeBound cost

/-- Complete two-way bridge data required for G3.

All four realization translations are explicit, and every direction carries
its own polynomial simulation-overhead certificate.  Encoding normalization is
also part of the payload, so representation conversion cannot be hidden outside
the runtime model. -/
structure G3ModelBridge (M : OfficialComplexityModel) where
  normalization : EncodingNormalization

  internalDTM_to_external :
    ∀ {L : BitLanguage},
      PolyDTMRealization L → M.PRealization L
  internalDTM_to_external_overhead : PolySimulationOverhead

  externalDTM_to_internal :
    ∀ {L : BitLanguage},
      M.PRealization L → PolyDTMRealization L
  externalDTM_to_internal_overhead : PolySimulationOverhead

  internalNTM_to_external :
    ∀ {L : BitLanguage},
      PolyNTMRealization L → M.NPRealization L
  internalNTM_to_external_overhead : PolySimulationOverhead

  externalNP_to_internal :
    ∀ {L : BitLanguage},
      M.NPRealization L → PolyNTMRealization L
  externalNP_to_internal_overhead : PolySimulationOverhead

theorem G3ModelBridge.p_match
    {M : OfficialComplexityModel}
    (G : G3ModelBridge M)
    (L : BitLanguage) :
    InP L ↔ M.P L := by
  constructor
  · rintro ⟨R⟩
    exact ⟨G.internalDTM_to_external R⟩
  · rintro ⟨R⟩
    exact ⟨G.externalDTM_to_internal R⟩

theorem G3ModelBridge.np_match
    {M : OfficialComplexityModel}
    (G : G3ModelBridge M)
    (L : BitLanguage) :
    InNP L ↔ M.NP L := by
  constructor
  · rintro ⟨R⟩
    exact ⟨G.internalNTM_to_external R⟩
  · rintro ⟨R⟩
    exact ⟨G.externalNP_to_internal R⟩

def G3ModelBridge.toExternalModelMatch
    {M : OfficialComplexityModel}
    (G : G3ModelBridge M) :
    ExternalModelMatch M.P M.NP :=
  { p_match := G.p_match
    np_match := G.np_match }

/-- Exact G3 open payload for one selected external model. -/
def G3Gap (M : OfficialComplexityModel) : Prop :=
  Nonempty (G3ModelBridge M)

#print axioms MCore.Real.G3ModelMatch.G3ModelBridge.p_match
#print axioms MCore.Real.G3ModelMatch.G3ModelBridge.np_match

end G3ModelMatch
end Real
end MCore
