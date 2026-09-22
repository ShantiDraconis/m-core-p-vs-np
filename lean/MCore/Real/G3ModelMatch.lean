import MCore.Real.FailProofAllGaps
import MCore.Real.EncodingNormalization

namespace MCore
namespace Real
namespace G3ModelMatch

open CanonicalFinalProof
open FailProofAllGaps
open OfficialModel
open EncodingNormalization

/-- Complete two-way bridge data required for G3.

The fields translate actual realization witnesses in both directions.
Consequently p_match/np_match below are derived, not postulated as an axiom. -/
structure G3ModelBridge (M : OfficialComplexityModel) where
  normalization : EncodingNormalization
  internalDTM_to_external :
    ∀ {L : BitLanguage},
      PolyDTMRealization L → M.PRealization L
  externalDTM_to_internal :
    ∀ {L : BitLanguage},
      M.PRealization L → PolyDTMRealization L
  internalNTM_to_external :
    ∀ {L : BitLanguage},
      PolyNTMRealization L → M.NPRealization L
  externalNP_to_internal :
    ∀ {L : BitLanguage},
      M.NPRealization L → PolyNTMRealization L

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
