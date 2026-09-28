import MCore.Real.CanonicalComplexityBridge
import MCore.Real.CookNormalizedDTMBridge
import MCore.Real.CookNormalizedNTMBridge

namespace MCore
namespace Real
namespace CookNormalizedOfficialBinding

open CanonicalFinalProof
open CanonicalComplexityBridge
open CookNormalizedMachineModel
open CookNormalizedDTMBridge
open CookNormalizedNTMBridge
open OfficialModel

/-- Exact deterministic-class binding between the canonical internal model and
the selected Cook-normalized external model. -/
theorem canonical_inP_iff_cook_normalized_P
    (L : BitLanguage) :
    canonicalInterface.inP L ↔ cookNormalizedSelection.model.P L := by
  constructor
  · rintro ⟨R⟩
    exact ⟨internalDTM_to_cook R⟩
  · rintro ⟨R⟩
    exact ⟨cookDTM_to_internal R⟩

/-- Exact nondeterministic-class binding between the canonical internal model
and the selected Cook-normalized external model. -/
theorem canonical_inNP_iff_cook_normalized_NP
    (L : BitLanguage) :
    canonicalInterface.inNP L ↔ cookNormalizedSelection.model.NP L := by
  constructor
  · rintro ⟨R⟩
    exact ⟨internalNTM_to_cook R⟩
  · rintro ⟨R⟩
    exact ⟨cookNTM_to_internal R⟩

/-- The legacy classical interface is therefore bound, class-for-class, to one
fixed external machine model carrying the pinned Cook/CMI provenance record.
This theorem does not assert P != NP. -/
theorem canonical_interface_bound_to_cook_normalized :
    (∀ L : BitLanguage,
      canonicalInterface.inP L ↔ cookNormalizedSelection.model.P L) ∧
    (∀ L : BitLanguage,
      canonicalInterface.inNP L ↔ cookNormalizedSelection.model.NP L) := by
  exact ⟨canonical_inP_iff_cook_normalized_P,
    canonical_inNP_iff_cook_normalized_NP⟩

#print axioms MCore.Real.CookNormalizedOfficialBinding.canonical_inP_iff_cook_normalized_P
#print axioms MCore.Real.CookNormalizedOfficialBinding.canonical_inNP_iff_cook_normalized_NP
#print axioms MCore.Real.CookNormalizedOfficialBinding.canonical_interface_bound_to_cook_normalized

end CookNormalizedOfficialBinding
end Real
end MCore
