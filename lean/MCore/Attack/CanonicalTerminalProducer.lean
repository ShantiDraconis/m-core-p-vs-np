import MCore.Real.CanonicalComplexityBridge
import MCore.BackwardAudit.OrientedWitnessBoundary

namespace MCore
namespace Attack

open Real
open Real.CanonicalComplexityBridge
open BackwardAudit

/-- Exact fixed official-model witness target for the canonical bit-language model. -/
structure CanonicalNotInPWitness where
  language : BitLanguage
  in_np : canonicalInterface.inNP language
  not_in_p : ¬ canonicalInterface.inP language

/-- The canonical interface already matches the repository's official InP/InNP predicates by rfl. -/
theorem canonicalModelMatch :
    ∀ L : BitLanguage,
      (canonicalInterface.inP L ↔ InP L) ∧
      (canonicalInterface.inNP L ↔ InNP L) := by
  intro L
  exact ⟨canonical_interface_p_match L, canonical_interface_np_match L⟩

/-- A genuine fixed not-in-P witness is exactly enough for the separation lane. -/
theorem canonicalWitness_closes_separation
    (w : CanonicalNotInPWitness) :
    SeparationFinal canonicalInterface.inP canonicalInterface.inNP := by
  exact typeB_closes_separation
    { language := w.language
      in_np := w.in_np
      not_in_p := w.not_in_p }

def terminalProducerStatus : String :=
  "OPEN_MATH: construct CanonicalNotInPWitness; canonical model matching is already PROVED/REUSE"

#print axioms canonicalModelMatch
#print axioms canonicalWitness_closes_separation

end Attack
end MCore
