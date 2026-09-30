import MCore.Real.P01FinalCertificate
import MCore.Real.P02G21G22Attack

namespace MCore.Real
namespace CanonicalFinalExternal

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open FailProofAllGaps
open P01FinalCertificate
open P02G21G22Attack

/-- Exact internal final-external payload on one canonical bitstring SAT model. -/
structure FinalExternalCertificate : Prop where
  p01 : P01ConstructionGap
  g21 : G21Pointwise

/-- Canonical internal separation root. -/
def FINAL_ROOT : Prop :=
  PneqNP

theorem finalExternal_to_FINAL_ROOT
    (E : FinalExternalCertificate) :
    FINAL_ROOT := by
  have hP01 : SATInNPGap circuitBitEncoding :=
    construction_closes_p01 E.p01
  exact p01_g21_closes_internal hP01 E.g21

/-- External presentation adds only a proof that the chosen external P/NP
    predicates coincide with the hardened internal model. -/
structure OfficialFinalExternalCertificate
    (officialP officialNP : BitLanguage → Prop) : Prop
    extends FinalExternalCertificate where
  model_match : ExternalModelMatch officialP officialNP

def OFFICIAL_FINAL_ROOT
    (officialP officialNP : BitLanguage → Prop) : Prop :=
  OfficialPneqNP officialP officialNP

theorem officialFinalExternal_to_ROOT
    {officialP officialNP : BitLanguage → Prop}
    (E : OfficialFinalExternalCertificate officialP officialNP) :
    OFFICIAL_FINAL_ROOT officialP officialNP :=
  internal_separation_transfers E.model_match
    (finalExternal_to_FINAL_ROOT E.toFinalExternalCertificate)

#print axioms MCore.Real.CanonicalFinalExternal.finalExternal_to_FINAL_ROOT
#print axioms MCore.Real.CanonicalFinalExternal.officialFinalExternal_to_ROOT

end CanonicalFinalExternal
end MCore.Real
