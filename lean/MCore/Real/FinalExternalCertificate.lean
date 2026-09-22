import MCore.Real.CanonicalSATBoundary
import MCore.Real.CanonicalCircuitBits
import MCore.Real.G3ModelMatch

namespace MCore
namespace Real
namespace FinalExternalCertificate

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open FailProofAllGaps
open OfficialModel
open G3ModelMatch

/-- The exact three-producer payload for the external certificate.

G1 is a concrete canonical SAT NP realization.
G2 is a concrete universal deterministic failure generator.
G3 is the two-way bridge to one externally selected reference-bearing model. -/
structure FinalExternalInputs (M : OfficialComplexityModel) where
  g1 : SATInNPGap circuitBitEncoding
  g2 : FailureGenerator (SATBits circuitBitEncoding)
  g3 : G3ModelBridge M

def FinalExternalInputs.toSATExternalClosure
    {M : OfficialComplexityModel}
    (I : FinalExternalInputs M) :
    SATExternalClosure M.P M.NP :=
  { encoding := circuitBitEncoding
    sat_in_np := I.g1
    fail_generator := I.g2
    model_match := I.g3.toExternalModelMatch }

def FinalExternalInputs.toFinalGapCertificate
    {M : OfficialComplexityModel}
    (I : FinalExternalInputs M) :
    FinalGapCertificate M.P M.NP :=
  { target := SATBits circuitBitEncoding
    target_in_np := I.g1
    fail_generator := I.g2
    model_match := I.g3.toExternalModelMatch }

theorem final_external_certificate
    {M : OfficialComplexityModel}
    (I : FinalExternalInputs M) :
    OfficialPneqNP M.P M.NP := by
  exact final_gap_certificate_closes I.toFinalGapCertificate

/-- Fail-closed external frontier.  It remains OPEN until G1+G2+G3 are all
inhabited; no no-hypothesis final theorem is manufactured in this file. -/
def FinalExternalGap (M : OfficialComplexityModel) : Prop :=
  Nonempty (FinalExternalInputs M)

theorem final_external_gap_closes
    {M : OfficialComplexityModel}
    (h : FinalExternalGap M) :
    OfficialPneqNP M.P M.NP := by
  rcases h with ⟨I⟩
  exact final_external_certificate I

#print axioms MCore.Real.FinalExternalCertificate.final_external_certificate
#print axioms MCore.Real.FinalExternalCertificate.final_external_gap_closes

end FinalExternalCertificate
end Real
end MCore
