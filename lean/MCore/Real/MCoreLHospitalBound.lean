import MCore.Real.P02BoundedPartSemantics
import MCore.Real.P02SemanticSelfEmbeddingClose
import MCore.Real.P01FinalCertificate
import MCore.Real.CookNormalizedG3Contract
import MCore.Real.FinalExternalCertificate

namespace MCore
namespace Real
namespace MCoreLHospitalBound

open CanonicalFinalProof
open CanonicalCircuitBits
open P02BoundedPartSemantics
open P02SemanticSelfEmbeddingClose
open P01FinalCertificate
open CookNormalizedG3Contract
open FinalExternalCertificate

/--
M-Core indeterminate constants are codes whose semantic evaluation at the
distinguished input is bottom.  This definition is descriptive only: it does
not make semantic divergence decidable and does not assert that bottom later
becomes a finite `evaln` value.
-/
def IndeterminateConstants : Type :=
  { c : Nat.Partrec.Code // DivergesAtZero c }

/--
Single explicit M-Core hypothesis used by the conditional lane.

Repository-level meaning: the M-Core L'Hospital rule supplies the exact
bounded diagonal witnesses required by the already-existing P02 semantic
self-embedding endpoint.  Keeping the assumption at this interface avoids the
inconsistent statement `c.eval 0 = ⊥ -> ∃ fuel, c.evaln fuel 0 = some v`,
which contradicts `evaln_sound`.

This proposition is the one unresolved assumption of this conditional module.
-/
def MCoreLHospitalBound : Prop :=
  UniversalWitnessExists

/--
Temporary explicit assumption.  Any theorem depending on this axiom remains
conditional until `MCoreLHospitalBound` is proved without this axiom.
-/
axiom MCORE_LHOSPITAL_AXIOM : MCoreLHospitalBound

/-- Conditional P02 closure under the explicit M-Core hypothesis. -/
theorem P02Target_conditional
    (h : MCoreLHospitalBound) :
    P02TerminalFrontier.P02Target := by
  exact universal_witness_closes_p02 h

/--
Conditional external-input producer.  P01 is still supplied through the
repository's actual P01 construction producer; G3 uses the existing normalized
external contract.  No field of `FinalExternalInputs` is fabricated.
-/
theorem FinalExternalGap_conditional
    (hLH : MCoreLHospitalBound)
    (hP01 : P01ConstructionGap) :
    FinalExternalGap := by
  have hG1 : SATInNPGap circuitBitEncoding :=
    construction_closes_p01 hP01
  have hP02 : P02TerminalFrontier.P02Target :=
    P02Target_conditional hLH
  rcases hP02 with ⟨G⟩
  exact ⟨{
    g1 := hG1
    g2 := G
    g3 := cookNormalizedExternalContract
  }⟩

/--
Explicit axiom-backed conditional endpoint.  The axiom remains visible in
`#print axioms`; therefore this theorem is not an unconditional proof.
-/
theorem FinalExternalGap_assumed
    (hP01 : P01ConstructionGap) :
    FinalExternalGap :=
  FinalExternalGap_conditional MCORE_LHOSPITAL_AXIOM hP01

/--
Audit theorem: semantic bottom cannot itself yield a finite `evaln` result.
This guards the conditional M-Core rule from being misread as a theorem about
Mathlib's `Part` bottom becoming defined.
-/
theorem bottom_has_no_bounded_value
    (I : IndeterminateConstants)
    (fuel v : Nat) :
    I.val.evaln fuel 0 ≠ some v := by
  intro h
  have hall :=
    divergence_implies_all_evaln_none I.property fuel
  rw [hall] at h
  contradiction

#print axioms MCore.Real.MCoreLHospitalBound.P02Target_conditional
#print axioms MCore.Real.MCoreLHospitalBound.FinalExternalGap_conditional
#print axioms MCore.Real.MCoreLHospitalBound.FinalExternalGap_assumed
#print axioms MCore.Real.MCoreLHospitalBound.bottom_has_no_bounded_value

end MCoreLHospitalBound
end Real
end MCore
