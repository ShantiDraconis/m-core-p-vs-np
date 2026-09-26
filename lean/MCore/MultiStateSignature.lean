import MCore.Signature
import MCore.Real.CanonicalFinalProof
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace SharedSignature

open Real
open Real.CanonicalFinalProof
open Real.CanonicalCircuitBits

/-- A single natural-number signature that is realized by at least two
distinct states inside every problem in the indexed family. -/
structure MultiStateSignature (Problem : Type) where
  code : Nat
  State : Problem → Type
  observable : (p : Problem) → State p → Nat
  multi_realized :
    ∀ p : Problem,
      ∃ a b : State p,
        a ≠ b ∧
        observable p a = code ∧
        observable p b = code

/-- The exact universal existence claim suggested by the shared-signature
program. No inhabitant is asserted here. -/
def UniversalMultiStateSignature (Problem : Type) : Prop :=
  Nonempty (MultiStateSignature Problem)

/-- Any inhabitant exposes one common numerical signature realized by
multiple distinct states in every problem. -/
theorem common_signature_of_multistate
    {Problem : Type}
    (S : MultiStateSignature Problem) :
    ∃ σ : Nat,
      ∀ p : Problem,
        ∃ a b : S.State p,
          a ≠ b ∧
          S.observable p a = σ ∧
          S.observable p b = σ := by
  refine ⟨S.code, ?_⟩
  intro p
  exact S.multi_realized p

/-- Existential form of the same theorem. -/
theorem universal_multistate_signature_iff
    {Problem : Type} :
    UniversalMultiStateSignature Problem ↔
      ∃ (State : Problem → Type)
        (observable : (p : Problem) → State p → Nat)
        (σ : Nat),
        ∀ p : Problem,
          ∃ a b : State p,
            a ≠ b ∧
            observable p a = σ ∧
            observable p b = σ := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.State, S.observable, S.code, S.multi_realized⟩
  · rintro ⟨State, observable, σ, h⟩
    exact ⟨{
      code := σ
      State := State
      observable := observable
      multi_realized := h
    }⟩

/-- Adapter required before a shared numerical signature may be promoted to
the canonical P-vs-NP lower-bound endpoint.  The adapter is intentionally a
separate object: the signature alone does not imply a complexity lower bound. -/
structure PNPSignatureAdapter
    {Problem : Type}
    (S : MultiStateSignature Problem) where
  signatureObstruction : Nat → Prop
  code_obstructs : signatureObstruction S.code
  obstruction_to_failure :
    signatureObstruction S.code →
      UniversalFailure
        (Real.CanonicalSATBoundary.SATBits circuitBitEncoding)

/-- A certified adapter promotes the shared signature to the exact PNP
OPEN_MATH producer. -/
theorem multistate_signature_with_adapter_closes_pnp_frontier
    {Problem : Type}
    (S : MultiStateSignature Problem)
    (A : PNPSignatureAdapter S) :
    UniversalFailure
      (Real.CanonicalSATBoundary.SATBits circuitBitEncoding) :=
  A.obstruction_to_failure A.code_obstructs

#print axioms MCore.SharedSignature.common_signature_of_multistate
#print axioms MCore.SharedSignature.universal_multistate_signature_iff
#print axioms MCore.SharedSignature.multistate_signature_with_adapter_closes_pnp_frontier

end SharedSignature
end MCore
