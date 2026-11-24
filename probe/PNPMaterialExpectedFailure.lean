import MCore.Real.CanonicalCircuitBits
import MCore.Real.CanonicalFinalProof

namespace MCore.Real.PNPMaterialProbe

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits

/-
EXPECTED FAILURE TARGET.
No LowerBoundWitness.not_in_p, SeparationCertificate, or universal-failure
oracle is supplied.
-/
/-- error: unsolved goals
⊢ InNP (SATBits circuitBitEncoding) ∧ UniversalFailure (SATBits circuitBitEncoding) -/
#guard_msgs in
example :
    InNP (SATBits circuitBitEncoding) ∧
    UniversalFailure (SATBits circuitBitEncoding) := by
  skip

end MCore.Real.PNPMaterialProbe
