import MCore.Real.P02TerminalForcingG2

namespace MCore
namespace Real
namespace P02TerminalInhabitantProbeG2

open CanonicalFinalProof
open P02UniversalFailureWitnessMaterial
open P02TerminalForcingG2

/-
DIRECT TERMINAL ATTACK.
No UniversalFailure oracle, not-InP field, SeparationCertificate, axiom or sorry
is supplied. Lean must synthesize the actual selector M ↦ x_M and prove the
expanded universal FailureLaw.
-/
example : G2_TERMINAL := by
  unfold G2_TERMINAL
  refine ⟨?_, ?_⟩

end P02TerminalInhabitantProbeG2
end Real
end MCore
