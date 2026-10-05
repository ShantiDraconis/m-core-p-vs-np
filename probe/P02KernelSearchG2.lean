import MCore.Real.P02TerminalForcingG2

namespace MCore
namespace Real
namespace P02KernelSearchG2

open CanonicalFinalProof
open P02UniversalFailureWitnessMaterial
open P02TerminalForcingG2

/--
T7-G2-COUNTEREXAMPLE search probe.
No axiom/sorry inhabitant is introduced; this asks Lean's tactic/search layer
whether an existing imported theorem/term already closes the material witness.
-/
example : UniversalFailureWitness := by
  exact?

example : UniversalFailureWitness := by
  aesop?

example : UniversalFailureWitness := by
  library_search

#check UniversalFailureWitness
#check failureGeneratorOfUniversalFailure
#check CounterexampleSelector
#check FailureLaw

end P02KernelSearchG2
end Real
end MCore
