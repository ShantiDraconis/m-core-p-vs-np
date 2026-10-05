import MCore.Real.P02TerminalForcingG2

namespace MCore
namespace Real
namespace P02TerminalQuestionsG2

open CanonicalFinalProof
open P02UniversalFailureWitnessMaterial
open P02TerminalForcingG2

#check CounterexampleSelector
#check FailureLaw
#check UniversalFailureWitness
#check G2_TERMINAL

#print MCore.Real.P02TerminalForcingG2.CounterexampleSelector
#print MCore.Real.P02TerminalForcingG2.FailureLaw
#print MCore.Real.P02UniversalFailureWitnessMaterial.UniversalFailureWitness

/-- Direct constructor question. Intentionally incomplete: the kernel must expose
the exact two missing payloads, xM and its universal FailureLaw proof. -/
example : Nonempty UniversalFailureWitness := by
  constructor
  refine {
    counterexample := ?_
    fails := ?_
  }

end P02TerminalQuestionsG2
end Real
end MCore
