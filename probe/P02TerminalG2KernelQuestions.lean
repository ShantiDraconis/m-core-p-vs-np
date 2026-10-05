import MCore.Real.P02TerminalForcingG2

namespace MCore
namespace Real
namespace P02TerminalG2KernelQuestions

open CanonicalFinalProof
open P02UniversalFailureWitnessMaterial
open P02TerminalForcingG2

#check CounterexampleSelector
#check FailureLaw
#check UniversalFailureWitness
#check G2_TERMINAL
#print UniversalFailureWitness
#print axioms failureLaw_iff_correctAt
#print axioms universalFailureWitnessOf
#print axioms g2_terminal_iff_witness

/-- Deliberately incomplete terminal constructor: Lean must expose the selector
M ↦ x_M and the universal FailureLaw as the only remaining fields. -/
example : Nonempty UniversalFailureWitness := by
  refine ⟨{
    counterexample := ?_
    fails := ?_ }⟩

/-- Same terminal asked in the expanded selector/law form. -/
example : G2_TERMINAL := by
  unfold G2_TERMINAL
  refine ⟨?_, ?_⟩

end P02TerminalG2KernelQuestions
end Real
end MCore
