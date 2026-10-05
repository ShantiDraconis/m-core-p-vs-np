import MCore.Real.P02TerminalForcingG2
import MCore.Real.P02UniversalFailureWitnessMaterial
import MCore.Real.FailProofAllGaps
import Mathlib.Tactic.LibrarySearch
import Aesop

namespace MCore
namespace Real
namespace P02KernelSearchG2V2

open CanonicalFinalProof
open P02UniversalFailureWitnessMaterial
open P02TerminalForcingG2
open FailProofAllGaps

set_option trace.aesop true

example : UniversalFailureWitness := by
  exact?

example : UniversalFailureWitness := by
  refine ⟨?counterexample, ?fails⟩
  case counterexample =>
    exact?
  case fails =>
    exact?

example : UniversalFailureWitness := by
  aesop?

example : UniversalFailureWitness := by
  library_search

#print MCore.Real.CanonicalFinalProof.PolyDTMCandidate
#check MCore.Real.CanonicalFinalProof.PolyDTMCandidate.timeBound
#check MCore.Real.CanonicalFinalProof.PolyDTMCandidate.CorrectAt
#check MCore.Real.P02UniversalFailureWitnessMaterial.CanonicalSAT
#check MCore.Real.FailProofAllGaps.failureGeneratorOfUniversalFailure

end P02KernelSearchG2V2
end Real
end MCore
