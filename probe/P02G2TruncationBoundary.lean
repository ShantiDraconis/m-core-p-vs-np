import MCore.Real.P02TerminalForcingG2
import MCore.Real.P02ClockBridgeMaterial
import MCore.Real.P02FiniteMachineDescription

namespace MCore
namespace Real
namespace P02G2TruncationBoundary

open CanonicalFinalProof
open P02UniversalFailureWitnessMaterial
open P02TerminalForcingG2
open P02ClockBridgeMaterial
open P02FiniteMachineDescription

/--
TRUNCATED_REAL boundary.

GREEN material already available:
* P02ClockBridgeMaterial;
* P02FiniteMachineDescription.

This probe intentionally exposes the final terminal gap with sorryAx.
It is not a CLOSED_GREEN proof and must never be imported by production material.
-/
def selfCodeForcado : PolyDTMCandidate → BitString :=
  fun M => List.ofFn (projectFiniteMachine M).accepting

theorem universalDisagreementForcado :
    ∀ M : PolyDTMCandidate,
      ¬ M.CorrectAt CanonicalSAT (selfCodeForcado M) := by
  sorry

def closeG2Forcado : UniversalFailureWitness :=
  { counterexample := selfCodeForcado
    fails := universalDisagreementForcado }

#print axioms MCore.Real.P02G2TruncationBoundary.universalDisagreementForcado
#print axioms MCore.Real.P02G2TruncationBoundary.closeG2Forcado

end P02G2TruncationBoundary
end Real
end MCore
