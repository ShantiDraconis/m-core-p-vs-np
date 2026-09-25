import MCore.Real.P01ConstructionGapClosure
import MCore.Real.P02TargetClosure
import MCore.Real.FinalExternalConsolidatedFlow

namespace MCore
namespace Real
namespace FinalProofCriticalClosures

open CanonicalFinalProof
open P01ConstructionGapClosure
open P02TargetClosure
open FinalExternalConsolidatedFlow

structure CriticalClosureData where
  p01 : P01ClosureData
  p02 : P02ClosureData
  g3 : G3ExternalContract

def CriticalClosureData.toExternalInputs
    (D : CriticalClosureData) :
    ConsolidatedExternalInputs where
  p01 := D.p01.toGap
  p02 := D.p02.closes_P02Target
  g3 := D.g3

/-
Critical chain:

P01MachineConstruction
-> P01ConstructionGap

EffectiveDiagonalCompiler
+ CookLevinCarrierData
+ CookLevinCorrect
+ SameInputOfFixed
-> flips_of_fixed
-> G21Pointwise
-> P02Target

P01ConstructionGap
+ P02Target
+ G3ExternalContract
-> ConsolidatedExternalInputs
-> existing FinalExternal certificate path.

This file does not assert that CriticalClosureData is inhabited.
-/

end FinalProofCriticalClosures
end Real
end MCore
