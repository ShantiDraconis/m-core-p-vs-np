import MCore.Real.P02CookLevinSameInputClosure
import MCore.Real.P02G21G22Attack

namespace MCore
namespace Real
namespace P02TargetClosure

open CanonicalFinalProof
open P02KleeneBridge
open P02KleeneCookLevinBridge
open P02CookLevinSameInputClosure
open P02G21G22Attack

structure P02ClosureData where
  compiler : ∀ M : PolyDTMCandidate, EffectiveDiagonalCompiler M
  carrier :
    ∀ M : PolyDTMCandidate,
      CookLevinCarrierData M (compiler M)
  cook_correct :
    ∀ M : PolyDTMCandidate,
      CookLevinCorrect (carrier M)
  same_input :
    ∀ M : PolyDTMCandidate,
      SameInputOfFixed (carrier M)

def P02ClosureData.toUniformBridge
    (D : P02ClosureData) :
    UniformCookLevinSameInputBridge where
  compiler := D.compiler
  data := fun M =>
    assembleCookLevinSameInputData
      (D.carrier M)
      (D.cook_correct M)
      (D.same_input M)

theorem P02ClosureData.closes_P02Target
    (D : P02ClosureData) :
    P02TerminalFrontier.P02Target :=
  uniformCookLevinBridge_closes_P02 D.toUniformBridge

theorem P02ClosureData.closes_G21
    (D : P02ClosureData) :
    G21Pointwise :=
  uniformCookLevinBridge_closes_G21 D.toUniformBridge

/-
Exact P02 worklist:
A. compiler: construct EffectiveDiagonalCompiler M.
B. carrier: define circuitOf c and selfInput c.
C. cook_correct: prove bounded Cook-Levin equivalence.
D. same_input: prove fixed-point transport to exact canonical encoded input.

Then C + D -> flips_of_fixed -> CanonicalSATFixedPointRealizer
-> DiagonalCounterexampleWitness -> DiagonalFamily
-> G21Pointwise -> P02Target.

No independent theorem remains between a P02ClosureData inhabitant and P02Target.
-/

#print axioms MCore.Real.P02TargetClosure.P02ClosureData.closes_P02Target
#print axioms MCore.Real.P02TargetClosure.P02ClosureData.closes_G21

end P02TargetClosure
end Real
end MCore
