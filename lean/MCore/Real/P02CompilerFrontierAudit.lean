import MCore.Real.P02KleeneDefinednessFrontier
import MCore.Real.P02KleeneBridgeAudit

namespace MCore
namespace Real
namespace P02CompilerFrontierAudit

open CanonicalFinalProof
open P02FinalAttack
open P02KleeneBridge
open P02KleeneDefinednessFrontier

structure UniformZeroTotalKleeneCompiler where
  compiler : ∀ M : PolyDTMCandidate, EffectiveDiagonalCompiler M
  zero_total : ∀ M : PolyDTMCandidate, CompilerZeroTotal (compiler M)
  realizer :
    ∀ M : PolyDTMCandidate,
      CanonicalSATFixedPointRealizer M (compiler M)

noncomputable theorem closes_D3
    (U : UniformZeroTotalKleeneCompiler) :
    D3SemanticSelfReference := by
  let B : D3KleeneSATBridge :=
    { compiler := U.compiler
      realizer := U.realizer }
  exact kleene_sat_bridge_closes_D3 B

theorem zeroTotal_closes_definedness
    {M : PolyDTMCandidate}
    (K : EffectiveDiagonalCompiler M)
    (h : CompilerZeroTotal K) :
    KleeneDefinednessGap M K :=
  compilerZeroTotal_closes_definedness K h

#print axioms closes_D3
#print axioms zeroTotal_closes_definedness

end P02CompilerFrontierAudit
end Real
end MCore
