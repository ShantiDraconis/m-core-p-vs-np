import MCore.Real.PNPDiscovery.ArithmeticRouteFalsified
import MCore.Real.PNPDiscovery.UniversalSimulationPrerequisites
import MCore.Real.PNPDiscovery.StrictLengthGrowth

namespace MCore
namespace Real
namespace PNPDiscovery
namespace KernelTestFalsifiedRoutes

open CanonicalFinalProof

/-- Negative regression: literal reduction fixed points stay impossible. -/
example (M : PolyDTMCandidate)
    (hTotal : P02TotalCandidateKleeneReduction.DeclaredClockTotal M) :
    ¬ LiteralReductionFixedPoint M hTotal :=
  strictGrowth_refutes_literalReductionFixedPoint M hTotal

/-- Negative regression: positive odd orbit points cannot have equal length. -/
example (M : PolyDTMCandidate)
    (hTotal : P02TotalCandidateKleeneReduction.DeclaredClockTotal M)
    (seed : BitString) (i d : Nat) :
    ¬ ((orbit M hTotal seed (i + 1)).length =
      (orbit M hTotal seed ((i + 1) + (2 * d + 1))).length) :=
  no_equalLength_positive_odd_pair M hTotal seed i d

/-- Negative regression: the same-length arithmetic breaker remains invalid
inside a live terminal barrier. -/
example (M : PolyDTMCandidate)
    (hTotal : P02TotalCandidateKleeneReduction.DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal) :
    ¬ ArithmeticBarrierBreaker M hTotal :=
  terminalBarrier_refutes_arithmeticBreaker M hTotal Hbar

#print axioms MCore.Real.PNPDiscovery.strictGrowth_refutes_literalReductionFixedPoint
#print axioms MCore.Real.PNPDiscovery.no_equalLength_positive_odd_pair
#print axioms MCore.Real.PNPDiscovery.terminalBarrier_refutes_arithmeticBreaker

end KernelTestFalsifiedRoutes
end PNPDiscovery
end Real
end MCore
