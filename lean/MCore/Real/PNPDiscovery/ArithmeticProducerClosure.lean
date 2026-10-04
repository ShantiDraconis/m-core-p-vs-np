import MCore.Real.PNPDiscovery.BarrierArithmeticFrontier
import MCore.Real.PNPDiscovery.TerminalStateFrontier

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof

/-- Per-candidate arithmetic breaker forces the positive recurrence branch of
the already-closed terminal-state dichotomy. -/
theorem arithmeticBreaker_forces_terminalRecurrence
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (B : ArithmeticBarrierBreaker M hTotal) :
    OddTerminalStateRecurrence M hTotal := by
  rcases terminalRecurrence_or_parityBarrier M hTotal with
    hRec | hBar
  · exact hRec
  · exact False.elim
      ((arithmeticBarrierBreaker_kills_barrier
        M hTotal B) hBar)

/-- Uniform arithmetic breakers therefore produce the exact diagonal
inhabitant. -/
theorem arithmeticBarrierBreakerProducer_to_exact
    (B : ArithmeticBarrierBreakerProducer) :
    TotalExactDiagonalProducer := by
  apply terminalStateRecurrence_to_exact
  intro M hTotal
  exact arithmeticBreaker_forces_terminalRecurrence
    M hTotal (B M hTotal)

/-- Current deepest material producer.  This is not marked CLOSED: producing
it uniformly is the new mathematical task exposed by the kernel-oriented
decomposition. -/
def CurrentDeepestMaterialProducer : Prop :=
  ArithmeticBarrierBreakerProducer

theorem currentDeepestProducer_closes_separationSide
    (B : CurrentDeepestMaterialProducer) :
    TotalExactDiagonalProducer :=
  arithmeticBarrierBreakerProducer_to_exact B

#print axioms MCore.Real.PNPDiscovery.arithmeticBreaker_forces_terminalRecurrence
#print axioms MCore.Real.PNPDiscovery.arithmeticBarrierBreakerProducer_to_exact
#print axioms MCore.Real.PNPDiscovery.currentDeepestProducer_closes_separationSide

end PNPDiscovery
end Real
end MCore
