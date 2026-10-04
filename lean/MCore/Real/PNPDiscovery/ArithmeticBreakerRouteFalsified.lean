import MCore.Real.PNPDiscovery.StrictLengthGrowth
import MCore.Real.PNPDiscovery.BarrierArithmeticFrontier

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof

/-- The former arithmetic breaker is only another spelling of the negation of
TerminalParityBarrier.  It therefore cannot count as a deeper producer. -/
theorem arithmeticBarrierBreaker_iff_not_barrier
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    ArithmeticBarrierBreaker M hTotal ↔
      ¬ TerminalParityBarrier M hTotal := by
  constructor
  · exact arithmeticBarrierBreaker_kills_barrier M hTotal
  · intro hNoBar
    intro Hbar
    exact False.elim (hNoBar Hbar)

/-- Strict length growth shows why the intended witness shape inside
ArithmeticBarrierBreaker can never occur on a live barrier branch. -/
theorem barrier_has_no_arithmeticBreaker_witness
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) :
    ¬ ∃ hLen :
        (orbit M hTotal seed (i + 1)).length =
          (orbit M hTotal seed ((i + 1) + (2 * d + 1))).length,
      let x := orbit M hTotal seed (i + 1)
      let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
      let W :=
        barrierFirstSourceMismatchWitness
          M hTotal Hbar seed i d hLen
      successorSharedConeEnvelope M x y ≤
        sourceCellOffsetLowerEnvelope
          M x.length (M.timeBound x.length) W.j := by
  rintro ⟨hLen, hRest⟩
  exact (no_positive_odd_length_recurrence
    M hTotal seed i d) hLen

/-- Classification marker: this route is formally equivalent to killing the
barrier and its intended same-length witness is impossible on the concrete
orbit. -/
def ArithmeticBreakerRouteFalsified : Prop :=
  ∀ M : PolyDTMCandidate, ∀ hTotal : DeclaredClockTotal M,
    ArithmeticBarrierBreaker M hTotal ↔
      ¬ TerminalParityBarrier M hTotal

theorem arithmeticBreakerRouteFalsified_closed :
    ArithmeticBreakerRouteFalsified := by
  intro M hTotal
  exact arithmeticBarrierBreaker_iff_not_barrier M hTotal

#print axioms MCore.Real.PNPDiscovery.arithmeticBarrierBreaker_iff_not_barrier
#print axioms MCore.Real.PNPDiscovery.barrier_has_no_arithmeticBreaker_witness
#print axioms MCore.Real.PNPDiscovery.arithmeticBreakerRouteFalsified_closed

end PNPDiscovery
end Real
end MCore
