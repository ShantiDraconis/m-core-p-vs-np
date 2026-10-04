import MCore.Real.PNPDiscovery.StrictLengthGrowth
import MCore.Real.PNPDiscovery.BarrierArithmeticFrontier
import MCore.Real.PNPDiscovery.ArithmeticProducerClosure

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof

/-- The equal-length branch used by ArithmeticBarrierBreaker is structurally
impossible on every positive concrete Cook--Levin orbit. -/
theorem no_equalLength_positive_odd_pair
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (i d : Nat) :
    ¬
      ((orbit M hTotal seed (i + 1)).length =
        (orbit M hTotal seed ((i + 1) + (2 * d + 1))).length) := by
  exact no_positive_odd_length_recurrence
    M hTotal seed i d

/-- Therefore, if TerminalParityBarrier is inhabited, no
ArithmeticBarrierBreaker can be inhabited: its required same-length witness
contradicts strict length growth. -/
theorem terminalBarrier_refutes_arithmeticBreaker
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal) :
    ¬ ArithmeticBarrierBreaker M hTotal := by
  intro B
  rcases B Hbar with ⟨seed, i, d, hLen, hGrowth⟩
  exact (no_equalLength_positive_odd_pair
    M hTotal seed i d) hLen

/-- The previous arithmetic escape law collapses to its LENGTH branch on the
actual concrete orbit.  The source-offset branch is unreachable for positive
odd-separated orbit points. -/
theorem arithmeticEscape_collapses_to_length
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) :
    let x := orbit M hTotal seed (i + 1)
    let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
    x.length ≠ y.length := by
  dsimp
  exact no_positive_odd_length_recurrence
    M hTotal seed i d

/-- Classification of the previous deepest producer:
it is not a viable constructive route through a live barrier branch. -/
def ArithmeticBarrierBreakerRouteFalsified : Prop :=
  ∀ M : PolyDTMCandidate, ∀ hTotal : DeclaredClockTotal M,
    TerminalParityBarrier M hTotal →
      ¬ ArithmeticBarrierBreaker M hTotal

theorem arithmeticBarrierBreakerRoute_falsified :
    ArithmeticBarrierBreakerRouteFalsified := by
  intro M hTotal Hbar
  exact terminalBarrier_refutes_arithmeticBreaker M hTotal Hbar

/-- New canonical counter-regime after eliminating the dead same-length route:
strict length growth plus terminal parity separation. -/
structure StrictGrowthParityRegime
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) : Prop where
  barrier : TerminalParityBarrier M hTotal
  strictGrowth :
    ∀ seed : BitString, ∀ n : Nat,
      (orbit M hTotal seed n).length <
        (orbit M hTotal seed (n + 1)).length

theorem terminalBarrier_to_strictGrowthRegime
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal) :
    StrictGrowthParityRegime M hTotal :=
  { barrier := Hbar
    strictGrowth := orbit_length_strictly_increases M hTotal }

/-- The genuine next material task is therefore to eliminate this
strict-growth parity regime without relying on length recurrence. -/
def StrictGrowthParityBreaker
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) : Prop :=
  StrictGrowthParityRegime M hTotal → False

def StrictGrowthParityBreakerProducer : Prop :=
  ∀ M : PolyDTMCandidate, ∀ hTotal : DeclaredClockTotal M,
    StrictGrowthParityBreaker M hTotal

theorem strictGrowthParityBreaker_kills_terminalBarrier
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (B : StrictGrowthParityBreaker M hTotal) :
    ¬ TerminalParityBarrier M hTotal := by
  intro Hbar
  exact B (terminalBarrier_to_strictGrowthRegime M hTotal Hbar)

#print axioms MCore.Real.PNPDiscovery.no_equalLength_positive_odd_pair
#print axioms MCore.Real.PNPDiscovery.terminalBarrier_refutes_arithmeticBreaker
#print axioms MCore.Real.PNPDiscovery.arithmeticEscape_collapses_to_length
#print axioms MCore.Real.PNPDiscovery.arithmeticBarrierBreakerRoute_falsified
#print axioms MCore.Real.PNPDiscovery.terminalBarrier_to_strictGrowthRegime
#print axioms MCore.Real.PNPDiscovery.strictGrowthParityBreaker_kills_terminalBarrier

end PNPDiscovery
end Real
end MCore
