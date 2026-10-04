import MCore.Real.PNPDiscovery.ArithmeticRouteFalsified
import MCore.Real.P03PerfectFlipDichotomy
import MCore.Real.P02OddSemanticRecurrence

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02OddSemanticRecurrence
open P02TableauDynamics
open P03RangeFailureFrontier
open P03PerfectFlipDichotomy

/-- PerfectFlip forces terminal-state separation on every odd-separated orbit
pair: equal terminal states would give equal declared acceptance, contradicting
the odd semantic flip. -/
theorem perfectFlip_implies_terminalParityBarrier
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (hFlip : PerfectFlip M hTotal) :
    TerminalParityBarrier M hTotal := by
  intro seed i d hState
  have hObs :
      DeclaredAccepts M
          (orbit M hTotal seed (i + (2 * d + 1))) ↔
        DeclaredAccepts M (orbit M hTotal seed i) := by
    unfold DeclaredAccepts terminalState at *
    rw [hState]
  have hNeg :
      DeclaredAccepts M
          (orbit M hTotal seed (i + (2 * d + 1))) ↔
        ¬ DeclaredAccepts M (orbit M hTotal seed i) := by
    have hGeneric :=
      perfectFlip_odd_not_equiv
        hFlip seed i d
    have hOrbit := orbit_eq_genericOrbit M hTotal seed
    by_contra hNo
    apply hGeneric
    simpa [ObsEquiv, hOrbit] using hObs
  by_cases hA :
      DeclaredAccepts M (orbit M hTotal seed i)
  · have hB := hObs.mpr hA
    exact (hNeg.mp hB) hA
  · have hB := hNeg.mpr hA
    exact hA (hObs.mp hB)

/-- Therefore every real PerfectFlip candidate inhabits the strict-growth
parity regime exposed by the discovery lane. -/
theorem perfectFlip_to_strictGrowthParityRegime
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (hFlip : PerfectFlip M hTotal) :
    StrictGrowthParityRegime M hTotal :=
  terminalBarrier_to_strictGrowthRegime
    M hTotal
    (perfectFlip_implies_terminalParityBarrier M hTotal hFlip)

/-- A hypothetical deterministic polynomial-time SAT realization produces
exactly the live strict-growth parity regime. -/
theorem satRealization_to_strictGrowthParityRegime
    (D : PolyDTMRealization
      PNPCookLevinMaterialMinCut.CanonicalSAT) :
    ∃ hTotal : DeclaredClockTotal D.candidate,
      StrictGrowthParityRegime D.candidate hTotal := by
  rcases sat_realization_candidate_perfectFlip D with
    ⟨hTotal, hFlip⟩
  exact ⟨hTotal,
    perfectFlip_to_strictGrowthParityRegime
      D.candidate hTotal hFlip⟩

/-- Audit consequence: a uniform breaker for StrictGrowthParityRegime would
directly exclude every deterministic polynomial-time realization of SAT. -/
theorem strictGrowthParityBreakerProducer_implies_sat_not_inP
    (B : StrictGrowthParityBreakerProducer) :
    ¬ InP PNPCookLevinMaterialMinCut.CanonicalSAT := by
  intro hP
  rcases hP with ⟨D⟩
  rcases satRealization_to_strictGrowthParityRegime D with
    ⟨hTotal, hRegime⟩
  exact (B D.candidate hTotal) hRegime

#print axioms MCore.Real.PNPDiscovery.perfectFlip_implies_terminalParityBarrier
#print axioms MCore.Real.PNPDiscovery.perfectFlip_to_strictGrowthParityRegime
#print axioms MCore.Real.PNPDiscovery.satRealization_to_strictGrowthParityRegime
#print axioms MCore.Real.PNPDiscovery.strictGrowthParityBreakerProducer_implies_sat_not_inP

end PNPDiscovery
end Real
end MCore
