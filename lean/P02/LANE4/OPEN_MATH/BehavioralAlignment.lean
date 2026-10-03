import P02.LANE4.StructuralClosure
import MCore.Real.P02BehavioralAlignment
import MCore.Real.P02ComplementRunRealization

namespace P02
namespace LANE4
namespace OPEN_MATH
namespace BehavioralAlignment

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.P02BehavioralAlignment
open MCore.Real.P02ComplementRunRealization
open MCore.Real.P02TotalCandidateKleeneReduction
open MCore.Real.PNPCookLevinMaterialMinCut

/-- Canonical reduction output used by the remaining semantic frontier. -/
abbrev reduceM
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) : BitString :=
  (complementSemanticReduction M hTotal).reduce x

/-- The already-closed Cook--Levin semantic fact. -/
theorem reduceM_sat_iff_not_accepts
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    CanonicalSAT (reduceM M hTotal x) ↔
      ¬ DeclaredAccepts M x := by
  simpa [reduceM] using complement_reduce_correct M hTotal x

/-- Exact positive branch: same declared behavior on source and reduction
output is precisely the witness consumed by BehavioralSelfAlignment. -/
def SameBehaviorAt
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) : Prop :=
  DeclaredAccepts M (reduceM M hTotal x) ↔
    DeclaredAccepts M x

theorem sameBehaviorAt_gives_behavioral_alignment
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString)
    (hSame : SameBehaviorAt M hTotal x) :
    BehavioralSelfAlignment M hTotal := by
  exact ⟨x, by simpa [SameBehaviorAt, reduceM] using hSame⟩

/-- The opposite branch does NOT give UniversalFailure.  Since acceptance is
Boolean-valued, opposite behavior together with Cook--Levin correctness makes
M agree with CanonicalSAT on the reduction output.  This theorem records the
direction explicitly so future work cannot accidentally promote that branch
to a lower-bound witness. -/
theorem oppositeBehaviorAt_implies_correct_on_reduction
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString)
    (hOpp :
      DeclaredAccepts M (reduceM M hTotal x) ↔
        ¬ DeclaredAccepts M x) :
    DeclaredAccepts M (reduceM M hTotal x) ↔
      CanonicalSAT (reduceM M hTotal x) := by
  rw [hOpp]
  exact (reduceM_sat_iff_not_accepts M hTotal x).symm

/-- A clock/fuel inequality alone is only a resource statement.  It does not
assert that an arbitrary candidate M interprets the Cook--Levin encoding,
recovers x, or simulates M on x.  The missing semantic content is therefore
kept as a separate producer rather than smuggled in through the clock. -/
def FuelDominatesSourceSimulation
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) : Prop :=
  M.timeBound (reduceM M hTotal x).length ≥
    M.timeBound x.length

/-- What would actually be sufficient: a genuine machine-specific theorem
turning a resource inequality plus the concrete encoding into behavioral
preservation.  This is intentionally a Prop interface, not an inhabitant. -/
def FuelToBehaviorBridge : Prop :=
  ∀ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString),
    FuelDominatesSourceSimulation M hTotal x →
      SameBehaviorAt M hTotal x

/-- A witness-producing fuel theorem plus a genuine FuelToBehaviorBridge would
close the remaining frontier.  This theorem is purely compositional and does
not assume UniversalFailure, not-InP, or P!=NP. -/
def FuelWitnessProducer : Prop :=
  ∀ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M),
    ∃ x : BitString, FuelDominatesSourceSimulation M hTotal x

theorem fuel_route_closes_behavioral_alignment
    (W : FuelWitnessProducer)
    (B : FuelToBehaviorBridge) :
    TotalBehavioralAlignmentProducer := by
  intro M hTotal
  rcases W M hTotal with ⟨x, hx⟩
  exact sameBehaviorAt_gives_behavioral_alignment
    M hTotal x (B M hTotal x hx)

/-- Exact remaining open material on the proposed fuel route. -/
structure FuelRouteProducer where
  witness : FuelWitnessProducer
  bridge : FuelToBehaviorBridge

theorem fuelRouteProducer_closes_T10
    (P : FuelRouteProducer) :
    TotalBehavioralAlignmentProducer :=
  fuel_route_closes_behavioral_alignment P.witness P.bridge

#print axioms P02.LANE4.OPEN_MATH.BehavioralAlignment.reduceM_sat_iff_not_accepts
#print axioms P02.LANE4.OPEN_MATH.BehavioralAlignment.oppositeBehaviorAt_implies_correct_on_reduction
#print axioms P02.LANE4.OPEN_MATH.BehavioralAlignment.fuel_route_closes_behavioral_alignment
#print axioms P02.LANE4.OPEN_MATH.BehavioralAlignment.fuelRouteProducer_closes_T10

end BehavioralAlignment
end OPEN_MATH
end LANE4
end P02
