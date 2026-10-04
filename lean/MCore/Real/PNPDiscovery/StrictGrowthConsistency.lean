import MCore.Real.PNPDiscovery.ArithmeticRouteFalsified
import MCore.Real.P03PerfectFlipConstruction
import MCore.Real.P02TableauDynamics

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02TableauDynamics
open P03RangeFailureFrontier
open P03PerfectFlipConstruction

/-- Abstract consistency witness showing that strict growth plus parity flipping
is not itself contradictory. -/
def toyLength (n : Nat) : Nat := n + 1

def toyObs (n : Nat) : Bool :=
  n % 2 = 1

theorem toyLength_strict :
    ∀ n : Nat, toyLength n < toyLength (n + 1) := by
  intro n
  simp [toyLength]

theorem toyObs_flips :
    ∀ n : Nat, toyObs (n + 1) = ! toyObs n := by
  intro n
  unfold toyObs
  omega

/-- Therefore no argument using only "length strictly increases" plus a
two-valued alternating observable can refute the counter-regime. -/
structure AbstractStrictGrowthFlipModel where
  len : Nat → Nat
  obs : Nat → Bool
  strict : ∀ n, len n < len (n + 1)
  flip : ∀ n, obs (n + 1) = ! obs n

def abstractStrictGrowthFlipModel :
    AbstractStrictGrowthFlipModel :=
  { len := toyLength
    obs := toyObs
    strict := toyLength_strict
    flip := toyObs_flips }

/-- Operational content of a perfect flip: on the larger successor encoding,
the candidate must return the negation of its decision on the recovered source. -/
def OperationalSelfSimulationLaw
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) : Prop :=
  ∀ x : BitString,
    DeclaredAccepts M (R_M M hTotal x) ↔
      ¬ DeclaredAccepts M x

theorem operationalSelfSimulation_iff_perfectFlip
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    OperationalSelfSimulationLaw M hTotal ↔
      PerfectFlip M hTotal := by
  rfl

/-- The source itself is concretely recoverable from the larger successor
encoding.  Thus source availability is CLOSED and cannot be the obstruction. -/
theorem operational_source_available
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    decodeSourceBits
        (complementToNTMCandidate M)
        x.length
        (M.timeBound x.length)
        (R_M M hTotal x) =
      some x := by
  exact R_M_source_recover M hTotal x

#print axioms MCore.Real.PNPDiscovery.toyLength_strict
#print axioms MCore.Real.PNPDiscovery.toyObs_flips
#print axioms MCore.Real.PNPDiscovery.operationalSelfSimulation_iff_perfectFlip
#print axioms MCore.Real.PNPDiscovery.operational_source_available

end PNPDiscovery
end Real
end MCore
