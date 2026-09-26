import MCore.Real.CanonicalFinalProof
import MCore.Real.CanonicalCircuitBits
import MCore.Real.P02TerminalFrontier

namespace MCore
namespace Real
namespace PNPSelfTheoremCircularityAudit20260926

open CanonicalFinalProof
open CanonicalCircuitBits
open P02TerminalFrontier

/-- "Use the theorem itself" in its exact canonical form:
assuming SAT is not in P, one obtains the universal failure inhabitant.
This is valid transport, but not a producer. -/
theorem sat_not_in_p_to_universalFailure
    (h : ¬ InP (SATBits circuitBitEncoding)) :
    UniversalFailure (SATBits circuitBitEncoding) :=
  not_in_p_implies_universal_failure h

/-- The converse is already known. Together these show that the proposed
self-theorem route is logically equivalent to the open theorem itself. -/
theorem universalFailure_to_sat_not_in_p
    (h : UniversalFailure (SATBits circuitBitEncoding)) :
    ¬ InP (SATBits circuitBitEncoding) :=
  universal_failure_implies_not_in_p h

theorem self_theorem_route_exactly_circular :
    UniversalFailure (SATBits circuitBitEncoding) ↔
      ¬ InP (SATBits circuitBitEncoding) :=
  universal_failure_iff_not_in_p

/-- The P02 endpoint is equivalent to the same open content. -/
theorem self_theorem_route_to_p02
    (h : ¬ InP (SATBits circuitBitEncoding)) :
    P02Target :=
  p02_target_iff_sat_not_in_p.mpr h

#print axioms sat_not_in_p_to_universalFailure
#print axioms universalFailure_to_sat_not_in_p
#print axioms self_theorem_route_exactly_circular
#print axioms self_theorem_route_to_p02

end PNPSelfTheoremCircularityAudit20260926
end Real
end MCore
