import MCore.Real.CanonicalFinalProof
import MCore.Real.P02TerminalFrontier

namespace MCore.Real.PNPDirectFrontier20260926

open CanonicalFinalProof
open CanonicalCircuitBits
open P02TerminalFrontier

def Frontier : Prop :=
  UniversalFailure (SATBits circuitBitEncoding)

theorem frontier_equiv :
    Frontier ↔ ¬ InP (SATBits circuitBitEncoding) :=
  universal_failure_iff_not_in_p

theorem frontier_to_p02
    (h : Frontier) :
    P02Target := by
  exact p02_target_iff_sat_not_in_p.mpr
    (frontier_equiv.mp h)

#print axioms frontier_equiv
#print axioms frontier_to_p02

end MCore.Real.PNPDirectFrontier20260926
