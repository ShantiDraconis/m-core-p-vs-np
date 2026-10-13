import MCore.Real.PNPAfterP01

/-! Auditoria: tipos exatos (falha de elaboração se divergirem) + axiomas. -/

example : MCore.Real.CanonicalFinalProof.InNP
    (MCore.Real.CanonicalSATBoundary.SATBits MCore.Real.CanonicalCircuitBits.circuitBitEncoding) :=
  MCore.Real.PNPAfterP01.sat_in_np

example : MCore.Real.CanonicalFinalProof.UniversalFailure
    (MCore.Real.CanonicalSATBoundary.SATBits MCore.Real.CanonicalCircuitBits.circuitBitEncoding) →
    MCore.Real.CanonicalFinalProof.PneqNP :=
  MCore.Real.PNPAfterP01.pneqnp_of_universal_failure

#print axioms MCore.Real.PNPAfterP01.sat_in_np
#print axioms MCore.Real.PNPAfterP01.pneqnp_of_universal_failure
#print axioms MCore.Real.PNPAfterP01.pneqnp_of_sat_not_in_p
#print axioms MCore.Real.PNPAfterP01.sat_in_p_iff_no_failure
