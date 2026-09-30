import MCore.Real.FinalProof

namespace MCore.Real

/-- FALSIFIED ONLY: exact missing SAT lower-bound certificate injected as an axiom. -/
axiom falsified_satLowerBoundCertificate : SATLowerBoundCertificate

/-- Propagation test: the falsified certificate yields SAT not in P. -/
theorem falsified_SATNotInP : SATNotInP :=
  sat_not_in_p_of_lower_bound_certificate
    falsified_satLowerBoundCertificate

#print axioms MCore.Real.falsified_SATNotInP

end MCore.Real
