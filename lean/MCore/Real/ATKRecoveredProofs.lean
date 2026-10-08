import MCore.Real.P01FinalCertificate
import MCore.Real.FinalProofAttack
import MCore.K10

/-! Recovered existing proofs, compiled as one import surface. This module adds no axioms and makes no terminal promotion. -/
namespace MCore.Real.ATKRecoveredProofs

open MCore.Real.P01FinalCertificate

#check P01MachineConstruction.correctAt
#check construction_closes_p01
#check MCore.separation_witness_separates
#check MCore.Real.FinalProofAttack.current_SATLowerBoundCertificate_refuted

#print axioms MCore.Real.P01FinalCertificate.P01MachineConstruction.correctAt
#print axioms MCore.Real.P01FinalCertificate.construction_closes_p01
#print axioms MCore.separation_witness_separates
#print axioms MCore.Real.FinalProofAttack.current_SATLowerBoundCertificate_refuted

end MCore.Real.ATKRecoveredProofs
