import MCore.K10
import MCore.Real.FinalProofAttack

namespace MCore

/-!
The former checks `hard_PvsNP_SAT_operational_forward` and
`hard_PvsNP_SAT_not_in_P_backward` referenced declarations that do not
exist in this repository.  These are the actual available statements.
The K10 implication requires a supplied witness; it does not produce one.
The arbitrary-encoder SAT model is refuted, not a proof of SAT outside P.
-/

#check MCore.separation_witness_not_in_P
#check MCore.separation_witness_separates
#check MCore.k10_open_obligation
#check MCore.Real.FinalProofAttack.current_SATNotInP_refuted

end MCore
