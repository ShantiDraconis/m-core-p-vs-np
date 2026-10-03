import MCore.Real.P03.Architecture

namespace MCore.Real.P03.ArchitectureAudit

#print axioms MCore.Real.P03.ClosedBase.C2I.closed_c2i
#print axioms MCore.Real.P03.ClosedBase.R2I.closed_r2i
#print axioms MCore.Real.P03.ClosedBase.PhiC.closed_phi_equivariance
#print axioms MCore.Real.P03.ClosedBase.SPlus.splus_eq_zero_iff
#print axioms MCore.Real.P03.ClosedBase.SMinus.sminus_eq_zero_iff
#print axioms MCore.Real.P03.ClosedBase.Nabla2.hessian_entries
#print axioms MCore.Real.P03.ClosedBase.Nabla2.rank_one_outer_product

#print axioms MCore.Real.P03.ClosedBridge.ComplementReduce.closed_complement_reduce
#print axioms MCore.Real.P03.ClosedBridge.Dichotomy.closed_existsPerfectFlip_iff_not_rangeFailureLaw
#print axioms MCore.Real.P03.ClosedBridge.Dichotomy.closed_global_dichotomy
#print axioms MCore.Real.P03.ClosedBridge.OddAntiRec.closed_perfectFlip_odd_anti_recurrence
#print axioms MCore.Real.P03.ClosedBridge.Transport.closed_fullRun_to_internal_endpoint
#print axioms MCore.Real.P03.ClosedBridge.Transport.closed_rangeFailure_to_internal_endpoint

#print axioms MCore.Real.P03.OpenBridge.BoundedCandidate.genuine
#print axioms MCore.Real.P03.OpenBridge.SourceLen.source_len_bound
#print axioms MCore.Real.P03.OpenBridge.UniformDecoder.pointwise_closed

#print axioms MCore.Real.P03.Architecture.closed_base_count
#print axioms MCore.Real.P03.Architecture.closed_bridge_count
#print axioms MCore.Real.P03.Architecture.unique_open_bridge_count
#print axioms MCore.Real.P03.Architecture.open_math_count
#print axioms MCore.Real.P03.Architecture.architecture_green_false
#print axioms MCore.Real.P03.Architecture.architecture_build_unverified

end MCore.Real.P03.ArchitectureAudit
