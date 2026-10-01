import MCore.Real.P02RecoveredTableauKernel

namespace MCore
namespace Real
namespace P02TableauCompletenessFrontier

open CanonicalFinalProof
open P02BoundedComputationEncoding
open P02BoundedComputationClose
open P02RecoveredTableauKernel

/-- Exact residual of the recovered A1 tableau: the concrete execution assignment
must satisfy every transition clause. Initial and final clauses are already proved. -/
def ExecutionTransitionsComplete : Prop :=
  ∀ (M : PolyDTMCandidate) (x : BitString) (t : Nat),
    evalCNF (executionAssignment M x t)
      (transitionsCNF M x t) = true

/-- Once transition completeness is supplied, the already-defined concrete
execution assignment yields the full tableau completeness certificate. -/
def tableauCompletenessCertificateOfTransitions
    (hTransitions : ExecutionTransitionsComplete) :
    TableauCompletenessCertificate where
  assignment := fun M x t _ => executionAssignment M x t
  satisfies := by
    intro M x t hacc
    unfold boundedExecTableauCNF
    rw [evalCNF_append_eq, evalCNF_append_eq]
    have hInit :
        evalCNF (executionAssignment M x t) (initialCNF M x t) = true :=
      executionAssignment_initialCNF M x t
    have hTrans :
        evalCNF (executionAssignment M x t) (transitionsCNF M x t) = true :=
      hTransitions M x t
    have hFinal :
        evalCNF (executionAssignment M x t) (finalAcceptanceCNF M t) = true :=
      executionAssignment_finalAcceptanceCNF M x t hacc
    simp [hInit, hTrans, hFinal]

theorem transitionsComplete_closes_boundedExec
    (hTransitions : ExecutionTransitionsComplete) :
    BoundedExecCorrectness :=
  boundedExecCorrectness_of_tableauCompleteness
    (tableauCompletenessCertificateOfTransitions hTransitions)

/-- Exact recovered-A1 status: only transition-clause completeness remains. -/
def RECOVERED_A1_OPEN_MATH : Prop :=
  ExecutionTransitionsComplete

end P02TableauCompletenessFrontier
end Real
end MCore
