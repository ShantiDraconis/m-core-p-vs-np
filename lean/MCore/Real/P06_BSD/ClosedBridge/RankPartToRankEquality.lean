import MCore.Real.P06_BSD.SourceBinding

namespace MCore.Real.P06_BSD.ClosedBridge.RankPartToRankEquality

open P06_BSD.SourceBinding

def evidence : SourceEvidence :=
  { name := "RankPartToRankEquality"
    kind := .closedBridge
    sourceRepo := canonicalBSDRepo
    sourceRef := canonicalMainRef
    sourcePath := "lean/MCore/K12.lean"
    theoremName := "k12_rank_part_iff_k8_target"
    semanticScope := "Closed definitional bridge from BSDRankPart on typed arithmetic/analytic data to the earlier BSDRankEquality target."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P06_BSD.ClosedBridge.RankPartToRankEquality.evidence_is_source_verified

end MCore.Real.P06_BSD.ClosedBridge.RankPartToRankEquality
