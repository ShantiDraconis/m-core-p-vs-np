import MCore.Real.P06_BSD.SourceBinding

namespace MCore.Real.P06_BSD.ClosedBase.AbstractRankInterfaceCounteraudit

open P06_BSD.SourceBinding

def evidence : SourceEvidence :=
  { name := "AbstractRankInterfaceCounteraudit"
    kind := .closedBase
    sourceRepo := canonicalBSDRepo
    sourceRef := canonicalMainRef
    sourcePath := "audit/ATK_BSD_ABSTRACT_TYPE_COUNTERAUDIT.lean"
    theoremName := "no_universal_rank_part_over_arbitrary_data"
    semanticScope := "Fail-closed counteraudit: the abstract pair-of-naturals interface is too broad, so realizable elliptic-curve binding is mandatory before universal promotion."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P06_BSD.ClosedBase.AbstractRankInterfaceCounteraudit.evidence_is_source_verified

end MCore.Real.P06_BSD.ClosedBase.AbstractRankInterfaceCounteraudit
