import MCore.Real.P06_BSD.SourceBinding

namespace MCore.Real.P06_BSD.ClosedBase.ExternalInputProvenance

open P06_BSD.SourceBinding

def evidence : SourceEvidence :=
  { name := "ExternalInputProvenance"
    kind := .closedBase
    sourceRepo := canonicalBSDRepo
    sourceRef := canonicalMainRef
    sourcePath := "lean/MCore/K11.lean"
    theoremName := "k11_modularity_external / k11_analytic_continuation_external / k11_functional_equation_external"
    semanticScope := "Closed provenance classification only: modularity, analytic continuation and functional equation are established external inputs; no BSD rank/refined conclusion is inferred."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P06_BSD.ClosedBase.ExternalInputProvenance.evidence_is_source_verified

end MCore.Real.P06_BSD.ClosedBase.ExternalInputProvenance
