import MCore.Real.P06_BSD.SourceBinding

namespace MCore.Real.P06_BSD.ClosedBase.NoFalseFinalCertificate

open P06_BSD.SourceBinding

def evidence : SourceEvidence :=
  { name := "NoFalseFinalCertificate"
    kind := .closedBase
    sourceRepo := canonicalBSDRepo
    sourceRef := canonicalMainRef
    sourcePath := "lean/MCore/K14.lean"
    theoremName := "k14_no_false_final_certificate / k14_chain_preserves_open_core"
    semanticScope := "Closed fail-closed audit: K11-K13 remain openBridge and K14 cannot manufacture a final proof certificate."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P06_BSD.ClosedBase.NoFalseFinalCertificate.evidence_is_source_verified

end MCore.Real.P06_BSD.ClosedBase.NoFalseFinalCertificate
