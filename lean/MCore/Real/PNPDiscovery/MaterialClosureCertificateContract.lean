import MCore.Real.PNPDiscovery.ExactOpenMathMinCut

namespace MCore
namespace Real
namespace PNPDiscovery

open P02ExactDiagonalFrontier

/-- Exact schema that a future material certificate must inhabit.
This file intentionally supplies no inhabitant. -/
structure MaterialClosureCertificatePayload where
  satInNP : SATInNPPhysicalGap
  separation : TotalExactDiagonalProducer

theorem materialClosurePayload_closes
    (P : MaterialClosureCertificatePayload) :
    CanonicalFinalProof.PneqNP :=
  exactMaterialMinCut_closes
    { satInNP := P.satInNP
      separation := P.separation }

/-!
When the material theorem is genuinely closed, create
MaterialClosureCertificate.lean with:

def materialClosureCertificate :
    MaterialClosureCertificatePayload := { ... }

theorem materialClosureCertificate_closes :
    CanonicalFinalProof.PneqNP :=
  materialClosurePayload_closes materialClosureCertificate

The fail-closed material gate requires those exact two declarations.
-/

#print axioms MCore.Real.PNPDiscovery.materialClosurePayload_closes

end PNPDiscovery
end Real
end MCore
