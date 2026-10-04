import MCore.Real.PNPDiscovery.ExactOpenMathMinCut
import MCore.Real.PNPDiscovery.NormalizedUniversalPrerequisites
import MCore.Real.PNPDiscovery.TransitionShapeFrontier
import MCore.Real.PNPDiscovery.FiniteDescriptionInjectivity

namespace MCore
namespace Real
namespace PNPDiscovery
namespace KernelTestOpenFrontier

/-- These checks intentionally do NOT inhabit the propositions.
They pin the names/types of every currently legitimate open atom. -/
#check SATInNPPhysicalGap
#check ExactSeparationOpenAtom
#check P02ExactDiagonalFrontier.TotalExactDiagonalProducer
#check DependentFiniteTableExtensionality
#check EqualRadiusTransitionShapeGap
#check NormalizedUniversalInfrastructureGap
#check NormalizedSelfReferenceCompilerGap
#check CurrentSelfReferencePrerequisitesGap

/-- Endpoint identity regression: no weaker alias may silently replace it. -/
example :
    ExactSeparationOpenAtom ↔ SATSeparationGap :=
  exactSeparationOpenAtom_iff_endpoint

/-- Method infrastructure remains only a route into the material atom. -/
#check NormalizedInfrastructureSemanticClosure
#check LayoutRouteMechanicalOpenAtom

#print axioms MCore.Real.PNPDiscovery.exactSeparationOpenAtom_iff_endpoint

end KernelTestOpenFrontier
end PNPDiscovery
end Real
end MCore
