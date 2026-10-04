import MCore.Real.PNPDiscovery.FiniteCandidateGodelWords
import MCore.Real.PNPDiscovery.FiniteDescriptionInjectivity
import MCore.Real.PNPDiscovery.NormalizedUniversalPrerequisites
import MCore.Real.PNPDiscovery.ConcreteMachineInputPairing

namespace MCore
namespace Real
namespace PNPDiscovery
namespace KernelTestGodelLayer

/-- Word layout length must remain exact. -/
example (D : FiniteCandidateDescription) :
    (finiteDescriptionWords D).length =
      4 + (D.stateCount + 1) * 9 +
        2 * (D.stateCount + 1) :=
  finiteDescriptionWords_length D

/-- Outer unary serialization must recover the exact word vector. -/
example (D : FiniteCandidateDescription) :
    decodeNatList (encodeFiniteDescription D) =
      some (finiteDescriptionWords D, []) :=
  decodeFiniteDescriptionWords_roundTrip D

/-- The remaining decoder atom is exactly finite dependent-table extensionality. -/
#check DependentFiniteTableExtensionality
#check dependentExtensionality_closes_reconstructor
#check NormalizedCandidateCodebook
#check NormalizedUniversalSimulator
#check NormalizedUniversalOverhead
#check NormalizedSelfReferenceCompiler

/-- Pairing size is exact and linear. -/
example (code x : BitString) :
    (concretePack code x).length =
      2 * code.length + x.length + 1 :=
  concretePack_length code x

#print axioms MCore.Real.PNPDiscovery.finiteDescriptionWords_length
#print axioms MCore.Real.PNPDiscovery.decodeFiniteDescriptionWords_roundTrip
#print axioms MCore.Real.PNPDiscovery.dependentExtensionality_closes_reconstructor
#print axioms MCore.Real.PNPDiscovery.concretePack_length

end KernelTestGodelLayer
end PNPDiscovery
end Real
end MCore
