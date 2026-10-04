import MCore.Real.PNPDiscovery.FiniteCandidateDescription

namespace MCore
namespace Real
namespace PNPDiscovery

/-- Ask the kernel/typeclass system whether the finite normalized description
is already encodable from its component instances. -/
#synth Encodable FiniteCandidateDescription

/-- If the instance exists, its canonical encode/decode laws give an immediate
abstract Gödel numbering.  This file deliberately contains no endpoint
mathematics; it only tests existing library infrastructure. -/
noncomputable def libraryFiniteDescriptionEncode
    (D : FiniteCandidateDescription) : Nat :=
  Encodable.encode D

noncomputable def libraryFiniteDescriptionDecode
    (n : Nat) : Option FiniteCandidateDescription :=
  Encodable.decode FiniteCandidateDescription n

theorem libraryFiniteDescription_roundTrip
    (D : FiniteCandidateDescription) :
    libraryFiniteDescriptionDecode
        (libraryFiniteDescriptionEncode D) =
      some D := by
  exact Encodable.encodek D

#print axioms MCore.Real.PNPDiscovery.libraryFiniteDescription_roundTrip

end PNPDiscovery
end Real
end MCore
