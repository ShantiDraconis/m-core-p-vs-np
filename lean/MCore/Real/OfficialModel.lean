import MCore.Real.CanonicalFinalProof

namespace MCore
namespace Real
namespace OfficialModel

open CanonicalFinalProof

/-- External complexity-model contract.

The witness types are intentionally external to the hardened internal
PolyDTM/PolyNTM realizations.  A concrete external/official model must provide
these witness types together with a nonempty bibliographic/formal reference.
This file does not identify the external model with the internal one. -/
structure OfficialComplexityModel where
  PRealization : BitLanguage → Type
  NPRealization : BitLanguage → Type
  reference : String
  reference_nonempty : reference ≠ ""

def OfficialComplexityModel.P
    (M : OfficialComplexityModel) :
    BitLanguage → Prop :=
  fun L => Nonempty (M.PRealization L)

def OfficialComplexityModel.NP
    (M : OfficialComplexityModel) :
    BitLanguage → Prop :=
  fun L => Nonempty (M.NPRealization L)

/-- A model is externally selected only when an actual reference-bearing model
value is supplied.  No default value is manufactured here. -/
def OfficialModelSelected : Prop :=
  Nonempty OfficialComplexityModel

end OfficialModel
end Real
end MCore
