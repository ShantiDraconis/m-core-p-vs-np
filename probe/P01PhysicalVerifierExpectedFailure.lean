import MCore.Real.P01FullVerifierPhysical

namespace MCore.Real.P01PhysicalVerifierMaterialProbe

open P01FullVerifierPhysical

/-
EXPECTED FAILURE TARGET.
All local physical primitives may be reused, but no global fixed TM,
halting theorem, or physical_eq_logical theorem is supplied here.
-/
example : Nonempty PhysicalVerifierRealization := by

end MCore.Real.P01PhysicalVerifierMaterialProbe
