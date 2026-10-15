/-!
ATK language audit — provenance-preserving source copy.
Source branch: atk-kernel-check
Source path: probe/P01MachineConstructionExpectedFailure.lean
Scope: This file is an intentionally incomplete negative compilation probe. Do not include it in a successful build target or replace the missing proof by an axiom.
No theorem statements, proof terms, imports, or axioms are modified by this copy.
This path is an audit artifact, not an installed module in the project's Lean build.
-/

import MCore.Real.P01FinalCertificate

namespace MCore.Real.P01MaterialProbe

open P01FinalCertificate

/-
EXPECTED FAILURE TARGET.
No P01MachineConstruction inhabitant is supplied.
-/
example : Nonempty P01MachineConstruction := by

end MCore.Real.P01MaterialProbe
