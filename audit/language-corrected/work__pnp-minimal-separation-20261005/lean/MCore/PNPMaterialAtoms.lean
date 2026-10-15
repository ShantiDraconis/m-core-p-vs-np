/-!
ATK language audit — provenance-preserving source copy.
Source branch: work/pnp-minimal-separation-20261005
Source path: lean/MCore/PNPMaterialAtoms.lean
Scope: The result concerns the local P01 construction and does not establish the original P versus NP separation.
No theorem statements, proof terms, imports, or axioms are modified by this copy.
This path is an audit artifact, not an installed module in the project's Lean build.
-/

import MCore.Real.P01FinalCertificate
import MCore.Real.FailProofAllGaps
import MCore.Real.CanonicalCircuitBits

namespace MCore

open Real
open Real.CanonicalFinalProof
open Real.CanonicalSATBoundary
open Real.CanonicalCircuitBits
open Real.P01FinalCertificate
open Real.FailProofAllGaps

example : P01MachineConstruction := by
  constructor

example : FailureGenerator (SATBits circuitBitEncoding) := by
  constructor

end MCore
