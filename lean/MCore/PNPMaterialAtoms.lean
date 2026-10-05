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
