import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.P01PreservingUnaryReaderCertificate
import MCore.Real.P01FinalCertificate

namespace MCore
namespace Real
namespace P01PreservingUnaryReaderFrontier

open CanonicalFinalProof
open CanonicalCircuitBits
open P01WitnessIndexedRead
open P01PreservingUnaryWitnessMachine
open P01PreservingUnaryReaderCertificate

/-!
Exact material frontier for the universal preserving unary reader.

This file intentionally contains definitions of the remaining proposition
shapes only.  It introduces proposition shapes only and no external closure claim.
-/

/-- One successor unary marker must advance the preserving machine from one
canonical loop configuration to the next while extending the traversed prefix
by exactly the next witness bit. -/
def SuccessorCycleObligation : Prop :=
  ∀ (pref : BitString) (b : Bool) (suffix : BitString) (n : Nat),
    pref ≠ [] →
    preservingUnaryReadMachine.run (4 * pref.length + 8)
        (indexSomeConfig pref (b :: suffix) (n + 1)) =
      indexSomeConfig (pref ++ [b]) suffix n

/-- The terminal target remains the existing universal material contract. -/
def UniversalReaderMaterialTarget : Prop :=
  PreservingUnaryReaderGap

/-- P01 integration may advance only after the universal reader is inhabited. -/
def ReaderBeforeP01Construction : Prop :=
  PreservingUnaryReaderGap → P01FinalCertificate.P01ConstructionGap

end P01PreservingUnaryReaderFrontier
end Real
end MCore
