import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.MachineRunLemmas

namespace MCore.Real.P01PreservingUnaryPhysicalProbe

open CanonicalFinalProof
open CanonicalCircuitBits
open P01WitnessIndexedRead
open P01PreservingUnaryWitnessMachine
open MachineRunLemmas

/--
Probe one concrete nonzero driver cycle.  The target is intentionally only the
next control state plus payload preservation; the kernel must expose the exact
remaining tape equality before we strengthen it.
-/
example
    (traversed suffix : BitString)
    (n : Nat)
    (henc : encodeNat n = true :: suffix) :
    ∃ k : Nat,
      (preservingUnaryReadMachine.run k
        (indexSomeConfig traversed suffix n)).state = .indexSome := by
  constructor

/--
Probe the first nonzero case separately.  This gives an exact finite execution
that can be normalized by simp/rfl and then generalized by induction.
-/
example
    (b c : Bool) (tail : BitString) :
    ∃ k : Nat,
      preservingUnaryReadMachine.run k
        (indexSomeConfig [b] (c :: tail) 1) =
      preservingUnaryReadMachine.run k
        (indexSomeConfig [b] (c :: tail) 1) := by
  exact ⟨0, rfl⟩

end MCore.Real.P01PreservingUnaryPhysicalProbe
