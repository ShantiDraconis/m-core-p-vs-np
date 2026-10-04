import MCore.Real.PNPDiscovery.NormalizedUniversalPrerequisites
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open CanonicalCircuitBits

/-- Concrete self-delimiting pairing: unary code length, then code, then input. -/
def concretePack
    (code x : BitString) : BitString :=
  encodeNat code.length ++ code ++ x

def concreteUnpack
    (bits : BitString) :
    Option (BitString × BitString) := do
  let (k, rest) ← decodeNat bits
  if hk : k ≤ rest.length then
    some (rest.take k, rest.drop k)
  else
    none

theorem concreteUnpack_pack
    (code x : BitString) :
    concreteUnpack (concretePack code x) =
      some (code, x) := by
  unfold concretePack concreteUnpack
  rw [List.append_assoc]
  rw [decodeNat_encodeNat_append]
  have hk : code.length ≤ (code ++ x).length := by simp
  simp only [dif_pos hk]
  rw [List.take_left]
  rw [List.drop_left]
  rfl

def concreteMachineInputPairing :
    MachineInputPairing :=
  { pack := concretePack
    unpack := concreteUnpack
    roundTrip := concreteUnpack_pack }

/-- Exact size formula for paired machine-code/input data. -/
theorem concretePack_length
    (code x : BitString) :
    (concretePack code x).length =
      2 * code.length + x.length + 1 := by
  unfold concretePack
  rw [List.length_append, List.length_append]
  rw [encodeNat_length]
  omega

/-- Pairing overhead is linear and fully closed. -/
theorem concretePack_linear
    (code x : BitString) :
    (concretePack code x).length ≤
      2 * (code.length + x.length + 1) := by
  rw [concretePack_length]
  omega

#print axioms MCore.Real.PNPDiscovery.concreteUnpack_pack
#print axioms MCore.Real.PNPDiscovery.concretePack_length
#print axioms MCore.Real.PNPDiscovery.concretePack_linear

end PNPDiscovery
end Real
end MCore
