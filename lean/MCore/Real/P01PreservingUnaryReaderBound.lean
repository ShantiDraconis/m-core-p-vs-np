import Mathlib
import MCore.Real.P01PreservingUnaryIteration
import MCore.Real.P01PreservingUnaryFinalRead
import MCore.Real.P01PreservingUnaryRewind
import MCore.Real.P01PreservingUnaryReaderCertificate
import MCore.Real.CanonicalSATWitness

namespace MCore
namespace Real
namespace P01PreservingUnaryReaderBound

open CanonicalFinalProof
open CanonicalCircuitBits
open P01PreservingUnaryIteration
open P01PreservingUnarySuccessorCycle
open P01PreservingUnaryReaderCertificate

/-- Closed form for the exact sum of successor-cycle costs. -/
theorem iteratedCycleFuel_closed
    (pref moved : BitString) :
    iteratedCycleFuel pref moved =
      2 * moved.length ^ 2 +
        (4 * pref.length + 6) * moved.length := by
  induction moved generalizing pref with
  | nil =>
      simp [iteratedCycleFuel, iteratedCycleFuelLen]
  | cons b rest ih =>
      rw [iteratedCycleFuel_cons]
      rw [ih]
      simp [successorCycleFuel]
      ring

/-- Exact total fuel of the nonzero physical reader path, expressed only in
the requested index. -/
def nonzeroReaderFuel (i : Nat) : Nat :=
  2 * i ^ 2 + 12 * i + 5

/-- A deliberately loose quadratic bound in the certificate input size. -/
def preservingUnaryReaderTimeBound : TimeBound :=
  fun n => 20 * (n + 1) ^ 2

theorem preservingUnaryReaderTimeBound_poly :
    PolynomialTimeBound preservingUnaryReaderTimeBound := by
  refine ⟨20, 2, ?_⟩
  intro n
  exact le_rfl

/-- The exact physical nonzero-path accounting collapses to nonzeroReaderFuel. -/
theorem nonzero_physical_fuel_identity
    (i : Nat) (hi : 0 < i) :
    let moved := i - 1
    8 +
      (2 * moved ^ 2 + 10 * moved) +
      (2 * i + 3) +
      (4 * i + 2) =
    nonzeroReaderFuel i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  simp [nonzeroReaderFuel]
  ring

/-- The certificate-size quadratic dominates the zero and nonzero physical
reader costs for every valid witness/index pair. -/
theorem nonzeroReaderFuel_le_timeBound
    (witness : BitString) (i : Nat) :
    nonzeroReaderFuel i ≤
      preservingUnaryReaderTimeBound
        (witness.length + (encodeNat i).length) := by
  simp [nonzeroReaderFuel, preservingUnaryReaderTimeBound,
    CanonicalSATWitness.encodeNat_length]
  nlinarith [Nat.zero_le witness.length, Nat.zero_le i]

theorem zeroFuel_le_timeBound
    (witness : BitString) :
    5 ≤ preservingUnaryReaderTimeBound
      (witness.length + (encodeNat 0).length) := by
  simp [preservingUnaryReaderTimeBound,
    CanonicalSATWitness.encodeNat_length]

#print axioms MCore.Real.P01PreservingUnaryReaderBound.iteratedCycleFuel_closed
#print axioms MCore.Real.P01PreservingUnaryReaderBound.preservingUnaryReaderTimeBound_poly
#print axioms MCore.Real.P01PreservingUnaryReaderBound.nonzeroReaderFuel_le_timeBound

end P01PreservingUnaryReaderBound
end Real
end MCore
