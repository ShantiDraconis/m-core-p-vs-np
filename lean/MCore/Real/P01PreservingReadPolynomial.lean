import MCore.Real.P01WitnessIndexedReadPreserving

namespace MCore
namespace Real
namespace P01WitnessIndexedReadPreserving

open CanonicalFinalProof

/-- Closed form for the exact preserving-reader fuel from an already moved
prefix.  This exposes the quadratic cost directly instead of leaving it hidden
behind the recursive operational definition. -/
theorem preservingMovedFuel_closed
    (m n : Nat) :
    preservingMovedFuel m n =
      4 * m * n + 5 * m + 2 * n ^ 2 + 9 * n + 6 := by
  induction n generalizing m with
  | zero =>
      simp [preservingMovedFuel]
  | succ n ih =>
      rw [preservingMovedFuel]
      rw [ih (m + 1)]
      ring

/-- Closed form for every positive unary index. -/
theorem preservingReadFuel_succ_closed
    (n : Nat) :
    preservingReadFuel (n + 1) =
      2 * (n + 1) ^ 2 + 9 * (n + 1) + 6 := by
  rw [show preservingReadFuel (n + 1) =
      6 + preservingMovedFuel 1 n by rfl]
  rw [preservingMovedFuel_closed]
  ring

/-- A simple quadratic envelope for the exact preserving-reader fuel. -/
theorem preservingReadFuel_le_quadratic
    (i : Nat) :
    preservingReadFuel i ≤ 17 * (i + 1) ^ 2 := by
  cases i with
  | zero =>
      simp [preservingReadFuel]
  | succ n =>
      rw [preservingReadFuel_succ_closed]
      nlinarith [Nat.zero_le n]

/-- The already-kernelized universal preserving reader is polynomial-time in
the unary index length. -/
theorem preservingReadFuel_poly :
    PolynomialTimeBound preservingReadFuel := by
  exact ⟨17, 2, preservingReadFuel_le_quadratic⟩

#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingMovedFuel_closed
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingReadFuel_succ_closed
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingReadFuel_le_quadratic
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingReadFuel_poly

end P01WitnessIndexedReadPreserving
end Real
end MCore
