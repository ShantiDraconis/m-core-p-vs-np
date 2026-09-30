import MCore.Real.P01CheckedEvalRunBoundedCertificate

namespace MCore
namespace Real
namespace P01BoundedOperatorBudget

open P01EncodedStackEvaluator
open P01CheckedVerifierGlobalBudget
open P01CheckedEvalRunBoundedCertificate

/--
The bounded circuit budget has enough slack for the physical NOT wrapper:
root tag, recursively bounded child, return frame, and final normalization.
-/
theorem not_budget_absorbs
    (child : CircuitK1.Circuit)
    (n : Nat) :
    checkedLoopStepEnvelope n +
        checkedCircuitBudget child n +
        checkedLoopStepEnvelope n +
        checkedLoopStepEnvelope n ≤
      checkedCircuitBudget (.not child) n := by
  have hcoef :
      8 * (evalStepCount child + 1) + 3 ≤
        8 * (evalStepCount (.not child) + 1) := by
    simp [evalStepCount]
    omega
  have hmul :=
    Nat.mul_le_mul_right (checkedLoopStepEnvelope n) hcoef
  simpa [checkedCircuitBudget, Nat.add_mul] using hmul

/--
A binary circuit budget absorbs all wrapper costs around two recursively
bounded children.  The four common envelopes account for the root tag, the
left-to-right continuation, the right return, and final normalization.
-/
theorem binary_budget_absorbs
    (left right : CircuitK1.Circuit)
    (n : Nat) :
    checkedLoopStepEnvelope n +
        checkedCircuitBudget left n +
        checkedLoopStepEnvelope n +
        checkedCircuitBudget right n +
        checkedLoopStepEnvelope n +
        checkedLoopStepEnvelope n ≤
      8 * (evalStepCount left + evalStepCount right + 4) *
        checkedLoopStepEnvelope n := by
  let E := checkedLoopStepEnvelope n
  let a := evalStepCount left
  let b := evalStepCount right
  have hcoef :
      8 * (a + 1) + 8 * (b + 1) + 4 ≤
        8 * (a + b + 4) := by
    omega
  have hmul :
      (8 * (a + 1) + 8 * (b + 1) + 4) * E ≤
        (8 * (a + b + 4)) * E :=
    Nat.mul_le_mul_right E hcoef
  change
    E + (8 * (a + 1) * E) + E +
        (8 * (b + 1) * E) + E + E ≤
      8 * (a + b + 4) * E
  have hshape :
      E + (8 * (a + 1) * E) + E +
          (8 * (b + 1) * E) + E + E =
        (8 * (a + 1) + 8 * (b + 1) + 4) * E := by
    calc
      E + (8 * (a + 1) * E) + E +
            (8 * (b + 1) * E) + E + E
          =
        (8 * (a + 1) * E) +
          (8 * (b + 1) * E) + (E + E + E + E) := by omega
      _ =
        (8 * (a + 1) * E) +
          (8 * (b + 1) * E) + 4 * E := by omega
      _ =
        (8 * (a + 1) + 8 * (b + 1) + 4) * E := by
          simp [Nat.add_mul, Nat.mul_assoc]
  exact hshape.trans_le hmul

/-- Specialized AND budget closure. -/
theorem and_budget_absorbs
    (left right : CircuitK1.Circuit)
    (n : Nat) :
    checkedLoopStepEnvelope n +
        checkedCircuitBudget left n +
        checkedLoopStepEnvelope n +
        checkedCircuitBudget right n +
        checkedLoopStepEnvelope n +
        checkedLoopStepEnvelope n ≤
      checkedCircuitBudget (.and left right) n := by
  have h := binary_budget_absorbs left right n
  simpa [checkedCircuitBudget, evalStepCount, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using h

/-- Specialized OR budget closure. -/
theorem or_budget_absorbs
    (left right : CircuitK1.Circuit)
    (n : Nat) :
    checkedLoopStepEnvelope n +
        checkedCircuitBudget left n +
        checkedLoopStepEnvelope n +
        checkedCircuitBudget right n +
        checkedLoopStepEnvelope n +
        checkedLoopStepEnvelope n ≤
      checkedCircuitBudget (.or left right) n := by
  have h := binary_budget_absorbs left right n
  simpa [checkedCircuitBudget, evalStepCount, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using h

#print axioms MCore.Real.P01BoundedOperatorBudget.not_budget_absorbs
#print axioms MCore.Real.P01BoundedOperatorBudget.binary_budget_absorbs
#print axioms MCore.Real.P01BoundedOperatorBudget.and_budget_absorbs
#print axioms MCore.Real.P01BoundedOperatorBudget.or_budget_absorbs

end P01BoundedOperatorBudget
end Real
end MCore
