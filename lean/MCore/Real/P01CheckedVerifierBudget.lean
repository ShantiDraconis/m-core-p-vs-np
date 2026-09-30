import MCore.Real.P01EvalStepSemanticRefinement
import MCore.Real.P01InputNodeCompositeRun
import MCore.Real.P01EncodedStackEvaluator

namespace MCore
namespace Real
namespace P01CheckedVerifierBudget

open CanonicalFinalProof
open CanonicalCircuitBits
open P01NeedExprCompositeRun
open P01InputNodeCompositeRun

/-- Exact unary length of the canonical natural-number payload. -/
theorem encodeNat_length (i : Nat) :
    (encodeNat i).length = i + 1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [encodeNat, ih, Nat.succ_eq_add_one]
      omega

/-- Uniform physical cost of one semantic evaluator transition when every
dynamic tape component is bounded by the original source length. -/
def checkedStepEnvelope (n : Nat) : Nat :=
  64 * (n + 1) ^ 2

theorem checkedStepEnvelope_poly :
    PolynomialTimeBound checkedStepEnvelope := by
  refine ⟨64, 2, ?_⟩
  intro n
  exact Nat.le_refl _

theorem constTagCompositeFuel_le_envelope
    (n : Nat) (frameStack rest : BitString)
    (hf : frameStack.length ≤ n)
    (hr : rest.length ≤ n) :
    constTagCompositeFuel frameStack rest ≤ checkedStepEnvelope n := by
  unfold constTagCompositeFuel checkedStepEnvelope
  have hlin :
      2 * frameStack.length + 2 * rest.length + 14 ≤ 4 * n + 14 := by
    omega
  have hquad : 4 * n + 14 ≤ 64 * (n + 1) ^ 2 := by
    nlinarith
  omega

theorem pushTagCompositeFuel_le_envelope
    (n : Nat) (frameStack rest : BitString)
    (hf : frameStack.length ≤ n)
    (hr : rest.length ≤ n) :
    pushTagCompositeFuel frameStack rest ≤ checkedStepEnvelope n := by
  unfold pushTagCompositeFuel checkedStepEnvelope
  have hlin :
      2 * frameStack.length + 2 * rest.length + 18 ≤ 4 * n + 18 := by
    omega
  have hquad : 4 * n + 18 ≤ 64 * (n + 1) ^ 2 := by
    nlinarith
  omega

/-- The complete 000 input primitive is also uniformly quadratic. -/
theorem inputNodeCompositeFuel_le_envelope
    (n consumed i : Nat)
    (tail frameStack : BitString)
    (hc : consumed ≤ n)
    (hi : i ≤ n)
    (ht : tail.length ≤ n)
    (hf : frameStack.length ≤ n) :
    inputNodeCompositeFuel consumed i tail frameStack ≤
      checkedStepEnvelope n := by
  have hbase :=
    inputNodeCompositeFuel_le consumed i tail frameStack
  have hcoef :
      2 * consumed + 4 * (i + 1) + 6 ≤ 6 * n + 10 := by
    omega
  have hmul :
      (2 * consumed + 4 * (i + 1) + 6) * i ≤
        (6 * n + 10) * n :=
    Nat.mul_le_mul hcoef hi
  have hrest :
      4 * consumed + 8 * i + tail.length + frameStack.length + 30 ≤
        14 * n + 30 := by
    omega
  have hpoly :
      (6 * n + 10) * n + (14 * n + 30) ≤
        64 * (n + 1) ^ 2 := by
    nlinarith
  unfold checkedStepEnvelope
  omega

theorem inputTagCompositeFuel_le_envelope
    (n consumed i : Nat)
    (tail frameStack : BitString)
    (hc : consumed ≤ n)
    (hi : i ≤ n)
    (ht : tail.length ≤ n)
    (hf : frameStack.length ≤ n) :
    inputTagCompositeFuel consumed i tail frameStack ≤
      checkedStepEnvelope n := by
  have hnode :=
    inputNodeCompositeFuel_le_envelope
      n (consumed + 3) i tail frameStack
      (by omega) hi ht hf
  have henc : (encodeNat i).length = i + 1 :=
    encodeNat_length i
  unfold inputTagCompositeFuel checkedStepEnvelope at *
  rw [List.length_append, henc]
  simp only [List.length_cons, List.length_nil, Nat.zero_add]
  have hpref :
      frameStack.length +
          (false :: false :: false :: (encodeNat i ++ tail)).length + 3 +
          1 + 3 + 1 ≤
        3 * n + 12 := by
    rw [List.length_cons, List.length_cons, List.length_cons,
      List.length_append, henc]
    omega
  have hpoly :
      3 * n + 12 + 64 * (n + 1) ^ 2 ≤
        128 * (n + 1) ^ 2 := by
    nlinarith
  -- The input path needs a slightly larger common envelope than the non-input
  -- tags; expose it explicitly rather than hiding the constant.
  omega

/-- Global candidate budget for the checked physical verifier.  The cubic
degree is enough for a linear number of semantic steps, each under a quadratic
physical envelope. -/
def checkedVerifierTimeBound : TimeBound :=
  fun n => 256 * (n + 1) ^ 3

theorem checkedVerifierTimeBound_poly :
    PolynomialTimeBound checkedVerifierTimeBound := by
  refine ⟨256, 3, ?_⟩
  intro n
  exact Nat.le_refl _

#print axioms MCore.Real.P01CheckedVerifierBudget.encodeNat_length
#print axioms MCore.Real.P01CheckedVerifierBudget.constTagCompositeFuel_le_envelope
#print axioms MCore.Real.P01CheckedVerifierBudget.pushTagCompositeFuel_le_envelope
#print axioms MCore.Real.P01CheckedVerifierBudget.inputNodeCompositeFuel_le_envelope
#print axioms MCore.Real.P01CheckedVerifierBudget.inputTagCompositeFuel_le_envelope
#print axioms MCore.Real.P01CheckedVerifierBudget.checkedVerifierTimeBound_poly

end P01CheckedVerifierBudget
end Real
end MCore
