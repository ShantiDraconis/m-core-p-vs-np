import MCore.Real.P01RawTotalContract
import MCore.Real.P01RawDecodeFailureCases
import MCore.Real.P01RawMalformedTag
import MCore.Real.P01RawMalformedUnary
import MCore.Real.P01CheckedEvalRunTagPrefix
import MCore.Real.P01CheckedVerifierBudget
import MCore.Real.P01CheckedVerifierGlobalBudget

namespace MCore
namespace Real
namespace P01RawMalformedBaseProducer

open CanonicalFinalProof
open CanonicalCircuitBits
open P01CNFMode
open P01EvalCursorMachine
open P01NeedExprTagDecode
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunTagPrefix
open P01CheckedVerifierInvariant
open P01CheckedVerifierBudget
open P01CheckedVerifierGlobalBudget
open P01RawTotalContract
open P01RawDecodeFailureCases
open P01RawMalformedTag
open P01RawMalformedUnary

abbrev EvalConfig :=
  Configuration CheckedEvalRunState (Option Bool)

theorem loopEnvelope_le_rawMalformedBudget
    (fuel n : Nat) :
    checkedLoopStepEnvelope n ≤ rawMalformedBudget fuel n := by
  unfold rawMalformedBudget
  have hcoef : 1 ≤ 256 * (fuel + 1) ^ 2 := by
    have hp : 1 ≤ (fuel + 1) ^ 2 := by
      have h1 : 1 ≤ fuel + 1 := by omega
      exact Nat.one_le_pow_of_one_le h1
    exact Nat.le_trans hp (Nat.le_mul_of_pos_left _ (by decide))
  calc
    checkedLoopStepEnvelope n =
        1 * checkedLoopStepEnvelope n := by simp
    _ ≤ (256 * (fuel + 1) ^ 2) * checkedLoopStepEnvelope n :=
      Nat.mul_le_mul_right _ hcoef
    _ = rawMalformedBudget fuel n := by
      unfold rawMalformedBudget
      ring

theorem two_loopEnvelope_le_rawMalformedBudget
    (fuel n : Nat) :
    2 * checkedLoopStepEnvelope n ≤ rawMalformedBudget fuel n := by
  unfold rawMalformedBudget
  have hcoef : 2 ≤ 256 * (fuel + 1) ^ 2 := by
    have hp : 1 ≤ (fuel + 1) ^ 2 := by
      have h1 : 1 ≤ fuel + 1 := by omega
      exact Nat.one_le_pow_of_one_le h1
    have h256 : 256 ≤ 256 * (fuel + 1) ^ 2 :=
      Nat.mul_le_mul_left 256 hp
    omega
  calc
    2 * checkedLoopStepEnvelope n
        ≤ (256 * (fuel + 1) ^ 2) * checkedLoopStepEnvelope n :=
      Nat.mul_le_mul_right _ hcoef
    _ = rawMalformedBudget fuel n := by
      unfold rawMalformedBudget
      ring

theorem n_le_loopEnvelope (n : Nat) :
    n ≤ checkedLoopStepEnvelope n := by
  unfold checkedLoopStepEnvelope
  have hsq : n ≤ (n + 1) ^ 2 := by
    have h1 : n ≤ n + 1 := by omega
    have h2 : n + 1 ≤ (n + 1) ^ 2 := by
      calc
        n + 1 = (n + 1) * 1 := by simp
        _ ≤ (n + 1) * (n + 1) :=
          Nat.mul_le_mul_left (n + 1) (by omega)
        _ = (n + 1) ^ 2 := by ring
    exact Nat.le_trans h1 h2
  have hcoef :
      (n + 1) ^ 2 ≤ 256 * (n + 1) ^ 2 := by
    exact Nat.le_mul_of_pos_left _ (by decide)
  exact Nat.le_trans hsq hcoef

theorem frame_length_le_of_layout
    {n consumed : Nat}
    {bits frameStack : BitString}
    (h : CheckedLayoutBound n consumed bits frameStack) :
    frameStack.length ≤ n :=
  h.frames_le

theorem source_length_le_of_layout
    {n consumed : Nat}
    {bits frameStack : BitString}
    (h : CheckedLayoutBound n consumed bits frameStack) :
    bits.length ≤ n :=
  h.source_le

/-- Short-tag structural failure reaches an honest active dead state. -/
theorem short_reaches_fail_closed
    (witness bits frameStack : BitString)
    (mode : SyntaxMode)
    (consumed padding n fuel : Nat)
    (hshort : bits.length < 3)
    (hLayout : CheckedLayoutBound n consumed bits frameStack) :
    ∃ m ≤ rawMalformedBudget fuel n, ∃ cfg : EvalConfig,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               bits frameStack padding }] ∧
      EvalFailClosed cfg := by
  obtain ⟨m, hm, dead, hmem, hactive, hdead⟩ :=
    checked_truncated_tag_reaches_dead
      mode witness bits frameStack consumed padding hshort
  have hsrc := source_length_le_of_layout hLayout
  have hfrm := frame_length_le_of_layout hLayout
  have hpref :
      checkedTagPrefixFuel bits frameStack ≤ checkedStepEnvelope n :=
    checkedTagPrefixFuel_le_envelope n bits frameStack hsrc hfrm
  have hstep :
      checkedStepEnvelope n ≤ checkedLoopStepEnvelope n :=
    checkedStepEnvelope_le_loopEnvelope n
  have hmLoop : m ≤ checkedLoopStepEnvelope n := by
    unfold checkedTagPrefixFuel at hpref
    omega
  refine ⟨m, Nat.le_trans hmLoop
      (loopEnvelope_le_rawMalformedBudget fuel n), dead, hmem, ?_⟩
  exact Or.inr ⟨hactive, hdead⟩

/-- 110 and 111 are not semantic circuit tags and reject explicitly. -/
theorem invalid_tag_reaches_fail_closed
    (witness rest frameStack : BitString)
    (mode : SyntaxMode)
    (consumed padding n fuel : Nat)
    (b2 : Bool)
    (hbad : b2 = false ∨ b2 = true)
    (hLayout :
      CheckedLayoutBound n consumed
        (true :: true :: b2 :: rest) frameStack) :
    ∃ m ≤ rawMalformedBudget fuel n, ∃ cfg : EvalConfig,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (true :: true :: b2 :: rest) frameStack padding }] ∧
      EvalFailClosed cfg := by
  have hdis :
      tagAllowed mode (decodeTagBits true true b2) = false := by
    cases b2 <;> cases mode <;> rfl
  obtain ⟨m, hm, hmem⟩ :=
    disallowed_tag_prefix_reaches_reject
      mode witness rest frameStack consumed padding
      true true b2 hdis
  have hsrc := source_length_le_of_layout hLayout
  have hfrm := frame_length_le_of_layout hLayout
  have hpref :
      checkedTagPrefixFuel (true :: true :: b2 :: rest) frameStack ≤
        checkedStepEnvelope n :=
    checkedTagPrefixFuel_le_envelope n
      (true :: true :: b2 :: rest) frameStack hsrc hfrm
  have hmLoop : m ≤ checkedLoopStepEnvelope n :=
    Nat.le_trans (Nat.le_trans hm hpref)
      (checkedStepEnvelope_le_loopEnvelope n)
  let cfg : EvalConfig :=
    { state := .reject,
      tape :=
        evalCursorReadTape witness (consumed + 3)
          rest frameStack padding }
  refine ⟨m, Nat.le_trans hmLoop
      (loopEnvelope_le_rawMalformedBudget fuel n), cfg, ?_, ?_⟩
  · simpa [cfg] using hmem
  · exact Or.inl rfl

/-- Truncated unary INPUT payload reaches the already-certified active dead
input-lookahead state. -/
theorem unary_reaches_fail_closed
    (witness frameStack : BitString)
    (mode : SyntaxMode)
    (consumed padding n fuel k : Nat)
    (hLayout :
      CheckedLayoutBound n consumed
        (false :: false :: false :: List.replicate k true)
        frameStack) :
    ∃ m ≤ rawMalformedBudget fuel n, ∃ cfg : EvalConfig,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (false :: false :: false :: List.replicate k true)
               frameStack padding }] ∧
      EvalFailClosed cfg := by
  obtain ⟨m, hm, dead, hmem, hactive, hdead⟩ :=
    checked_truncated_unary_reaches_dead
      mode witness frameStack consumed padding k
  have hsrc := source_length_le_of_layout hLayout
  have hfrm := frame_length_le_of_layout hLayout
  have hpref :
      checkedTagPrefixFuel
          (false :: false :: false :: List.replicate k true)
          frameStack ≤ checkedStepEnvelope n :=
    checkedTagPrefixFuel_le_envelope n
      (false :: false :: false :: List.replicate k true)
      frameStack hsrc hfrm
  have hk : k + 1 ≤ n := by
    simp at hsrc
    omega
  have hkLoop : k + 1 ≤ checkedLoopStepEnvelope n :=
    Nat.le_trans hk (n_le_loopEnvelope n)
  have hm2 :
      m ≤ 2 * checkedLoopStepEnvelope n := by
    have hstep :=
      checkedStepEnvelope_le_loopEnvelope n
    omega
  refine ⟨m, Nat.le_trans hm2
      (two_loopEnvelope_le_rawMalformedBudget fuel n),
    dead, hmem, Or.inr ⟨hactive, hdead⟩⟩

#print axioms MCore.Real.P01RawMalformedBaseProducer.short_reaches_fail_closed
#print axioms MCore.Real.P01RawMalformedBaseProducer.invalid_tag_reaches_fail_closed
#print axioms MCore.Real.P01RawMalformedBaseProducer.unary_reaches_fail_closed

end P01RawMalformedBaseProducer
end Real
end MCore
