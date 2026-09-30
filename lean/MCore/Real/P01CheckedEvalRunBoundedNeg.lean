import MCore.Real.P01CheckedEvalRunBoundedCertificate
import MCore.Real.P01CheckedEvalRunCircuitCertificate
import MCore.Real.P01CheckedEvalRunHaveValue

namespace MCore
namespace Real
namespace P01CheckedEvalRunBoundedNeg

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunNeedTags
open P01CheckedEvalRunHaveValue
open P01CheckedEvalRunCircuitCertificate
open P01CheckedEvalRunBaseCases
open P01CheckedEvalRunBoundedHelpers
open P01CheckedEvalRunBoundedCertificate
open P01CheckedVerifierInvariant
open P01CheckedVerifierGlobalBudget
open P01CNFMode
open P01NTMRunLaws

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- The deliberately loose circuit budget absorbs one checked tag transition,
the recursively bounded child run, the negation return, and final outcome
normalization. -/
theorem neg_budget_absorbs
    (c : CircuitK1.Circuit) (n : Nat) :
    checkedLoopStepEnvelope n +
        checkedCircuitBudget c n +
        checkedLoopStepEnvelope n +
        checkedLoopStepEnvelope n ≤
      checkedCircuitBudget (.not c) n := by
  let E := checkedLoopStepEnvelope n
  let k := evalStepCount c
  have hcoeff :
      8 * (k + 1) + 3 ≤ 8 * (k + 3) := by
    omega
  have hmul :
      (8 * (k + 1) + 3) * E ≤
        (8 * (k + 3)) * E :=
    Nat.mul_le_mul_right E hcoeff
  change
    E + (8 * (k + 1) * E) + E + E ≤
      8 * (k + 3) * E
  have hshape :
      E + (8 * (k + 1) * E) + E + E =
        (8 * (k + 1) + 3) * E := by
    rw [Nat.add_mul]
    omega
  exact hshape.trans_le hmul

/-- Bounded structural producer for negation.

This is the first recursive constructor case of the bounded checked evaluator:
the physical checked tag transition, child execution, negation return, and
outcome normalization are all accounted for inside the same source-length
budget. -/
theorem neg_bounded_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (circuit : CircuitK1.Circuit)
    (hchild :
      BoundedCheckedCircuitRunCertificate
        sigma witness (childMode mode .neg) circuit) :
    BoundedCheckedCircuitRunCertificate
      sigma witness mode (.not circuit) := by
  intro hmode tail frames consumed padding n hLayout hlen hread

  have hmodeParts :
      tagAllowed mode .neg = true ∧
        modeCheck (childMode mode .neg) circuit = true := by
    have h := hmode
    rw [modeCheck_not] at h
    simpa using h
  have hAllowed : tagAllowed mode .neg = true := hmodeParts.1
  have hchildMode :
      modeCheck (childMode mode .neg) circuit = true := hmodeParts.2

  have hlenChild : varBound circuit ≤ witness.length := by
    simpa [varBound] using hlen
  have hreadChild :
      ∀ i, i < varBound circuit →
        witness.getD i false = sigma i := by
    intro i hi
    exact hread i (by simpa [varBound] using hi)

  have hLayout0 :
      CheckedLayoutBound n consumed
        (false :: true :: true :: (encodeCircuit circuit ++ tail))
        (encodeEvalFrames frames) := by
    simpa [encodeCircuit, List.append_assoc] using hLayout

  obtain ⟨m0, hm0, h0⟩ :=
    pushTag_checked_reaches_need_within_envelope
      n mode witness (encodeCircuit circuit ++ tail)
      (encodeEvalFrames frames) consumed padding
      false true true .neg .neg rfl hAllowed
      (by simp [P01CheckedEvalRunTagPrefix.postTagState, childMode])
      hLayout0.source_le hLayout0.frames_le

  let padChild := ((padding - 1) - 1) - 1
  let cNeed : CheckedConfig :=
    { state := .need (childMode mode .neg) needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness (consumed + 3)
          (encodeCircuit circuit ++ tail)
          (encodeEvalFrame .neg ++ encodeEvalFrames frames)
          padChild }

  have h0' :
      cNeed ∈ checkedEvalRunLoopMachine.runBranches m0
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (encodeCircuit (.not circuit) ++ tail)
               (encodeEvalFrames frames) padding }] := by
    simpa [cNeed, padChild, encodeCircuit, List.append_assoc] using h0

  have hLayoutChild :
      CheckedLayoutBound n (consumed + 3)
        (encodeCircuit circuit ++ tail)
        (encodeEvalFrames (.neg :: frames)) := by
    have h :=
      P01CheckedVerifierInvariant.after_push_tag
        n consumed false true true
        (encodeCircuit circuit ++ tail)
        (encodeEvalFrames frames) .neg hLayout0
    simpa [encodeEvalFrames, List.append_assoc] using h

  obtain ⟨m1, hm1, cfg1, h1, hout1⟩ :=
    hchild hchildMode tail (.neg :: frames)
      (consumed + 3) padChild n
      hLayoutChild hlenChild hreadChild

  have h1' :
      cfg1 ∈ checkedEvalRunLoopMachine.runBranches m1 [cNeed] := by
    simpa [cNeed, encodeEvalFrames, List.append_assoc] using h1

  have h01 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      m0 m1
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.not circuit) ++ tail)
             (encodeEvalFrames frames) padding }]
      cNeed cfg1 h0' h1'

  have hchildInput :
      ∃ i, circuit = .input i := by
    have hm :
        modeCheck .mustInput circuit = true := by
      simpa [childMode] using hchildMode
    exact (modeCheck_mustInput_iff circuit).1 hm

  have houtHave :
      ∃ consumed1 padding1,
        cfg1 =
          { state := .have .mustInput (.start (evalCircuit sigma circuit)),
            tape :=
              evalCursorStackEndTape witness consumed1 tail
                (encodeEvalFrames (.neg :: frames)) padding1 } := by
    rcases hchildInput with ⟨i, rfl⟩
    simpa [CheckedLoopOutcome, exitMode, childMode, circuitTag] using hout1

  rcases houtHave with ⟨consumed1, padding1, hcfg1⟩
  subst cfg1

  obtain ⟨m2, hm2, h2⟩ :=
    negReturn_checked_reaches_have
      .mustInput witness tail (encodeEvalFrames frames)
      consumed1 padding1 (evalCircuit sigma circuit)

  let cHave : CheckedConfig :=
    { state := .have .mustInput (.start (!(evalCircuit sigma circuit))),
      tape :=
        evalCursorStackEndTape witness consumed1 tail
          (encodeEvalFrames frames) (padding1 + 3) }

  have h2' :
      cHave ∈
        checkedEvalRunLoopMachine.runBranches m2
          [{ state := .have .mustInput
               (.start (evalCircuit sigma circuit)),
             tape :=
               evalCursorStackEndTape witness consumed1 tail
                 (encodeEvalFrames (.neg :: frames)) padding1 }] := by
    simpa [cHave, encodeEvalFrames, List.append_assoc] using h2

  have h012 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1) m2
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.not circuit) ++ tail)
             (encodeEvalFrames frames) padding }]
      ({ state := .have .mustInput
           (.start (evalCircuit sigma circuit)),
         tape :=
           evalCursorStackEndTape witness consumed1 tail
             (encodeEvalFrames (.neg :: frames)) padding1 } : CheckedConfig)
      cHave h01 h2'

  obtain ⟨m3, hm3, cfgFinal, h3, hout3⟩ :=
    have_reaches_outcome_within_envelope
      n .mustInput witness (!(evalCircuit sigma circuit))
      tail frames consumed1 (padding1 + 3)

  have hAll :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1 + m2) m3
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.not circuit) ++ tail)
             (encodeEvalFrames frames) padding }]
      cHave cfgFinal h012 h3

  refine ⟨m0 + m1 + m2 + m3, ?_, cfgFinal, hAll, ?_⟩
  · have hsum :
        m0 + m1 + m2 + m3 ≤
          checkedLoopStepEnvelope n +
            checkedCircuitBudget circuit n +
            checkedLoopStepEnvelope n +
            checkedLoopStepEnvelope n := by
      have hm2' : m2 ≤ checkedLoopStepEnvelope n :=
        Nat.le_trans hm2 (nine_le_stepEnvelope n)
      omega
    exact Nat.le_trans hsum (neg_budget_absorbs circuit n)
  · simpa [P01CheckedEvalRunBaseCases.exitMode, childMode,
      circuitTag, evalCircuit] using hout3

#print axioms MCore.Real.P01CheckedEvalRunBoundedNeg.neg_budget_absorbs
#print axioms MCore.Real.P01CheckedEvalRunBoundedNeg.neg_bounded_certificate

end P01CheckedEvalRunBoundedNeg
end Real
end MCore
