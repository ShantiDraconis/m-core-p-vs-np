import MCore.Real.P01ExactBoundedCircuitProducer
import MCore.Real.P01CheckedEvalReject

namespace MCore
namespace Real
namespace P01ExactBoundedReject

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBoundedHelpers
open P01CheckedEvalRunBoundedCertificate
open P01CheckedEvalReject
open P01CheckedVerifierInvariant
open P01CheckedVerifierBudget
open P01CheckedVerifierGlobalBudget
open P01ExactBoundedCircuitProducer
open P01CNFMode
open P01NTMRunLaws

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- Bounded negative counterpart of the exact positive circuit certificate. -/
def ExactBoundedCheckedCircuitRejectCertificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (phi : CircuitK1.Circuit) : Prop :=
  modeCheck mode phi = false →
  ∀ (tail : BitString) (frames : List EvalFrame)
      (consumed padding n : Nat),
    CheckedLayoutBound n consumed
      (encodeCircuit phi ++ tail) (encodeEvalFrames frames) →
    varBound phi ≤ witness.length →
    (∀ i, i < varBound phi →
      witness.getD i false = sigma i) →
    ∃ m ≤ checkedCircuitBudget phi n, ∃ cfg,
      cfg ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit phi ++ tail)
                 (encodeEvalFrames frames) padding }] ∧
      cfg.state = .reject

/-- A syntactically forbidden physical tag rejects within one common loop
envelope. -/
theorem root_tag_reject_within_envelope
    (n : Nat)
    (mode : SyntaxMode)
    (witness rest frameStack : BitString)
    (consumed padding : Nat)
    (b0 b1 b2 : Bool)
    (hdisallowed :
      tagAllowed mode
        (P01NeedExprTagDecode.decodeTagBits b0 b1 b2) = false)
    (hsource : (b0 :: b1 :: b2 :: rest).length ≤ n)
    (hframes : frameStack.length ≤ n) :
    ∃ m ≤ checkedLoopStepEnvelope n, ∃ tape,
      ({ state := .reject, tape := tape } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (b0 :: b1 :: b2 :: rest)
                 frameStack padding }] := by
  obtain ⟨m, hm, hrun⟩ :=
    P01CheckedEvalRunTagPrefix.disallowed_tag_prefix_reaches_reject
      mode witness rest frameStack consumed padding
      b0 b1 b2 hdisallowed
  have hfuel :
      P01CheckedEvalRunTagPrefix.checkedTagPrefixFuel
          (b0 :: b1 :: b2 :: rest) frameStack ≤
        checkedStepEnvelope n :=
    checkedTagPrefixFuel_le_envelope
      n (b0 :: b1 :: b2 :: rest) frameStack hsource hframes
  refine ⟨m, Nat.le_trans hm
      (Nat.le_trans hfuel (checkedStepEnvelope_le_loopEnvelope n)),
    evalCursorReadTape witness (consumed + 3) rest frameStack padding,
    ?_⟩
  simpa using hrun

/-- Input nodes are valid in every syntax mode, so their negative certificate
is vacuous. -/
theorem input_exact_bounded_reject
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (i : Nat) :
    ExactBoundedCheckedCircuitRejectCertificate
      sigma witness mode (.input i) := by
  intro hinvalid
  cases mode <;>
    simp [modeCheck, tagAllowed, isCNFBool, isClauseBool] at hinvalid

/-- Invalid constants reject at their root tag under the exact circuit budget. -/
theorem const_exact_bounded_reject
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (v : Bool) :
    ExactBoundedCheckedCircuitRejectCertificate
      sigma witness mode (.const v) := by
  intro hinvalid tail frames consumed padding n hLayout hlen hread
  have hroot :
      tagAllowed mode (circuitTag (.const v)) = false := by
    cases v <;> cases mode <;>
      simp [modeCheck, tagAllowed, circuitTag,
        isCNFBool, isClauseBool] at hinvalid ⊢
  cases v with
  | false =>
      obtain ⟨m, hm, tape, hrun⟩ :=
        root_tag_reject_within_envelope
          n mode witness tail (encodeEvalFrames frames)
          consumed padding false false true
          (by simpa [circuitTag] using hroot)
          (by simpa [encodeCircuit] using hLayout.source_le)
          hLayout.frames_le
      refine ⟨m,
        Nat.le_trans hm
          (loopEnvelope_le_checkedCircuitBudget (.const false) n),
        { state := .reject, tape := tape }, ?_, rfl⟩
      simpa [encodeCircuit] using hrun
  | true =>
      obtain ⟨m, hm, tape, hrun⟩ :=
        root_tag_reject_within_envelope
          n mode witness tail (encodeEvalFrames frames)
          consumed padding false true false
          (by simpa [circuitTag] using hroot)
          (by simpa [encodeCircuit] using hLayout.source_le)
          hLayout.frames_le
      refine ⟨m,
        Nat.le_trans hm
          (loopEnvelope_le_checkedCircuitBudget (.const true) n),
        { state := .reject, tape := tape }, ?_, rfl⟩
      simpa [encodeCircuit] using hrun

/-- Bounded negative producer for negation.  If the root negation tag is
forbidden, rejection is immediate.  Otherwise the child is entered in
must-input mode and its bounded negative certificate is composed. -/
theorem neg_exact_bounded_reject
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (child : CircuitK1.Circuit)
    (hchild :
      ExactBoundedCheckedCircuitRejectCertificate
        sigma witness (childMode mode .neg) child) :
    ExactBoundedCheckedCircuitRejectCertificate
      sigma witness mode (.not child) := by
  intro hinvalid tail frames consumed padding n hLayout hlen hread
  cases hroot : tagAllowed mode .neg with
  | false =>
      have hLayout0 :
          CheckedLayoutBound n consumed
            (false :: true :: true :: (encodeCircuit child ++ tail))
            (encodeEvalFrames frames) := by
        simpa [encodeCircuit, List.append_assoc] using hLayout
      obtain ⟨m, hm, tape, hrun⟩ :=
        root_tag_reject_within_envelope
          n mode witness (encodeCircuit child ++ tail)
          (encodeEvalFrames frames) consumed padding
          false true true
          (by simpa using hroot)
          hLayout0.source_le hLayout0.frames_le
      refine ⟨m,
        Nat.le_trans hm
          (loopEnvelope_le_checkedCircuitBudget (.not child) n),
        { state := .reject, tape := tape }, ?_, rfl⟩
      simpa [encodeCircuit, List.append_assoc] using hrun
  | true =>
      have hchildInvalid :
          modeCheck (childMode mode .neg) child = false := by
        rw [modeCheck_not] at hinvalid
        simpa [hroot] using hinvalid

      have hlenChild : varBound child ≤ witness.length := by
        simpa [varBound] using hlen
      have hreadChild :
          ∀ i, i < varBound child →
            witness.getD i false = sigma i := by
        intro i hi
        exact hread i (by simpa [varBound] using hi)

      have hLayout0 :
          CheckedLayoutBound n consumed
            (false :: true :: true :: (encodeCircuit child ++ tail))
            (encodeEvalFrames frames) := by
        simpa [encodeCircuit, List.append_assoc] using hLayout

      have hLayoutChild :
          CheckedLayoutBound n (consumed + 3)
            (encodeCircuit child ++ tail)
            (encodeEvalFrame .neg ++ encodeEvalFrames frames) :=
        after_push_tag n consumed false true true
          (encodeCircuit child ++ tail) (encodeEvalFrames frames) .neg hLayout0

      obtain ⟨m0, hm0, h0⟩ :=
        pushTag_checked_reaches_need_within_envelope
          n mode witness (encodeCircuit child ++ tail)
          (encodeEvalFrames frames) consumed padding
          false true true .neg .neg rfl hroot rfl
          hLayout0.source_le hLayout0.frames_le

      let padChild := ((padding - 1) - 1) - 1
      let cNeed : CheckedConfig :=
        { state := .need (childMode mode .neg)
            needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness (consumed + 3)
              (encodeCircuit child ++ tail)
              (encodeEvalFrame .neg ++ encodeEvalFrames frames)
              padChild }

      have h0' :
          cNeed ∈
            checkedEvalRunLoopMachine.runBranches m0
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.not child) ++ tail)
                     (encodeEvalFrames frames) padding }] := by
        simpa [cNeed, padChild, encodeCircuit, List.append_assoc] using h0

      obtain ⟨m1, hm1, cfg1, h1, hrej⟩ :=
        hchild hchildInvalid tail (.neg :: frames)
          (consumed + 3) padChild n
          (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutChild)
          hlenChild hreadChild

      have h1' :
          cfg1 ∈ checkedEvalRunLoopMachine.runBranches m1 [cNeed] := by
        simpa [cNeed, encodeEvalFrames, List.append_assoc] using h1

      have hAll :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          m0 m1
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.not child) ++ tail)
                 (encodeEvalFrames frames) padding }]
          cNeed cfg1 h0' h1'

      have hbudget :
          m0 + m1 ≤ checkedCircuitBudget (.not child) n := by
        have hraw :
            m0 + m1 ≤
              checkedLoopStepEnvelope n +
                checkedCircuitBudget child n := by
          omega
        let E := checkedLoopStepEnvelope n
        have hcoef :
            1 + 8 * (evalStepCount child + 1) ≤
              8 * (evalStepCount (.not child) + 1) := by
          simp [evalStepCount]
          omega
        have hmul := Nat.mul_le_mul_right E hcoef
        have hcap :
            checkedLoopStepEnvelope n +
                checkedCircuitBudget child n ≤
              checkedCircuitBudget (.not child) n := by
          unfold checkedCircuitBudget
          dsimp [E] at hmul ⊢
          omega
        exact Nat.le_trans hraw hcap

      exact ⟨m0 + m1, hbudget, cfg1, hAll, hrej⟩

#print axioms MCore.Real.P01ExactBoundedReject.root_tag_reject_within_envelope
#print axioms MCore.Real.P01ExactBoundedReject.input_exact_bounded_reject
#print axioms MCore.Real.P01ExactBoundedReject.const_exact_bounded_reject
#print axioms MCore.Real.P01ExactBoundedReject.neg_exact_bounded_reject

end P01ExactBoundedReject
end Real
end MCore
