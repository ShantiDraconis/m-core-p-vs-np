import MCore.Real.P01CheckedEvalRunTagPrefix
import MCore.Real.CanonicalCircuitBits
import MCore.Real.P01EncodedFrameTape
import MCore.Real.P01CheckedEvalRunNeedTags

namespace MCore
namespace Real
namespace P01CheckedEvalReject

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01CNFMode
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunTagPrefix
open P01CheckedEvalRunNeedTags
open P01NTMRunLaws

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- If the canonical root tag of a circuit is forbidden by the current syntax
mode, the checked evaluator physically rejects after the common
seek/decode/check prefix.

This is the root-rejection producer.  It contains no recursive semantic
assumption about children. -/
theorem root_disallowed_reaches_reject
    (mode : SyntaxMode)
    (witness : BitString)
    (phi : Circuit)
    (tail : BitString)
    (frames : List P01EncodedStackEvaluator.EvalFrame)
    (consumed padding : Nat)
    (hroot :
      tagAllowed mode (circuitTag phi) = false) :
    ∃ m,
      ({ state := .reject,
         tape :=
           evalCursorReadTape witness (consumed + 3)
             ((encodeCircuit phi).drop 3 ++ tail)
             (encodeEvalFrames frames) padding } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit phi ++ tail)
                 (encodeEvalFrames frames) padding }] := by
  cases phi with
  | input i =>
      obtain ⟨m, hm, hrun⟩ :=
        disallowed_tag_prefix_reaches_reject
          mode witness (encodeNat i ++ tail)
          (encodeEvalFrames frames) consumed padding
          false false false hroot
      refine ⟨m, ?_⟩
      simpa [encodeCircuit, circuitTag, List.append_assoc] using hrun
  | const v =>
      cases v with
      | false =>
          obtain ⟨m, hm, hrun⟩ :=
            disallowed_tag_prefix_reaches_reject
              mode witness tail (encodeEvalFrames frames)
              consumed padding false false true hroot
          refine ⟨m, ?_⟩
          simpa [encodeCircuit, circuitTag] using hrun
      | true =>
          obtain ⟨m, hm, hrun⟩ :=
            disallowed_tag_prefix_reaches_reject
              mode witness tail (encodeEvalFrames frames)
              consumed padding false true false hroot
          refine ⟨m, ?_⟩
          simpa [encodeCircuit, circuitTag] using hrun
  | not child =>
      obtain ⟨m, hm, hrun⟩ :=
        disallowed_tag_prefix_reaches_reject
          mode witness (encodeCircuit child ++ tail)
          (encodeEvalFrames frames) consumed padding
          false true true hroot
      refine ⟨m, ?_⟩
      simpa [encodeCircuit, circuitTag, List.append_assoc] using hrun
  | and left right =>
      obtain ⟨m, hm, hrun⟩ :=
        disallowed_tag_prefix_reaches_reject
          mode witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding
          true false false hroot
      refine ⟨m, ?_⟩
      simpa [encodeCircuit, circuitTag, List.append_assoc] using hrun
  | or left right =>
      obtain ⟨m, hm, hrun⟩ :=
        disallowed_tag_prefix_reaches_reject
          mode witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding
          true false true hroot
      refine ⟨m, ?_⟩
      simpa [encodeCircuit, circuitTag, List.append_assoc] using hrun

/-- In must-input mode, every failing semantic check is already visible
at the root tag: the only admitted circuit form is an input node. -/
theorem mustInput_root_disallowed_of_check_false
    (phi : Circuit)
    (h : modeCheck .mustInput phi = false) :
    tagAllowed .mustInput (circuitTag phi) = false := by
  cases phi with
  | input i =>
      simp [modeCheck] at h
  | const v =>
      cases v <;> rfl
  | not c =>
      rfl
  | and a b =>
      rfl
  | or a b =>
      rfl

/-- A syntactically invalid negation is physically rejected.

If the current mode forbids the negation tag, rejection happens at the root.
Otherwise negation switches to must-input mode; any invalid child then has a
root-disallowed tag, so the already-certified root rejection producer applies
after the physical neg-frame push. -/
theorem invalid_not_reaches_reject
    (mode : SyntaxMode)
    (witness : BitString)
    (child : Circuit)
    (tail : BitString)
    (frames : List P01EncodedStackEvaluator.EvalFrame)
    (consumed padding : Nat)
    (hinvalid : modeCheck mode (.not child) = false) :
    ∃ m cfg,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (encodeCircuit (.not child) ++ tail)
               (encodeEvalFrames frames) padding }] ∧
      cfg.state = .reject := by
  cases hroot : tagAllowed mode .neg with
  | false =>
      have hroot' :
          tagAllowed mode (circuitTag (.not child)) = false := by
        simpa [circuitTag] using hroot
      obtain ⟨m, hrun⟩ :=
        root_disallowed_reaches_reject
          mode witness (.not child) tail frames consumed padding hroot'
      let cfg : CheckedConfig :=
        { state := .reject,
          tape :=
            evalCursorReadTape witness (consumed + 3)
              ((encodeCircuit (.not child)).drop 3 ++ tail)
              (encodeEvalFrames frames) padding }
      exact ⟨m, cfg, by simpa [cfg] using hrun, rfl⟩
  | true =>
      have hchild :
          modeCheck .mustInput child = false := by
        rw [modeCheck_not] at hinvalid
        simpa [hroot, childMode] using hinvalid
      have hchildRoot :
          tagAllowed .mustInput (circuitTag child) = false :=
        mustInput_root_disallowed_of_check_false child hchild

      obtain ⟨m0, h0⟩ :=
        neg_checked_reaches_need
          mode witness (encodeCircuit child ++ tail)
          (encodeEvalFrames frames) consumed padding hroot

      let padChild := ((padding - 1) - 1) - 1
      let cChild : CheckedConfig :=
        { state := .need .mustInput needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness (consumed + 3)
              (encodeCircuit child ++ tail)
              (encodeEvalFrames (.neg :: frames)) padChild }

      have h0' :
          cChild ∈ checkedEvalRunLoopMachine.runBranches m0
            [{ state := .need mode needExprCompositeMachine.initial,
               tape :=
                 evalCursorStackEndTape witness consumed
                   (encodeCircuit (.not child) ++ tail)
                   (encodeEvalFrames frames) padding }] := by
        simpa [cChild, padChild, encodeCircuit,
          encodeEvalFrames, List.append_assoc] using h0

      obtain ⟨m1, h1⟩ :=
        root_disallowed_reaches_reject
          .mustInput witness child tail (.neg :: frames)
          (consumed + 3) padChild hchildRoot

      let cReject : CheckedConfig :=
        { state := .reject,
          tape :=
            evalCursorReadTape witness (consumed + 6)
              ((encodeCircuit child).drop 3 ++ tail)
              (encodeEvalFrames (.neg :: frames)) padChild }

      have h1' :
          cReject ∈ checkedEvalRunLoopMachine.runBranches m1 [cChild] := by
        simpa [cReject, cChild] using h1

      have hAll :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          m0 m1
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.not child) ++ tail)
                 (encodeEvalFrames frames) padding }]
          cChild cReject h0' h1'

      exact ⟨m0 + m1, cReject, hAll, rfl⟩

/-- Producer-first rejection certificate for one circuit under one syntax
mode.  It is dual to `CheckedCircuitRunCertificate`: a failing mode check must
lead the physical checked loop to its reject state, while preserving arbitrary
external source tail and continuation stack. -/
def CheckedCircuitRejectCertificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (phi : Circuit) : Prop :=
  modeCheck mode phi = false →
  ∀ (tail : BitString)
      (frames : List P01EncodedStackEvaluator.EvalFrame)
      (consumed padding : Nat),
    varBound phi ≤ witness.length →
    (∀ i, i < varBound phi →
      witness.getD i false = sigma i) →
    ∃ m cfg,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (encodeCircuit phi ++ tail)
               (encodeEvalFrames frames) padding }] ∧
      cfg.state = .reject

/-- Input nodes are admitted by every syntax mode, so an invalid-input
certificate is vacuous. -/
theorem input_reject_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (i : Nat) :
    CheckedCircuitRejectCertificate sigma witness mode (.input i) := by
  intro hinvalid
  cases mode <;>
    simp [modeCheck, tagAllowed, isCNFBool, isClauseBool] at hinvalid

/-- Constants rejected by a syntax mode are rejected immediately at their root
tag. -/
theorem const_reject_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (v : Bool) :
    CheckedCircuitRejectCertificate sigma witness mode (.const v) := by
  intro hinvalid tail frames consumed padding hlen hread
  have hroot :
      tagAllowed mode (circuitTag (.const v)) = false := by
    cases v <;> cases mode <;>
      simp [modeCheck, tagAllowed, circuitTag,
        isCNFBool, isClauseBool] at hinvalid ⊢
  obtain ⟨m, hrun⟩ :=
    root_disallowed_reaches_reject
      mode witness (.const v) tail frames consumed padding hroot
  let cfg : CheckedConfig :=
    { state := .reject,
      tape :=
        evalCursorReadTape witness (consumed + 3)
          ((encodeCircuit (.const v)).drop 3 ++ tail)
          (encodeEvalFrames frames) padding }
  exact ⟨m, cfg, by simpa [cfg] using hrun, rfl⟩

/-- Negation rejection certificate: invalid negation is already completely
handled by the root/must-input producer above. -/
theorem not_reject_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (child : Circuit) :
    CheckedCircuitRejectCertificate sigma witness mode (.not child) := by
  intro hinvalid tail frames consumed padding hlen hread
  exact invalid_not_reaches_reject
    mode witness child tail frames consumed padding hinvalid

#print axioms MCore.Real.P01CheckedEvalReject.input_reject_certificate
#print axioms MCore.Real.P01CheckedEvalReject.const_reject_certificate
#print axioms MCore.Real.P01CheckedEvalReject.not_reject_certificate

#print axioms MCore.Real.P01CheckedEvalReject.mustInput_root_disallowed_of_check_false
#print axioms MCore.Real.P01CheckedEvalReject.invalid_not_reaches_reject

#print axioms MCore.Real.P01CheckedEvalReject.root_disallowed_reaches_reject

end P01CheckedEvalReject
end Real
end MCore
