import MCore.Real.P01CheckedEvalRunBaseCases
import MCore.Real.P01CheckedEvalRunNeedTags
import MCore.Real.P01CheckedEvalRunHaveValue
import MCore.Real.P01CheckedEvalRunInputTag
import MCore.Real.CanonicalSATWitness
import MCore.Real.CanonicalCircuitBits
import MCore.Real.P01EncodedFrameTape

namespace MCore
namespace Real
namespace P01CheckedEvalRunCircuitCertificate

open CanonicalFinalProof
open CircuitK1
open CanonicalSATWitness
open CanonicalCircuitBits
open P01EncodedFrameTape
open P01EncodedStackEvaluator
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBaseCases
open P01CheckedEvalRunNeedTags
open P01CheckedEvalRunHaveValue
open P01CheckedEvalRunInputTag
open P01CNFMode
open P01NTMRunLaws

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- Normalize a checked haveValue state into the external checked circuit
outcome.  If external source or continuation frames remain, no step is needed.
If both are empty, reuse the mandatory source-empty finalization guard. -/
theorem have_reaches_outcome
    (mode : SyntaxMode)
    (witness : BitString)
    (value : Bool)
    (tail : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat) :
    ∃ m cfg,
      cfg ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .have mode (.start value),
             tape :=
               evalCursorStackEndTape witness consumed tail
                 (encodeEvalFrames frames) padding }] ∧
      CheckedLoopOutcome witness mode value tail frames cfg := by
  cases tail with
  | cons b bs =>
      let cfg : CheckedConfig :=
        { state := .have mode (.start value),
          tape :=
            evalCursorStackEndTape witness consumed (b :: bs)
              (encodeEvalFrames frames) padding }
      refine ⟨0, cfg, ?_, ?_⟩
      · simp [cfg, NTM.runBranches]
      · exact ⟨consumed, padding, rfl⟩
  | nil =>
      cases frames with
      | cons f fs =>
          let cfg : CheckedConfig :=
            { state := .have mode (.start value),
              tape :=
                evalCursorStackEndTape witness consumed []
                  (encodeEvalFrames (f :: fs)) padding }
          refine ⟨0, cfg, ?_, ?_⟩
          · simp [cfg, NTM.runBranches]
          · exact ⟨consumed, padding, rfl⟩
      | nil =>
          obtain ⟨m, hm, hrun⟩ :=
            checked_empty_frames_reaches_final
              mode witness consumed padding value
          let cfg : CheckedConfig :=
            { state := .final value,
              tape :=
                Tape.move none .left
                  (Tape.move none .left
                    (evalCursorStackEndTape witness consumed [] [] padding)) }
          refine ⟨m, cfg, ?_, ?_⟩
          · simpa [cfg] using hrun
          · exact ⟨cfg.tape, rfl⟩

/-- Checked structural producer for negation.

A checked negation is necessarily a literal: `modeCheck_not` forces its child
into `mustInput`.  The physical route therefore consists of the admitted neg
tag, the already-certified checked child run, the neg continuation return, and
the common haveValue normalization above. -/
theorem neg_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (circuit : Circuit)
    (hchild :
      CheckedCircuitRunCertificate
        sigma witness (childMode mode .neg) circuit) :
    CheckedCircuitRunCertificate sigma witness mode (.not circuit) := by
  intro hmode tail frames consumed padding hlen hread

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

  obtain ⟨m0, h0⟩ :=
    neg_checked_reaches_need
      mode witness (encodeCircuit circuit ++ tail)
        (encodeEvalFrames frames) consumed padding hAllowed

  let padChild := ((padding - 1) - 1) - 1
  let childMode' := childMode mode .neg
  let cNeed : CheckedConfig :=
    { state := .need childMode' needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness (consumed + 3)
          (encodeCircuit circuit ++ tail)
          (encodeEvalFrame .neg ++ encodeEvalFrames frames)
          padChild }

  have h0' :
      cNeed ∈
        checkedEvalRunLoopMachine.runBranches m0
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.not circuit) ++ tail)
                 (encodeEvalFrames frames) padding }] := by
    simpa [cNeed, childMode', childMode, padChild, encodeCircuit,
      List.append_assoc] using h0

  obtain ⟨m1, cfg1, h1, hout1⟩ :=
    hchild hchildMode tail (.neg :: frames)
      (consumed + 3) padChild hlenChild hreadChild

  have h1' :
      cfg1 ∈ checkedEvalRunLoopMachine.runBranches m1 [cNeed] := by
    simpa [cNeed, childMode', encodeEvalFrames,
      List.append_assoc] using h1

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

  obtain ⟨m3, cfgFinal, h3, hout3⟩ :=
    have_reaches_outcome
      .mustInput witness (!(evalCircuit sigma circuit))
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

  refine ⟨m0 + m1 + m2 + m3, cfgFinal, hAll, ?_⟩
  simpa [CheckedLoopOutcome, exitMode, childMode, circuitTag, evalCircuit] using hout3

#print axioms MCore.Real.P01CheckedEvalRunCircuitCertificate.have_reaches_outcome
#print axioms MCore.Real.P01CheckedEvalRunCircuitCertificate.neg_certificate

end P01CheckedEvalRunCircuitCertificate
end Real
end MCore
