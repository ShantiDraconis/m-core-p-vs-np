import MCore.Real.P01CheckedEvalRunPhaseLift
import MCore.Real.P01CheckedVerifierInvariant
import MCore.Real.P01NeedExprTagDecode
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01MalformedPhysicalReject

open CanonicalFinalProof
open P01CNFMode
open P01EvalCursorMachine
open P01NeedExprTagDecode
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunPhaseLift
open P01NTMRunLaws

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

private theorem one_step_of_successor
    (a b : CheckedConfig)
    (ha : ¬ Halted checkedEvalRunLoopMachine a)
    (hs : b ∈ checkedEvalRunLoopMachine.successors a) :
    b ∈ checkedEvalRunLoopMachine.runBranches 1 [a] := by
  have h :=
    mem_runBranches_succ_of_successor
      checkedEvalRunLoopMachine 0 [a] a b
      (by simp [NTM.runBranches]) ha hs
  simpa using h

/-- On fewer than three unread source bits the physical three-bit tag decoder
reaches its reject state within three deterministic decoder steps. -/
theorem tagDecode_short_rejects_within_three
    (witness bits frameStack : BitString)
    (consumed padding : Nat)
    (hshort : bits.length < 3) :
    ∃ d ≤ 3,
      (tagDecodeMachine.run d
        { state := tagDecodeMachine.initial,
          tape := evalCursorReadTape witness consumed bits frameStack padding }).state =
        .reject := by
  rcases bits with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, rest⟩⟩⟩
  · refine ⟨1, by omega, ?_⟩
    simp [tagDecodeMachine, evalCursorReadTape, TM.run, TM.step,
      Tape.write, Tape.move]
  · refine ⟨2, by omega, ?_⟩
    cases b0 <;>
      simp [tagDecodeMachine, evalCursorReadTape, TM.run, TM.step,
        Tape.write, Tape.move]
  · refine ⟨3, by omega, ?_⟩
    cases b0 <;> cases b1 <;>
      simp [tagDecodeMachine, evalCursorReadTape, TM.run, TM.step,
        Tape.write, Tape.move]
  · simp at hshort

/-- Short unread sources are physically rejected by the checked evaluator.

The proof is exact machine composition:
stack-end layout -> certified cursor seek -> decoder handoff -> bounded short
decoder rejection -> checked reject handoff.  No semantic decoder assumption is
used. -/
theorem short_source_reaches_reject
    (mode : SyntaxMode)
    (witness bits frameStack : BitString)
    (consumed padding : Nat)
    (hshort : bits.length < 3) :
    ∃ m ≤ frameStack.length + bits.length + 8, ∃ cfg : CheckedConfig,
      cfg ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 bits frameStack padding }] ∧
      cfg.state = .reject := by
  let nSeek := frameStack.length + bits.length + 3
  let cSeek0 : Configuration CursorSeekState (Option Bool) :=
    { state := cursorSeekMachine.initial,
      tape := evalCursorStackEndTape witness consumed bits frameStack padding }
  let cSeekH : Configuration CursorSeekState (Option Bool) :=
    { state := .halt,
      tape := evalCursorReadTape witness consumed bits frameStack padding }

  have hSeekExact : cursorSeekMachine.run nSeek cSeek0 = cSeekH := by
    dsimp [nSeek, cSeek0, cSeekH]
    exact cursorSeek_run witness consumed bits frameStack padding

  obtain ⟨mS, hmS, hS⟩ :=
    seek_run_reachable mode nSeek cSeek0
  have hS' :
      seekConfig mode cSeekH ∈
        checkedEvalRunLoopMachine.runBranches mS [seekConfig mode cSeek0] := by
    rw [hSeekExact] at hS
    exact hS

  let cDec0 : Configuration TagDecodeState (Option Bool) :=
    { state := tagDecodeMachine.initial,
      tape := evalCursorReadTape witness consumed bits frameStack padding }

  have hHandSucc :
      decodeConfig mode cDec0 ∈
        checkedEvalRunLoopMachine.successors (seekConfig mode cSeekH) := by
    dsimp [cDec0, cSeekH, decodeConfig, seekConfig]
    simp [checkedEvalRunLoopMachine, needExprCompositeMachine,
      needCheckedEmbed, NTM.successors, NTM.stepBranch,
      Tape.write, Tape.move]

  have hHand :
      decodeConfig mode cDec0 ∈
        checkedEvalRunLoopMachine.runBranches 1 [seekConfig mode cSeekH] :=
    one_step_of_successor
      (seekConfig mode cSeekH) (decodeConfig mode cDec0)
      (seekConfig_not_halted mode cSeekH) hHandSucc

  have hToDec :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      mS 1 [seekConfig mode cSeek0]
      (seekConfig mode cSeekH) (decodeConfig mode cDec0)
      hS' hHand

  obtain ⟨d, hd, hRejectState⟩ :=
    tagDecode_short_rejects_within_three
      witness bits frameStack consumed padding hshort

  obtain ⟨mD, hmD, hD⟩ :=
    decode_run_reachable mode d cDec0

  let cDecR := decodeConfig mode (tagDecodeMachine.run d cDec0)
  have hD' :
      cDecR ∈
        checkedEvalRunLoopMachine.runBranches mD [decodeConfig mode cDec0] := by
    simpa [cDecR] using hD

  have hToRejectDecode :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (mS + 1) mD [seekConfig mode cSeek0]
      (decodeConfig mode cDec0) cDecR
      hToDec hD'

  have hcstate :
      cDecR.state = .need mode (.decode .reject) := by
    dsimp [cDecR, decodeConfig]
    rw [hRejectState]

  let cReject : CheckedConfig :=
    { state := .reject, tape := cDecR.tape }

  have hRejectSucc :
      cReject ∈ checkedEvalRunLoopMachine.successors cDecR := by
    rcases cDecR with ⟨q, tape⟩
    simp only at hcstate
    subst q
    dsimp [cReject]
    simp [checkedEvalRunLoopMachine, needExprCompositeMachine,
      needCheckedEmbed, NTM.successors, NTM.stepBranch,
      Tape.write, Tape.move]

  have hNotHalted : ¬ Halted checkedEvalRunLoopMachine cDecR := by
    rcases cDecR with ⟨q, tape⟩
    simp only at hcstate
    subst q
    simp [Halted, checkedEvalRunLoopMachine, needExprCompositeMachine]

  have hRejectOne :
      cReject ∈ checkedEvalRunLoopMachine.runBranches 1 [cDecR] :=
    one_step_of_successor cDecR cReject hNotHalted hRejectSucc

  have hAll :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (mS + 1 + mD) 1 [seekConfig mode cSeek0]
      cDecR cReject hToRejectDecode hRejectOne

  refine ⟨mS + 1 + mD + 1, ?_, cReject, ?_, rfl⟩
  · dsimp [nSeek] at hmS
    omega
  · dsimp [cSeek0, seekConfig] at hAll ⊢
    simpa using hAll

#print axioms MCore.Real.P01MalformedPhysicalReject.tagDecode_short_rejects_within_three
#print axioms MCore.Real.P01MalformedPhysicalReject.short_source_reaches_reject

end P01MalformedPhysicalReject
end Real
end MCore
