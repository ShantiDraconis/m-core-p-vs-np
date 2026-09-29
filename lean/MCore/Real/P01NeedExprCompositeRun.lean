import MCore.Real.P01NeedExprCompositeNTM
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01NeedExprCompositeRun

open CanonicalFinalProof
open P01NTMRunLaws
open P01EvalCursorMachine
open P01EvalCursorRoundTrip
open P01EvalFramePushMachine
open P01EncodedStackEvaluator
open P01NeedExprTagDecode
open P01InputNodeCompositeNTM
open P01NeedExprCompositeNTM

abbrev NeedExprConfig :=
  Configuration NeedExprCompositeState (Option Bool)

def seekConfig
    (c : Configuration CursorSeekState (Option Bool)) :
    NeedExprConfig :=
  { state := .seek c.state, tape := c.tape }

def decodeConfig
    (c : Configuration TagDecodeState (Option Bool)) :
    NeedExprConfig :=
  { state := .decode c.state, tape := c.tape }

def retValueConfig
    (value : Bool)
    (c : Configuration CursorReturnState (Option Bool)) :
    NeedExprConfig :=
  { state := .retValue value c.state, tape := c.tape }

def retPushConfig
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (c : Configuration CursorReturnState (Option Bool)) :
    NeedExprConfig :=
  { state := .retPush frame c.state, tape := c.tape }

def pushConfig
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (c : Configuration FramePushState (Option Bool)) :
    NeedExprConfig :=
  { state := .push frame c.state, tape := c.tape }

@[simp] theorem seekConfig_not_halted
    (c : Configuration CursorSeekState (Option Bool)) :
    ¬ Halted needExprCompositeMachine (seekConfig c) := by
  simp [Halted, seekConfig, needExprCompositeMachine]

@[simp] theorem decodeConfig_not_halted
    (c : Configuration TagDecodeState (Option Bool)) :
    ¬ Halted needExprCompositeMachine (decodeConfig c) := by
  simp [Halted, decodeConfig, needExprCompositeMachine]

@[simp] theorem retValueConfig_not_halted
    (value : Bool)
    (c : Configuration CursorReturnState (Option Bool)) :
    ¬ Halted needExprCompositeMachine (retValueConfig value c) := by
  simp [Halted, retValueConfig, needExprCompositeMachine]

@[simp] theorem retPushConfig_not_halted
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (c : Configuration CursorReturnState (Option Bool)) :
    ¬ Halted needExprCompositeMachine (retPushConfig frame c) := by
  simp [Halted, retPushConfig, needExprCompositeMachine]

@[simp] theorem pushConfig_not_halted
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (c : Configuration FramePushState (Option Bool)) :
    ¬ Halted needExprCompositeMachine (pushConfig frame c) := by
  simp [Halted, pushConfig, needExprCompositeMachine]

theorem seek_successors_active
    (c : Configuration CursorSeekState (Option Bool))
    (h : cursorSeekMachine.halting c.state = false) :
    needExprCompositeMachine.successors (seekConfig c) =
      [seekConfig (cursorSeekMachine.step c)] := by
  unfold NTM.successors
  simp only [seekConfig]
  rw [seek_transition_active c.state c.tape.head h]
  simp [seekConfig, NTM.stepBranch, TM.step,
    cursorSeekMachine, needExprCompositeMachine,
    Tape.write, Tape.move]

theorem decode_successors_active
    (c : Configuration TagDecodeState (Option Bool))
    (h : tagDecodeMachine.halting c.state = false) :
    needExprCompositeMachine.successors (decodeConfig c) =
      [decodeConfig (tagDecodeMachine.step c)] := by
  unfold NTM.successors
  simp only [decodeConfig]
  rw [decode_transition_active c.state c.tape.head h]
  simp [decodeConfig, NTM.stepBranch, TM.step,
    tagDecodeMachine, needExprCompositeMachine,
    Tape.write, Tape.move]

theorem retValue_successors_active
    (value : Bool)
    (c : Configuration CursorReturnState (Option Bool))
    (h : cursorReturnMachine.halting c.state = false) :
    needExprCompositeMachine.successors (retValueConfig value c) =
      [retValueConfig value (cursorReturnMachine.step c)] := by
  unfold NTM.successors
  simp only [retValueConfig]
  rw [retValue_transition_active value c.state c.tape.head h]
  simp [retValueConfig, NTM.stepBranch, TM.step,
    cursorReturnMachine, needExprCompositeMachine,
    Tape.write, Tape.move]

theorem retPush_successors_active
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (c : Configuration CursorReturnState (Option Bool))
    (h : cursorReturnMachine.halting c.state = false) :
    needExprCompositeMachine.successors (retPushConfig frame c) =
      [retPushConfig frame (cursorReturnMachine.step c)] := by
  unfold NTM.successors
  simp only [retPushConfig]
  rw [retPush_transition_active frame c.state c.tape.head h]
  simp only [List.map_singleton]
  simp [retPushConfig, NTM.stepBranch, TM.step,
    needExprCompositeMachine, cursorReturnMachine]

theorem push_successors_active
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (c : Configuration FramePushState (Option Bool))
    (h : framePushMachine.halting c.state = false) :
    needExprCompositeMachine.successors (pushConfig frame c) =
      [pushConfig frame (framePushMachine.step c)] := by
  unfold NTM.successors
  simp only [pushConfig]
  rw [push_transition_active frame c.state c.tape.head h]
  simp [pushConfig, NTM.stepBranch, TM.step,
    framePushMachine, needExprCompositeMachine,
    Tape.write, Tape.move]

/-- Generic deterministic phase reachability, specialized by an injection and
a one-step successor theorem. -/
private theorem tm_phase_run_reachable
    {S : Type}
    (M : TM S (Option Bool))
    (embed : Configuration S (Option Bool) → NeedExprConfig)
    (embed_not_halted :
      ∀ c, ¬ Halted needExprCompositeMachine (embed c))
    (step_successors :
      ∀ c, M.halting c.state = false →
        needExprCompositeMachine.successors (embed c) =
          [embed (M.step c)]) :
    ∀ (n : Nat) (c : Configuration S (Option Bool)),
      ∃ m ≤ n,
        embed (M.run n c) ∈
          needExprCompositeMachine.runBranches m [embed c] := by
  intro n
  induction n with
  | zero =>
      intro c
      refine ⟨0, by omega, ?_⟩
      change embed c ∈ [embed c]
      simp
  | succ n ih =>
      intro c
      cases hhalt : M.halting c.state with
      | true =>
          have hr := MachineRunLemmas.run_halted M c hhalt (n + 1)
          refine ⟨0, by omega, ?_⟩
          rw [hr]
          simp [NTM.runBranches]
      | false =>
          obtain ⟨m, hm, hmem⟩ := ih (M.step c)
          have hsucc :
              embed (M.step c) ∈
                needExprCompositeMachine.successors (embed c) := by
            rw [step_successors c hhalt]
            simp
          have hone :
              embed (M.step c) ∈
                needExprCompositeMachine.runBranches 1 [embed c] := by
            have h :=
              mem_runBranches_succ_of_successor
                needExprCompositeMachine 0 [embed c]
                (embed c) (embed (M.step c))
                (by simp [NTM.runBranches])
                (embed_not_halted c) hsucc
            simpa using h
          have htrans :=
            mem_runBranches_trans needExprCompositeMachine
              1 m [embed c]
              (embed (M.step c))
              (embed (M.run n (M.step c)))
              hone hmem
          refine ⟨1 + m, by omega, ?_⟩
          simpa [TM.run, hhalt] using htrans

theorem seek_run_reachable
    (n : Nat)
    (c : Configuration CursorSeekState (Option Bool)) :
    ∃ m ≤ n,
      seekConfig (cursorSeekMachine.run n c) ∈
        needExprCompositeMachine.runBranches m [seekConfig c] :=
  tm_phase_run_reachable
    cursorSeekMachine seekConfig
    seekConfig_not_halted seek_successors_active n c

theorem decode_run_reachable
    (n : Nat)
    (c : Configuration TagDecodeState (Option Bool)) :
    ∃ m ≤ n,
      decodeConfig (tagDecodeMachine.run n c) ∈
        needExprCompositeMachine.runBranches m [decodeConfig c] :=
  tm_phase_run_reachable
    tagDecodeMachine decodeConfig
    decodeConfig_not_halted decode_successors_active n c

theorem retValue_run_reachable
    (value : Bool) (n : Nat)
    (c : Configuration CursorReturnState (Option Bool)) :
    ∃ m ≤ n,
      retValueConfig value (cursorReturnMachine.run n c) ∈
        needExprCompositeMachine.runBranches m [retValueConfig value c] :=
  tm_phase_run_reachable
    cursorReturnMachine (retValueConfig value)
    (retValueConfig_not_halted value)
    (retValue_successors_active value) n c

theorem retPush_run_reachable
    (frame : P01EncodedStackEvaluator.EvalFrame) (n : Nat)
    (c : Configuration CursorReturnState (Option Bool)) :
    ∃ m ≤ n,
      retPushConfig frame (cursorReturnMachine.run n c) ∈
        needExprCompositeMachine.runBranches m [retPushConfig frame c] :=
  tm_phase_run_reachable
    cursorReturnMachine (retPushConfig frame)
    (retPushConfig_not_halted frame)
    (retPush_successors_active frame) n c

theorem push_run_reachable
    (frame : P01EncodedStackEvaluator.EvalFrame) (n : Nat)
    (c : Configuration FramePushState (Option Bool)) :
    ∃ m ≤ n,
      pushConfig frame (framePushMachine.run n c) ∈
        needExprCompositeMachine.runBranches m [pushConfig frame c] :=
  tm_phase_run_reachable
    framePushMachine (pushConfig frame)
    (pushConfig_not_halted frame)
    (push_successors_active frame) n c

/-- One active successor is reachable in one composite step. -/
private theorem one_step_of_successor
    (a b : NeedExprConfig)
    (ha : ¬ Halted needExprCompositeMachine a)
    (hs : b ∈ needExprCompositeMachine.successors a) :
    b ∈ needExprCompositeMachine.runBranches 1 [a] := by
  have h :=
    mem_runBranches_succ_of_successor
      needExprCompositeMachine 0 [a] a b
      (by simp [NTM.runBranches]) ha hs
  simpa using h

/-- Uniform majorant for the fused constant-tag route. -/
def constTagCompositeFuel
    (frameStack rest : BitString) : Nat :=
  (frameStack.length + (rest.length + 3) + 3) +
    1 + 3 + 1 +
    (rest.length + frameStack.length + 2) + 1

/-- Complete physical `001` route in the single fused `needExpr` NTM. -/
theorem constFalse_reaches_done
    (witness rest frameStack : BitString)
    (consumed padding : Nat) :
    ∃ m ≤ constTagCompositeFuel frameStack rest,
      ({ state := .doneValue false,
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest frameStack padding } : NeedExprConfig) ∈
        needExprCompositeMachine.runBranches m
          [{ state := needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (false :: false :: true :: rest)
                 frameStack padding }] := by
  let nSeek := frameStack.length + (rest.length + 3) + 3
  let nRet := rest.length + frameStack.length + 2
  let t0 :=
    evalCursorStackEndTape witness consumed
      (false :: false :: true :: rest) frameStack padding
  let tRead :=
    evalCursorReadTape witness consumed
      (false :: false :: true :: rest) frameStack padding
  let tAfterTag :=
    evalCursorReadTape witness (consumed + 3)
      rest frameStack padding
  let tDone :=
    evalCursorStackEndTape witness (consumed + 3)
      rest frameStack padding

  let cSeek0 : Configuration CursorSeekState (Option Bool) :=
    { state := cursorSeekMachine.initial, tape := t0 }
  let cSeekH : Configuration CursorSeekState (Option Bool) :=
    { state := .halt, tape := tRead }
  let cDec0 : Configuration TagDecodeState (Option Bool) :=
    { state := tagDecodeMachine.initial, tape := tRead }
  let cDecH : Configuration TagDecodeState (Option Bool) :=
    { state := .halt .constFalse, tape := tAfterTag }
  let cRet0 : Configuration CursorReturnState (Option Bool) :=
    { state := .scanUnread, tape := tAfterTag }
  let cRetH : Configuration CursorReturnState (Option Bool) :=
    { state := .halt, tape := tDone }
  let cDone : NeedExprConfig :=
    { state := .doneValue false, tape := tDone }

  have hSeekExact :
      cursorSeekMachine.run nSeek cSeek0 = cSeekH := by
    dsimp [nSeek, cSeek0, cSeekH, t0, tRead]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      cursorSeek_run witness consumed
        (false :: false :: true :: rest) frameStack padding

  obtain ⟨mS, hmS, hS⟩ := seek_run_reachable nSeek cSeek0
  have hS' :
      seekConfig cSeekH ∈
        needExprCompositeMachine.runBranches mS [seekConfig cSeek0] := by
    rw [hSeekExact] at hS
    exact hS

  have hSeekHandSucc :
      decodeConfig cDec0 ∈
        needExprCompositeMachine.successors (seekConfig cSeekH) := by
    rw [seek_handoff_successors tRead]
    simp [seekConfig, decodeConfig, cSeekH, cDec0]
  have hSeekHand :
      decodeConfig cDec0 ∈
        needExprCompositeMachine.runBranches 1 [seekConfig cSeekH] :=
    one_step_of_successor
      (seekConfig cSeekH) (decodeConfig cDec0)
      (seekConfig_not_halted cSeekH) hSeekHandSucc

  have hToDec :=
    mem_runBranches_trans needExprCompositeMachine
      mS 1 [seekConfig cSeek0]
      (seekConfig cSeekH) (decodeConfig cDec0)
      hS' hSeekHand

  have hDecExact :
      tagDecodeMachine.run 3 cDec0 = cDecH := by
    dsimp [cDec0, cDecH, tRead, tAfterTag]
    simpa [decodeTagBits] using
      tagDecode_run_three witness rest frameStack consumed padding
        false false true

  obtain ⟨mD, hmD, hD⟩ := decode_run_reachable 3 cDec0
  have hD' :
      decodeConfig cDecH ∈
        needExprCompositeMachine.runBranches mD [decodeConfig cDec0] := by
    rw [hDecExact] at hD
    exact hD
  have hThroughDec :=
    mem_runBranches_trans needExprCompositeMachine
      (mS + 1) mD [seekConfig cSeek0]
      (decodeConfig cDec0) (decodeConfig cDecH)
      hToDec hD'

  have hDecHandSucc :
      retValueConfig false cRet0 ∈
        needExprCompositeMachine.successors (decodeConfig cDecH) := by
    rw [constFalse_handoff_successors tAfterTag]
    simp [decodeConfig, retValueConfig, cDecH, cRet0]
  have hDecHand :
      retValueConfig false cRet0 ∈
        needExprCompositeMachine.runBranches 1 [decodeConfig cDecH] :=
    one_step_of_successor
      (decodeConfig cDecH) (retValueConfig false cRet0)
      (decodeConfig_not_halted cDecH) hDecHandSucc
  have hToRet :=
    mem_runBranches_trans needExprCompositeMachine
      ((mS + 1) + mD) 1 [seekConfig cSeek0]
      (decodeConfig cDecH) (retValueConfig false cRet0)
      hThroughDec hDecHand

  have hRetExact :
      cursorReturnMachine.run nRet cRet0 = cRetH := by
    dsimp [nRet, cRet0, cRetH, tAfterTag, tDone]
    exact cursorReturn_preserve_run
      witness (consumed + 3) rest frameStack padding

  obtain ⟨mR, hmR, hR⟩ :=
    retValue_run_reachable false nRet cRet0
  have hR' :
      retValueConfig false cRetH ∈
        needExprCompositeMachine.runBranches mR
          [retValueConfig false cRet0] := by
    rw [hRetExact] at hR
    exact hR
  have hThroughRet :=
    mem_runBranches_trans needExprCompositeMachine
      (((mS + 1) + mD) + 1) mR [seekConfig cSeek0]
      (retValueConfig false cRet0)
      (retValueConfig false cRetH)
      hToRet hR'

  have hFinalSucc :
      cDone ∈
        needExprCompositeMachine.successors
          (retValueConfig false cRetH) := by
    rw [retValue_handoff_successors false tDone]
    simp [cDone, retValueConfig, cRetH]
  have hFinal :
      cDone ∈
        needExprCompositeMachine.runBranches 1
          [retValueConfig false cRetH] :=
    one_step_of_successor
      (retValueConfig false cRetH) cDone
      (retValueConfig_not_halted false cRetH) hFinalSucc

  have hAll :=
    mem_runBranches_trans needExprCompositeMachine
      ((((mS + 1) + mD) + 1) + mR) 1 [seekConfig cSeek0]
      (retValueConfig false cRetH) cDone
      hThroughRet hFinal

  refine ⟨((((mS + 1) + mD) + 1) + mR) + 1, ?_, ?_⟩
  · dsimp [constTagCompositeFuel, nSeek, nRet] at *
    omega
  · dsimp [cDone, tDone, cSeek0, t0] at hAll ⊢
    simpa [seekConfig, needExprCompositeMachine] using hAll

#print axioms MCore.Real.P01NeedExprCompositeRun.constFalse_reaches_done

#print axioms MCore.Real.P01NeedExprCompositeRun.seek_run_reachable
#print axioms MCore.Real.P01NeedExprCompositeRun.decode_run_reachable
#print axioms MCore.Real.P01NeedExprCompositeRun.retValue_run_reachable
#print axioms MCore.Real.P01NeedExprCompositeRun.retPush_run_reachable
#print axioms MCore.Real.P01NeedExprCompositeRun.push_run_reachable

end P01NeedExprCompositeRun
end Real
end MCore
