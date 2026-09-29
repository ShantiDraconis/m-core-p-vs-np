import MCore.Real.P01EvalRunLoopNTM
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01EvalRunLoopRun

open CanonicalFinalProof
open P01NTMRunLaws
open P01EncodedStackEvaluator
open P01EvalCursorMachine
open P01EvalCursorRoundTrip
open P01NeedExprTagDecode
open P01NeedExprCompositeNTM
open P01EvalRunLoopNTM

abbrev LoopConfig :=
  Configuration EvalRunLoopState (Option Bool)

def seekLoopConfig
    (c : Configuration CursorSeekState (Option Bool)) : LoopConfig :=
  { state := .need (.seek c.state), tape := c.tape }

def decodeLoopConfig
    (c : Configuration TagDecodeState (Option Bool)) : LoopConfig :=
  { state := .need (.decode c.state), tape := c.tape }

def retValueLoopConfig
    (value : Bool)
    (c : Configuration CursorReturnState (Option Bool)) : LoopConfig :=
  { state := .need (.retValue value c.state), tape := c.tape }

@[simp] theorem seekLoop_not_halted
    (c : Configuration CursorSeekState (Option Bool)) :
    ¬ Halted evalRunLoopMachine (seekLoopConfig c) := by
  simp [Halted, seekLoopConfig, evalRunLoopMachine]

@[simp] theorem decodeLoop_not_halted
    (c : Configuration TagDecodeState (Option Bool)) :
    ¬ Halted evalRunLoopMachine (decodeLoopConfig c) := by
  simp [Halted, decodeLoopConfig, evalRunLoopMachine]

@[simp] theorem retValueLoop_not_halted
    (value : Bool)
    (c : Configuration CursorReturnState (Option Bool)) :
    ¬ Halted evalRunLoopMachine (retValueLoopConfig value c) := by
  simp [Halted, retValueLoopConfig, evalRunLoopMachine]

theorem seekLoop_successors_active
    (c : Configuration CursorSeekState (Option Bool))
    (h : cursorSeekMachine.halting c.state = false) :
    evalRunLoopMachine.successors (seekLoopConfig c) =
      [seekLoopConfig (cursorSeekMachine.step c)] := by
  unfold NTM.successors
  simp only [seekLoopConfig]
  cases c.state <;>
    simp [evalRunLoopMachine, needExprCompositeMachine,
      needLoopEmbed, cursorSeekMachine, NTM.stepBranch, TM.step,
      Tape.write, Tape.move] at h ⊢

theorem decodeLoop_successors_active
    (c : Configuration TagDecodeState (Option Bool))
    (h : tagDecodeMachine.halting c.state = false) :
    evalRunLoopMachine.successors (decodeLoopConfig c) =
      [decodeLoopConfig (tagDecodeMachine.step c)] := by
  unfold NTM.successors
  simp only [decodeLoopConfig]
  cases c.state <;>
    simp [evalRunLoopMachine, needExprCompositeMachine,
      needLoopEmbed, tagDecodeMachine, NTM.stepBranch, TM.step,
      Tape.write, Tape.move] at h ⊢

theorem retValueLoop_successors_active
    (value : Bool)
    (c : Configuration CursorReturnState (Option Bool))
    (h : cursorReturnMachine.halting c.state = false) :
    evalRunLoopMachine.successors (retValueLoopConfig value c) =
      [retValueLoopConfig value (cursorReturnMachine.step c)] := by
  unfold NTM.successors
  simp only [retValueLoopConfig]
  cases c.state <;>
    simp [evalRunLoopMachine, needExprCompositeMachine,
      needLoopEmbed, cursorReturnMachine, NTM.stepBranch, TM.step,
      Tape.write, Tape.move] at h ⊢

private theorem tm_phase_run_reachable
    {S : Type}
    (M : TM S (Option Bool))
    (embed : Configuration S (Option Bool) → LoopConfig)
    (embed_not_halted :
      ∀ c, ¬ Halted evalRunLoopMachine (embed c))
    (step_successors :
      ∀ c, M.halting c.state = false →
        evalRunLoopMachine.successors (embed c) =
          [embed (M.step c)]) :
    ∀ (n : Nat) (c : Configuration S (Option Bool)),
      ∃ m ≤ n,
        embed (M.run n c) ∈
          evalRunLoopMachine.runBranches m [embed c] := by
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
                evalRunLoopMachine.successors (embed c) := by
            rw [step_successors c hhalt]
            simp
          have hone :
              embed (M.step c) ∈
                evalRunLoopMachine.runBranches 1 [embed c] := by
            have h :=
              mem_runBranches_succ_of_successor
                evalRunLoopMachine 0 [embed c]
                (embed c) (embed (M.step c))
                (by simp [NTM.runBranches])
                (embed_not_halted c) hsucc
            simpa using h
          have htrans :=
            mem_runBranches_trans evalRunLoopMachine
              1 m [embed c]
              (embed (M.step c))
              (embed (M.run n (M.step c)))
              hone hmem
          refine ⟨1 + m, by omega, ?_⟩
          simpa [TM.run, hhalt] using htrans

theorem seekLoop_run_reachable
    (n : Nat)
    (c : Configuration CursorSeekState (Option Bool)) :
    ∃ m ≤ n,
      seekLoopConfig (cursorSeekMachine.run n c) ∈
        evalRunLoopMachine.runBranches m [seekLoopConfig c] :=
  tm_phase_run_reachable
    cursorSeekMachine seekLoopConfig
    seekLoop_not_halted seekLoop_successors_active n c

theorem decodeLoop_run_reachable
    (n : Nat)
    (c : Configuration TagDecodeState (Option Bool)) :
    ∃ m ≤ n,
      decodeLoopConfig (tagDecodeMachine.run n c) ∈
        evalRunLoopMachine.runBranches m [decodeLoopConfig c] :=
  tm_phase_run_reachable
    tagDecodeMachine decodeLoopConfig
    decodeLoop_not_halted decodeLoop_successors_active n c

theorem retValueLoop_run_reachable
    (value : Bool) (n : Nat)
    (c : Configuration CursorReturnState (Option Bool)) :
    ∃ m ≤ n,
      retValueLoopConfig value (cursorReturnMachine.run n c) ∈
        evalRunLoopMachine.runBranches m [retValueLoopConfig value c] :=
  tm_phase_run_reachable
    cursorReturnMachine (retValueLoopConfig value)
    (retValueLoop_not_halted value)
    (retValueLoop_successors_active value) n c

private theorem one_step_of_successor
    (a b : LoopConfig)
    (ha : ¬ Halted evalRunLoopMachine a)
    (hs : b ∈ evalRunLoopMachine.successors a) :
    b ∈ evalRunLoopMachine.runBranches 1 [a] := by
  have h :=
    mem_runBranches_succ_of_successor
      evalRunLoopMachine 0 [a] a b
      (by simp [NTM.runBranches]) ha hs
  simpa using h

def constLoopFuel
    (frameStack rest : BitString) : Nat :=
  (frameStack.length + (rest.length + 3) + 3) +
    1 + 3 + 1 +
    (rest.length + frameStack.length + 2) + 1

/-- Generic physical loop route for constant tags 001/010. -/
theorem constTag_loop_reaches_have
    (witness rest frameStack : BitString)
    (consumed padding : Nat)
    (b0 b1 b2 value : Bool)
    (tag : NeedExprTag)
    (hdecode : decodeTagBits b0 b1 b2 = tag)
    (hhandoff :
      ∀ tape : Tape (Option Bool),
        needExprCompositeMachine.successors
          { state := .decode (.halt tag), tape := tape } =
          [{ state := .retValue value .scanUnread, tape := tape }]) :
    ∃ m ≤ constLoopFuel frameStack rest,
      ({ state := .have (.start value),
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest frameStack padding } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .need needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (b0 :: b1 :: b2 :: rest)
                 frameStack padding }] := by
  let nSeek := frameStack.length + (rest.length + 3) + 3
  let nRet := rest.length + frameStack.length + 2
  let t0 :=
    evalCursorStackEndTape witness consumed
      (b0 :: b1 :: b2 :: rest) frameStack padding
  let tRead :=
    evalCursorReadTape witness consumed
      (b0 :: b1 :: b2 :: rest) frameStack padding
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
    { state := .halt tag, tape := tAfterTag }
  let cRet0 : Configuration CursorReturnState (Option Bool) :=
    { state := .scanUnread, tape := tAfterTag }
  let cRetH : Configuration CursorReturnState (Option Bool) :=
    { state := .halt, tape := tDone }

  have hSeekExact :
      cursorSeekMachine.run nSeek cSeek0 = cSeekH := by
    dsimp [nSeek, cSeek0, cSeekH, t0, tRead]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      cursorSeek_run witness consumed
        (b0 :: b1 :: b2 :: rest) frameStack padding
  obtain ⟨mS, hmS, hS⟩ := seekLoop_run_reachable nSeek cSeek0
  have hS' :
      seekLoopConfig cSeekH ∈
        evalRunLoopMachine.runBranches mS [seekLoopConfig cSeek0] := by
    rw [hSeekExact] at hS
    exact hS

  have hSeekHandSucc :
      decodeLoopConfig cDec0 ∈
        evalRunLoopMachine.successors (seekLoopConfig cSeekH) := by
    dsimp [seekLoopConfig, decodeLoopConfig, cSeekH, cDec0]
    simp [evalRunLoopMachine, needExprCompositeMachine, needLoopEmbed,
      NTM.successors, NTM.stepBranch, Tape.write, Tape.move]
  have hSeekHand :
      decodeLoopConfig cDec0 ∈
        evalRunLoopMachine.runBranches 1 [seekLoopConfig cSeekH] :=
    one_step_of_successor
      (seekLoopConfig cSeekH) (decodeLoopConfig cDec0)
      (seekLoop_not_halted cSeekH) hSeekHandSucc
  have hToDec :=
    mem_runBranches_trans evalRunLoopMachine
      mS 1 [seekLoopConfig cSeek0]
      (seekLoopConfig cSeekH) (decodeLoopConfig cDec0)
      hS' hSeekHand

  have hDecExact :
      tagDecodeMachine.run 3 cDec0 = cDecH := by
    dsimp [cDec0, cDecH, tRead, tAfterTag]
    simpa [hdecode] using
      tagDecode_run_three witness rest frameStack consumed padding
        b0 b1 b2
  obtain ⟨mD, hmD, hD⟩ := decodeLoop_run_reachable 3 cDec0
  have hD' :
      decodeLoopConfig cDecH ∈
        evalRunLoopMachine.runBranches mD [decodeLoopConfig cDec0] := by
    rw [hDecExact] at hD
    exact hD
  have hThroughDec :=
    mem_runBranches_trans evalRunLoopMachine
      (mS + 1) mD [seekLoopConfig cSeek0]
      (decodeLoopConfig cDec0) (decodeLoopConfig cDecH)
      hToDec hD'

  have hDecHandSucc :
      retValueLoopConfig value cRet0 ∈
        evalRunLoopMachine.successors (decodeLoopConfig cDecH) := by
    dsimp [decodeLoopConfig, retValueLoopConfig, cDecH, cRet0]
    have hsrc := hhandoff tAfterTag
    simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
      Tape.write, Tape.move] at hsrc
    simp [evalRunLoopMachine, needExprCompositeMachine, needLoopEmbed,
      NTM.successors, NTM.stepBranch, hdecode,
      Tape.write, Tape.move]
  have hDecHand :
      retValueLoopConfig value cRet0 ∈
        evalRunLoopMachine.runBranches 1 [decodeLoopConfig cDecH] :=
    one_step_of_successor
      (decodeLoopConfig cDecH) (retValueLoopConfig value cRet0)
      (decodeLoop_not_halted cDecH) hDecHandSucc
  have hToRet :=
    mem_runBranches_trans evalRunLoopMachine
      ((mS + 1) + mD) 1 [seekLoopConfig cSeek0]
      (decodeLoopConfig cDecH) (retValueLoopConfig value cRet0)
      hThroughDec hDecHand

  have hRetExact :
      cursorReturnMachine.run nRet cRet0 = cRetH := by
    dsimp [nRet, cRet0, cRetH, tAfterTag, tDone]
    exact cursorReturn_preserve_run
      witness (consumed + 3) rest frameStack padding
  obtain ⟨mR, hmR, hR⟩ :=
    retValueLoop_run_reachable value nRet cRet0
  have hR' :
      retValueLoopConfig value cRetH ∈
        evalRunLoopMachine.runBranches mR
          [retValueLoopConfig value cRet0] := by
    rw [hRetExact] at hR
    exact hR
  have hThroughRet :=
    mem_runBranches_trans evalRunLoopMachine
      (((mS + 1) + mD) + 1) mR [seekLoopConfig cSeek0]
      (retValueLoopConfig value cRet0)
      (retValueLoopConfig value cRetH)
      hToRet hR'

  let cHave : LoopConfig :=
    { state := .have (.start value), tape := tDone }
  have hFinalSucc :
      cHave ∈
        evalRunLoopMachine.successors
          (retValueLoopConfig value cRetH) := by
    dsimp [cHave, retValueLoopConfig, cRetH]
    simp [evalRunLoopMachine, needExprCompositeMachine,
      NTM.successors, NTM.stepBranch, Tape.write, Tape.move]
  have hFinal :
      cHave ∈
        evalRunLoopMachine.runBranches 1
          [retValueLoopConfig value cRetH] :=
    one_step_of_successor
      (retValueLoopConfig value cRetH) cHave
      (retValueLoop_not_halted value cRetH) hFinalSucc

  have hAll :=
    mem_runBranches_trans evalRunLoopMachine
      ((((mS + 1) + mD) + 1) + mR) 1
      [seekLoopConfig cSeek0]
      (retValueLoopConfig value cRetH) cHave
      hThroughRet hFinal

  refine ⟨(((((mS + 1) + mD) + 1) + mR) + 1), ?_, ?_⟩
  · dsimp [constLoopFuel, nSeek, nRet] at *
    omega
  · dsimp [cHave, tDone, cSeek0, t0] at hAll ⊢
    simpa [seekLoopConfig, needExprCompositeMachine] using hAll

theorem constFalse_loop_reaches_have
    (witness rest frameStack : BitString)
    (consumed padding : Nat) :
    ∃ m ≤ constLoopFuel frameStack rest,
      ({ state := .have (.start false),
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest frameStack padding } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .need needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (false :: false :: true :: rest)
                 frameStack padding }] := by
  apply constTag_loop_reaches_have
    witness rest frameStack consumed padding
      false false true false .constFalse
  · rfl
  · exact constFalse_handoff_successors

theorem constTrue_loop_reaches_have
    (witness rest frameStack : BitString)
    (consumed padding : Nat) :
    ∃ m ≤ constLoopFuel frameStack rest,
      ({ state := .have (.start true),
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest frameStack padding } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .need needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (false :: true :: false :: rest)
                 frameStack padding }] := by
  apply constTag_loop_reaches_have
    witness rest frameStack consumed padding
      false true false true .constTrue
  · rfl
  · exact constTrue_handoff_successors

#print axioms MCore.Real.P01EvalRunLoopRun.constTag_loop_reaches_have
#print axioms MCore.Real.P01EvalRunLoopRun.constFalse_loop_reaches_have
#print axioms MCore.Real.P01EvalRunLoopRun.constTrue_loop_reaches_have

end P01EvalRunLoopRun
end Real
end MCore
