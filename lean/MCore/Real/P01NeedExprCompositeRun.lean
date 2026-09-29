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

#print axioms MCore.Real.P01NeedExprCompositeRun.seek_run_reachable
#print axioms MCore.Real.P01NeedExprCompositeRun.decode_run_reachable
#print axioms MCore.Real.P01NeedExprCompositeRun.retValue_run_reachable
#print axioms MCore.Real.P01NeedExprCompositeRun.retPush_run_reachable
#print axioms MCore.Real.P01NeedExprCompositeRun.push_run_reachable

end P01NeedExprCompositeRun
end Real
end MCore
