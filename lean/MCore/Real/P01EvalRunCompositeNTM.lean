import MCore.Real.P01EvalStepSemanticRefinement

namespace MCore
namespace Real
namespace P01EvalRunCompositeNTM

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01HaveValueCompositeNTM
open P01EvalStepCompositeNTM
open P01NTMRunLaws

/-- Physical controller for repeated evaluator steps.

A completed need-expression step restarts the need arm immediately.
A completed value step first inspects the physical continuation stack:
* empty stack -> final Boolean result;
* nonempty stack -> restore the stack-end head and restart the haveValue arm.
-/
inductive EvalRunCompositeState where
  | step : EvalStepCompositeState → EvalRunCompositeState
  | valueStart : Bool → EvalRunCompositeState
  | valuePeek : Bool → EvalRunCompositeState
  | valueReturn : Bool → EvalRunCompositeState
  | final : Bool → EvalRunCompositeState
  | reject
  deriving DecidableEq, Repr

/-- Terminal-depromoting embedding used between macro evaluator steps. -/
def evalRunStateEmbed : EvalStepCompositeState → EvalRunCompositeState
  | .doneNeed =>
      .step (.need needExprCompositeMachine.initial)
  | .doneValue v =>
      .valueStart v
  | .reject =>
      .reject
  | q =>
      .step q

def evalRunCompositeMachine :
    NTM EvalRunCompositeState (Option Bool) where
  initial := .step (.need needExprCompositeMachine.initial)
  blank := none
  transition := fun q symbol =>
    match q with
    | .step qs =>
        (evalStepCompositeMachine.transition qs symbol).map
          (fun t => (evalRunStateEmbed t.1, t.2.1, t.2.2))
    | .valueStart v =>
        match symbol with
        | none => [(.valuePeek v, none, .left)]
        | some b => [(.reject, some b, .stay)]
    | .valuePeek v =>
        match symbol with
        | none => [(.final v, none, .right)]
        | some b => [(.valueReturn v, some b, .right)]
    | .valueReturn v =>
        match symbol with
        | none => [(.step (.have (.start v)), none, .stay)]
        | some b => [(.reject, some b, .stay)]
    | .final _ => []
    | .reject => []
  accepting := fun q =>
    match q with
    | .final true => true
    | _ => false
  rejecting := fun q =>
    match q with
    | .final false => true
    | .reject => true
    | _ => false

@[simp] theorem evalRunCompositeMachine_initial :
    evalRunCompositeMachine.initial =
      .step (.need needExprCompositeMachine.initial) := rfl

@[simp] theorem evalRunCompositeMachine_blank :
    evalRunCompositeMachine.blank = none := rfl

@[simp] theorem embed_doneNeed :
    evalRunStateEmbed .doneNeed =
      .step (.need needExprCompositeMachine.initial) := rfl

@[simp] theorem embed_doneValue (v : Bool) :
    evalRunStateEmbed (.doneValue v) = .valueStart v := rfl

@[simp] theorem accepting_final_true :
    evalRunCompositeMachine.accepting (.final true) = true := rfl

@[simp] theorem rejecting_final_false :
    evalRunCompositeMachine.rejecting (.final false) = true := rfl

@[simp] theorem rejecting_reject :
    evalRunCompositeMachine.rejecting .reject = true := rfl

/-- On active evalStep states, the evalRun controller has exactly the same
physical successors, with terminal targets converted to restart states. -/
theorem step_successors
    (q : EvalStepCompositeState)
    (tape : Tape (Option Bool)) :
    evalRunCompositeMachine.successors
      { state := .step q, tape := tape } =
    (evalStepCompositeMachine.successors
      { state := q, tape := tape }).map
        (fun c =>
          ({ state := evalRunStateEmbed c.state, tape := c.tape } :
            Configuration EvalRunCompositeState (Option Bool))) := by
  simp [NTM.successors, NTM.stepBranch,
    evalRunCompositeMachine, evalStepCompositeMachine,
    Tape.write, Tape.move, List.map_map, Function.comp_def]

private theorem one_step_of_successor
    (a b : Configuration EvalRunCompositeState (Option Bool))
    (ha : ¬ P01NTMRunLaws.Halted evalRunCompositeMachine a)
    (hs : b ∈ evalRunCompositeMachine.successors a) :
    b ∈ evalRunCompositeMachine.runBranches 1 [a] := by
  have h :=
    P01NTMRunLaws.mem_runBranches_succ_of_successor
      evalRunCompositeMachine 0 [a] a b
      (by simp [NTM.runBranches]) ha hs
  simpa using h

/-- A completed value with no continuation frame reaches a physical final
result in two controller steps.  The original stack-end tape is restored. -/
theorem value_empty_frames_run_two
    (witness unread : BitString)
    (consumed padding : Nat)
    (v : Bool) :
    ({ state := .final v,
       tape :=
         evalCursorStackEndTape witness consumed unread [] padding } :
      Configuration EvalRunCompositeState (Option Bool)) ∈
    evalRunCompositeMachine.runBranches 2
      [{ state := .valueStart v,
         tape :=
           evalCursorStackEndTape witness consumed unread [] padding }] := by
  let t0 :=
    evalCursorStackEndTape witness consumed unread [] padding
  let t1 := Tape.move none .left t0
  let c0 : Configuration EvalRunCompositeState (Option Bool) :=
    { state := .valueStart v, tape := t0 }
  let c1 : Configuration EvalRunCompositeState (Option Bool) :=
    { state := .valuePeek v, tape := t1 }
  let c2 : Configuration EvalRunCompositeState (Option Bool) :=
    { state := .final v, tape := t0 }

  have h01succ :
      c1 ∈ evalRunCompositeMachine.successors c0 := by
    dsimp [c0, c1, t1, t0]
    simp [NTM.successors, NTM.stepBranch,
      evalRunCompositeMachine, evalCursorStackEndTape,
      Tape.write, Tape.move]
  have h01 :
      c1 ∈ evalRunCompositeMachine.runBranches 1 [c0] :=
    one_step_of_successor c0 c1
      (by simp [P01NTMRunLaws.Halted, c0, evalRunCompositeMachine]) h01succ

  have h12succ :
      c2 ∈ evalRunCompositeMachine.successors c1 := by
    dsimp [c1, c2, t1, t0]
    simp [NTM.successors, NTM.stepBranch,
      evalRunCompositeMachine, evalCursorStackEndTape,
      Tape.write, Tape.move]
  have h12 :
      c2 ∈ evalRunCompositeMachine.runBranches 1 [c1] :=
    one_step_of_successor c1 c2
      (by simp [P01NTMRunLaws.Halted, c1, evalRunCompositeMachine]) h12succ

  have h :=
    P01NTMRunLaws.mem_runBranches_trans evalRunCompositeMachine
      1 1 [c0] c1 c2 h01 h12
  dsimp [c0, c2, t0] at h ⊢
  simpa using h

/-- A completed value with a nonempty continuation stack is restored to the
canonical stack-end tape and re-enters the haveValue arm after three fixed
controller steps. -/
theorem value_nonempty_frames_run_three
    (witness unread frameTail : BitString)
    (consumed padding : Nat)
    (v b : Bool) :
    ({ state := .step (.have (.start v)),
       tape :=
         evalCursorStackEndTape witness consumed unread
           (b :: frameTail) padding } :
      Configuration EvalRunCompositeState (Option Bool)) ∈
    evalRunCompositeMachine.runBranches 3
      [{ state := .valueStart v,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (b :: frameTail) padding }] := by
  let t0 :=
    evalCursorStackEndTape witness consumed unread
      (b :: frameTail) padding
  let t1 := Tape.move none .left t0
  let c0 : Configuration EvalRunCompositeState (Option Bool) :=
    { state := .valueStart v, tape := t0 }
  let c1 : Configuration EvalRunCompositeState (Option Bool) :=
    { state := .valuePeek v, tape := t1 }
  let c2 : Configuration EvalRunCompositeState (Option Bool) :=
    { state := .valueReturn v, tape := t0 }
  let c3 : Configuration EvalRunCompositeState (Option Bool) :=
    { state := .step (.have (.start v)), tape := t0 }

  have h01succ :
      c1 ∈ evalRunCompositeMachine.successors c0 := by
    dsimp [c0, c1, t1, t0]
    simp [NTM.successors, NTM.stepBranch,
      evalRunCompositeMachine, evalCursorStackEndTape,
      Tape.write, Tape.move]
  have h01 :
      c1 ∈ evalRunCompositeMachine.runBranches 1 [c0] :=
    one_step_of_successor c0 c1
      (by simp [P01NTMRunLaws.Halted, c0, evalRunCompositeMachine]) h01succ

  have h12succ :
      c2 ∈ evalRunCompositeMachine.successors c1 := by
    dsimp [c1, c2, t1, t0]
    simp [NTM.successors, NTM.stepBranch,
      evalRunCompositeMachine, evalCursorStackEndTape,
      Tape.write, Tape.move]
  have h12 :
      c2 ∈ evalRunCompositeMachine.runBranches 1 [c1] :=
    one_step_of_successor c1 c2
      (by simp [P01NTMRunLaws.Halted, c1, evalRunCompositeMachine]) h12succ

  have h23succ :
      c3 ∈ evalRunCompositeMachine.successors c2 := by
    dsimp [c2, c3, t0]
    simp [NTM.successors, NTM.stepBranch,
      evalRunCompositeMachine, evalCursorStackEndTape,
      Tape.write, Tape.move]
  have h23 :
      c3 ∈ evalRunCompositeMachine.runBranches 1 [c2] :=
    one_step_of_successor c2 c3
      (by simp [P01NTMRunLaws.Halted, c2, evalRunCompositeMachine]) h23succ

  have h02 :=
    P01NTMRunLaws.mem_runBranches_trans evalRunCompositeMachine
      1 1 [c0] c1 c2 h01 h12
  have h03 :=
    P01NTMRunLaws.mem_runBranches_trans evalRunCompositeMachine
      2 1 [c0] c2 c3 h02 h23
  dsimp [c0, c3, t0] at h03 ⊢
  simpa using h03

/-- Every encoded evaluator frame is physically nonempty, so the previous
dispatcher theorem applies directly to semantic frame stacks. -/
theorem value_encoded_frame_run_three
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (v : Bool) (frame : EvalFrame) :
    ({ state := .step (.have (.start v)),
       tape :=
         evalCursorStackEndTape witness consumed unread
           (encodeEvalFrame frame ++ frameStack) padding } :
      Configuration EvalRunCompositeState (Option Bool)) ∈
    evalRunCompositeMachine.runBranches 3
      [{ state := .valueStart v,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame frame ++ frameStack) padding }] := by
  cases frame with
  | neg =>
      simpa [encodeEvalFrame] using
        value_nonempty_frames_run_three
          witness unread ([false, false] ++ frameStack)
          consumed padding v false
  | andLeft =>
      simpa [encodeEvalFrame] using
        value_nonempty_frames_run_three
          witness unread ([false, true] ++ frameStack)
          consumed padding v false
  | andRight b =>
      cases b with
      | false =>
          simpa [encodeEvalFrame] using
            value_nonempty_frames_run_three
              witness unread ([true, false] ++ frameStack)
              consumed padding v false
      | true =>
          simpa [encodeEvalFrame] using
            value_nonempty_frames_run_three
              witness unread ([true, true] ++ frameStack)
              consumed padding v false
  | orLeft =>
      simpa [encodeEvalFrame] using
        value_nonempty_frames_run_three
          witness unread ([false, false] ++ frameStack)
          consumed padding v true
  | orRight b =>
      cases b with
      | false =>
          simpa [encodeEvalFrame] using
            value_nonempty_frames_run_three
              witness unread ([false, true] ++ frameStack)
              consumed padding v true
      | true =>
          simpa [encodeEvalFrame] using
            value_nonempty_frames_run_three
              witness unread ([true, false] ++ frameStack)
              consumed padding v true

#print axioms MCore.Real.P01EvalRunCompositeNTM.step_successors
#print axioms MCore.Real.P01EvalRunCompositeNTM.value_empty_frames_run_two
#print axioms MCore.Real.P01EvalRunCompositeNTM.value_nonempty_frames_run_three
#print axioms MCore.Real.P01EvalRunCompositeNTM.value_encoded_frame_run_three

end P01EvalRunCompositeNTM
end Real
end MCore
