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

/-- A completed value with no continuation frame is a physical final result.
The two lookahead moves restore the exact original stack-end tape. -/
theorem value_empty_frames_run_two
    (witness unread : BitString)
    (consumed padding : Nat)
    (v : Bool) :
    evalRunCompositeMachine.runBranches 2
      [{ state := .valueStart v,
         tape :=
           evalCursorStackEndTape witness consumed unread [] padding }] =
      [{ state := .final v,
         tape :=
           evalCursorStackEndTape witness consumed unread [] padding }] := by
  cases v <;>
    simp [NTM.runBranches, evalRunCompositeMachine,
      evalCursorStackEndTape, Tape.write, Tape.move]

/-- A completed value with a nonempty continuation stack is restored to the
canonical stack-end tape and re-enters the haveValue arm after three fixed
controller steps. -/
theorem value_nonempty_frames_run_three
    (witness unread frameTail : BitString)
    (consumed padding : Nat)
    (v b : Bool) :
    evalRunCompositeMachine.runBranches 3
      [{ state := .valueStart v,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (b :: frameTail) padding }] =
      [{ state := .step (.have (.start v)),
         tape :=
           evalCursorStackEndTape witness consumed unread
             (b :: frameTail) padding }] := by
  cases v <;> cases b <;>
    simp [NTM.runBranches, evalRunCompositeMachine,
      evalCursorStackEndTape, Tape.write, Tape.move]

/-- Every encoded evaluator frame is physically nonempty, so the previous
dispatcher theorem applies directly to semantic frame stacks. -/
theorem value_encoded_frame_run_three
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (v : Bool) (frame : EvalFrame) :
    evalRunCompositeMachine.runBranches 3
      [{ state := .valueStart v,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame frame ++ frameStack) padding }] =
      [{ state := .step (.have (.start v)),
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame frame ++ frameStack) padding }] := by
  rw [encodeEvalFrame_eq_bits]
  exact value_nonempty_frames_run_three
    witness unread
      ((frameBit1 frame :: frameBit2 frame :: []) ++ frameStack)
      consumed padding v (frameBit0 frame)

#print axioms MCore.Real.P01EvalRunCompositeNTM.step_successors
#print axioms MCore.Real.P01EvalRunCompositeNTM.value_empty_frames_run_two
#print axioms MCore.Real.P01EvalRunCompositeNTM.value_nonempty_frames_run_three
#print axioms MCore.Real.P01EvalRunCompositeNTM.value_encoded_frame_run_three

end P01EvalRunCompositeNTM
end Real
end MCore
