import MCore.Real.P01EvalCursorMachine
import MCore.Real.P01EvalCursorRoundTrip
import MCore.Real.P01EvalFramePushMachine
import MCore.Real.P01NeedExprTagDecode
import MCore.Real.P01InputNodeCompositeNTM

namespace MCore
namespace Real
namespace P01NeedExprCompositeNTM

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EvalCursorMachine
open P01EvalCursorRoundTrip
open P01EvalFramePushMachine
open P01NeedExprTagDecode
open P01InputNodeCompositeNTM

/-- Finite control for one complete physical `needExpr` evaluator step.

The six valid prefix tags share the same physical seek and 3-bit decoder.
After decoding:
* 000 enters the already-certified indexed-input composite;
* 001/010 preserve-return and finish with a Boolean value;
* 011/100/101 preserve-return, push one continuation frame, and finish in
  `needExpr` mode;
* 110/111 reject.

All dynamic source/witness/frame data remains on tape; finite control carries
only finite tags, frames, Booleans, and submachine states. -/
inductive NeedExprCompositeState where
  | seek : CursorSeekState → NeedExprCompositeState
  | decode : TagDecodeState → NeedExprCompositeState
  | input : InputNodeCompositeState → NeedExprCompositeState
  | retValue : Bool → CursorReturnState → NeedExprCompositeState
  | retPush : EvalFrame → CursorReturnState → NeedExprCompositeState
  | push : EvalFrame → FramePushState → NeedExprCompositeState
  | doneValue : Bool → NeedExprCompositeState
  | doneNeed
  | reject
  deriving DecidableEq, Repr

/-- One fixed NTM implementing all six valid `needExpr` tag cases. -/
def needExprCompositeMachine :
    NTM NeedExprCompositeState (Option Bool) where
  initial := .seek cursorSeekMachine.initial
  blank := none
  transition := fun q symbol =>
    match q with
    | .seek qs =>
        match qs with
        | .halt =>
            [(.decode tagDecodeMachine.initial, symbol, .stay)]
        | .reject => []
        | _ =>
            let t := cursorSeekMachine.transition qs symbol
            [(.seek t.1, t.2.1, t.2.2)]
    | .decode qd =>
        match qd with
        | .halt tag =>
            match tag with
            | .input =>
                [(.input inputNodeCompositeMachine.initial, symbol, .stay)]
            | .constFalse =>
                [(.retValue false .scanUnread, symbol, .stay)]
            | .constTrue =>
                [(.retValue true .scanUnread, symbol, .stay)]
            | .neg =>
                [(.retPush .neg .scanUnread, symbol, .stay)]
            | .and =>
                [(.retPush .andLeft .scanUnread, symbol, .stay)]
            | .or =>
                [(.retPush .orLeft .scanUnread, symbol, .stay)]
            | .invalid110 => []
            | .invalid111 => []
        | .reject => []
        | _ =>
            let t := tagDecodeMachine.transition qd symbol
            [(.decode t.1, t.2.1, t.2.2)]
    | .input qi =>
        match qi with
        | .done selected _mode =>
            [(.doneValue selected, symbol, .stay)]
        | .reject => []
        | _ =>
            (inputNodeCompositeMachine.transition qi symbol).map
              (fun t => (.input t.1, t.2.1, t.2.2))
    | .retValue value qr =>
        match qr with
        | .halt =>
            [(.doneValue value, symbol, .stay)]
        | .reject => []
        | _ =>
            let t := cursorReturnMachine.transition qr symbol
            [(.retValue value t.1, t.2.1, t.2.2)]
    | .retPush frame qr =>
        match qr with
        | .halt =>
            [(.push frame (.start frame), symbol, .stay)]
        | .reject => []
        | _ =>
            let t := cursorReturnMachine.transition qr symbol
            [(.retPush frame t.1, t.2.1, t.2.2)]
    | .push frame qp =>
        match qp with
        | .halt =>
            [(.doneNeed, symbol, .stay)]
        | .reject => []
        | _ =>
            let t := framePushMachine.transition qp symbol
            [(.push frame t.1, t.2.1, t.2.2)]
    | .doneValue _ => []
    | .doneNeed => []
    | .reject => []
  accepting := fun q =>
    match q with
    | .doneValue _ => true
    | .doneNeed => true
    | _ => false
  rejecting := fun q =>
    match q with
    | .reject => true
    | _ => false

@[simp] theorem needExprCompositeMachine_initial :
    needExprCompositeMachine.initial =
      .seek cursorSeekMachine.initial := rfl

@[simp] theorem needExprCompositeMachine_blank :
    needExprCompositeMachine.blank = none := rfl

@[simp] theorem needExprCompositeMachine_accepting_value (b : Bool) :
    needExprCompositeMachine.accepting (.doneValue b) = true := rfl

@[simp] theorem needExprCompositeMachine_accepting_need :
    needExprCompositeMachine.accepting .doneNeed = true := rfl

/-- Cursor-seek completion hands the unchanged tape to the tag decoder. -/
theorem seek_handoff_successors
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .seek .halt, tape := tape } =
      [{ state := .decode tagDecodeMachine.initial, tape := tape }] := by
  simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

/-- The physical input tag dispatches to the already-certified input-node
composite without changing the tape. -/
theorem input_tag_handoff_successors
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .decode (.halt .input), tape := tape } =
      [{ state := .input inputNodeCompositeMachine.initial, tape := tape }] := by
  simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem constFalse_handoff_successors
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .decode (.halt .constFalse), tape := tape } =
      [{ state := .retValue false .scanUnread, tape := tape }] := by
  simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem constTrue_handoff_successors
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .decode (.halt .constTrue), tape := tape } =
      [{ state := .retValue true .scanUnread, tape := tape }] := by
  simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem neg_handoff_successors
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .decode (.halt .neg), tape := tape } =
      [{ state := .retPush .neg .scanUnread, tape := tape }] := by
  simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem and_handoff_successors
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .decode (.halt .and), tape := tape } =
      [{ state := .retPush .andLeft .scanUnread, tape := tape }] := by
  simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem or_handoff_successors
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .decode (.halt .or), tape := tape } =
      [{ state := .retPush .orLeft .scanUnread, tape := tape }] := by
  simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

/-- Invalid tag patterns have no successor. -/
theorem invalid110_rejects
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .decode (.halt .invalid110), tape := tape } = [] := by
  simp [needExprCompositeMachine, NTM.successors]

theorem invalid111_rejects
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .decode (.halt .invalid111), tape := tape } = [] := by
  simp [needExprCompositeMachine, NTM.successors]

#print axioms MCore.Real.P01NeedExprCompositeNTM.seek_handoff_successors
#print axioms MCore.Real.P01NeedExprCompositeNTM.input_tag_handoff_successors
#print axioms MCore.Real.P01NeedExprCompositeNTM.constFalse_handoff_successors
#print axioms MCore.Real.P01NeedExprCompositeNTM.neg_handoff_successors
#print axioms MCore.Real.P01NeedExprCompositeNTM.invalid110_rejects

end P01NeedExprCompositeNTM
end Real
end MCore
