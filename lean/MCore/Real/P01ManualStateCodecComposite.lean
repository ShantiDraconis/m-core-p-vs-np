set_option maxRecDepth 10000 in
import MCore.Real.P01ManualStateCodecBase
import MCore.Real.P01CheckedVerifierCompositeNTM

namespace MCore
namespace Real
namespace P01ManualStateCodecComposite

open P01VerifierStateCode
open P01ManualStateCodecBase

def frameCursorCode
    (f : P01EncodedStackEvaluator.EvalFrame)
    (q : P01EvalCursorRoundTrip.CursorReturnState) : Nat :=
  evalFrameCode f * 5 + cursorReturnCode q

def frameCursorDecode (n : Nat) :
    P01EncodedStackEvaluator.EvalFrame × P01EvalCursorRoundTrip.CursorReturnState :=
  if n < 5 then (.neg, cursorReturnDecode n)
  else if n < 10 then (.andLeft, cursorReturnDecode (n - 5))
  else if n < 15 then (.andRight false, cursorReturnDecode (n - 10))
  else if n < 20 then (.andRight true, cursorReturnDecode (n - 15))
  else if n < 25 then (.orLeft, cursorReturnDecode (n - 20))
  else if n < 30 then (.orRight false, cursorReturnDecode (n - 25))
  else (.orRight true, cursorReturnDecode (n - 30))

@[simp] theorem frameCursorDecode_code
    (f : P01EncodedStackEvaluator.EvalFrame)
    (q : P01EvalCursorRoundTrip.CursorReturnState) :
    frameCursorDecode (frameCursorCode f q) = (f, q) := by
  have h := cursorReturnCode_lt q
  cases f with
  | neg => simp [frameCursorDecode, frameCursorCode, evalFrameCode, cursorReturnDecode_code, Nat.add_sub_cancel_left]; omega
  | andLeft => simp [frameCursorDecode, frameCursorCode, evalFrameCode, cursorReturnDecode_code, Nat.add_sub_cancel_left]; omega
  | andRight b =>
      cases b <;> simp [frameCursorDecode, frameCursorCode, evalFrameCode, cursorReturnDecode_code, Nat.add_sub_cancel_left] <;> omega
  | orLeft => simp [frameCursorDecode, frameCursorCode, evalFrameCode, cursorReturnDecode_code, Nat.add_sub_cancel_left]; omega
  | orRight b =>
      cases b <;> simp [frameCursorDecode, frameCursorCode, evalFrameCode, cursorReturnDecode_code, Nat.add_sub_cancel_left] <;> omega

theorem frameCursorCode_lt
    (f : P01EncodedStackEvaluator.EvalFrame)
    (q : P01EvalCursorRoundTrip.CursorReturnState) :
    frameCursorCode f q < 35 := by
  have h := cursorReturnCode_lt q
  cases f with
  | neg => simp [frameCursorCode, evalFrameCode]; omega
  | andLeft => simp [frameCursorCode, evalFrameCode]; omega
  | andRight b => cases b <;> simp [frameCursorCode, evalFrameCode] <;> omega
  | orLeft => simp [frameCursorCode, evalFrameCode]; omega
  | orRight b => cases b <;> simp [frameCursorCode, evalFrameCode] <;> omega

def framePushPairCode
    (f : P01EncodedStackEvaluator.EvalFrame)
    (q : P01EvalFramePushMachine.FramePushState) : Nat :=
  evalFrameCode f * 23 + framePushCode q

def framePushPairDecode (n : Nat) :
    P01EncodedStackEvaluator.EvalFrame × P01EvalFramePushMachine.FramePushState :=
  if n < 23 then (.neg, framePushDecode n)
  else if n < 46 then (.andLeft, framePushDecode (n - 23))
  else if n < 69 then (.andRight false, framePushDecode (n - 46))
  else if n < 92 then (.andRight true, framePushDecode (n - 69))
  else if n < 115 then (.orLeft, framePushDecode (n - 92))
  else if n < 138 then (.orRight false, framePushDecode (n - 115))
  else (.orRight true, framePushDecode (n - 138))

@[simp] theorem framePushPairDecode_code
    (f : P01EncodedStackEvaluator.EvalFrame)
    (q : P01EvalFramePushMachine.FramePushState) :
    framePushPairDecode (framePushPairCode f q) = (f, q) := by
  have h := framePushCode_lt q
  cases f with
  | neg => simp [framePushPairDecode, framePushPairCode, evalFrameCode, framePushDecode_code, Nat.add_sub_cancel_left]; omega
  | andLeft => simp [framePushPairDecode, framePushPairCode, evalFrameCode, framePushDecode_code, Nat.add_sub_cancel_left]; omega
  | andRight b =>
      cases b <;> simp [framePushPairDecode, framePushPairCode, evalFrameCode, framePushDecode_code, Nat.add_sub_cancel_left] <;> omega
  | orLeft => simp [framePushPairDecode, framePushPairCode, evalFrameCode, framePushDecode_code, Nat.add_sub_cancel_left]; omega
  | orRight b =>
      cases b <;> simp [framePushPairDecode, framePushPairCode, evalFrameCode, framePushDecode_code, Nat.add_sub_cancel_left] <;> omega

theorem framePushPairCode_lt
    (f : P01EncodedStackEvaluator.EvalFrame)
    (q : P01EvalFramePushMachine.FramePushState) :
    framePushPairCode f q < 161 := by
  have h := framePushCode_lt q
  cases f with
  | neg => simp [framePushPairCode, evalFrameCode]; omega
  | andLeft => simp [framePushPairCode, evalFrameCode]; omega
  | andRight b => cases b <;> simp [framePushPairCode, evalFrameCode] <;> omega
  | orLeft => simp [framePushPairCode, evalFrameCode]; omega
  | orRight b => cases b <;> simp [framePushPairCode, evalFrameCode] <;> omega

def needExprStateCount : Nat := 401

def needExprCode : P01NeedExprCompositeNTM.NeedExprCompositeState → Nat
  | .seek q => cursorSeekCode q
  | .decode q => 5 + tagDecodeStateCode q
  | .input q => 21 + inputNodeCode q
  | .retValue false q => 191 + cursorReturnCode q
  | .retValue true q => 196 + cursorReturnCode q
  | .retPush f q => 201 + frameCursorCode f q
  | .push f q => 236 + framePushPairCode f q
  | .doneValue false => 397
  | .doneValue true => 398
  | .doneNeed => 399
  | .reject => 400

def needExprDecode (n : Nat) : P01NeedExprCompositeNTM.NeedExprCompositeState :=
  if n < 5 then .seek (cursorSeekDecode n)
  else if n < 21 then .decode (tagDecodeStateDecode (n - 5))
  else if n < 191 then .input (inputNodeDecode (n - 21))
  else if n < 196 then .retValue false (cursorReturnDecode (n - 191))
  else if n < 201 then .retValue true (cursorReturnDecode (n - 196))
  else if n < 236 then
    let p := frameCursorDecode (n - 201)
    .retPush p.1 p.2
  else if n < 397 then
    let p := framePushPairDecode (n - 236)
    .push p.1 p.2
  else if n = 397 then .doneValue false
  else if n = 398 then .doneValue true
  else if n = 399 then .doneNeed
  else .reject

@[simp] theorem needExprDecode_code
    (q : P01NeedExprCompositeNTM.NeedExprCompositeState) :
    needExprDecode (needExprCode q) = q := by
  cases q with
  | seek q =>
      have h := cursorSeekCode_lt q
      simp [needExprDecode, needExprCode, h, cursorSeekDecode_code]
  | decode q =>
      have h := tagDecodeStateCode_lt q
      simp [needExprDecode, needExprCode, h, tagDecodeStateDecode_code, Nat.add_sub_cancel_left] <;> omega
  | input q =>
      have h := inputNodeCode_lt q
      simp [needExprDecode, needExprCode, inputNodeStateCount, h, inputNodeDecode_code, Nat.add_sub_cancel_left] <;> omega
  | retValue b q =>
      have h := cursorReturnCode_lt q
      cases b <;> simp [needExprDecode, needExprCode, h, cursorReturnDecode_code, Nat.add_sub_cancel_left] <;> omega
  | retPush f q =>
      have h := frameCursorCode_lt f q
      simp [needExprDecode, needExprCode, h, frameCursorDecode_code, Nat.add_sub_cancel_left] <;> omega
  | push f q =>
      have h := framePushPairCode_lt f q
      simp [needExprDecode, needExprCode, h, framePushPairDecode_code, Nat.add_sub_cancel_left] <;> omega
  | doneValue b => cases b <;> simp [needExprDecode, needExprCode]
  | doneNeed => simp [needExprDecode, needExprCode]
  | reject => simp [needExprDecode, needExprCode]

theorem needExprCode_lt
    (q : P01NeedExprCompositeNTM.NeedExprCompositeState) :
    needExprCode q < needExprStateCount := by
  cases q with
  | seek q =>
      have h := cursorSeekCode_lt q
      simp [needExprCode, needExprStateCount, inputNodeStateCount]
      omega
  | decode q =>
      have h := tagDecodeStateCode_lt q
      simp [needExprCode, needExprStateCount, inputNodeStateCount]
      omega
  | input q =>
      have h := inputNodeCode_lt q
      simp [needExprCode, needExprStateCount, inputNodeStateCount] at *
      omega
  | retValue b q =>
      have h := cursorReturnCode_lt q
      cases b <;> simp [needExprCode, needExprStateCount, inputNodeStateCount] <;> omega
  | retPush f q =>
      have h := frameCursorCode_lt f q
      simp [needExprCode, needExprStateCount, inputNodeStateCount]
      omega
  | push f q =>
      have h := framePushPairCode_lt f q
      simp [needExprCode, needExprStateCount, inputNodeStateCount]
      omega
  | doneValue b => cases b <;> decide
  | doneNeed => decide
  | reject => decide

def haveValueStateCount : Nat := 213

def haveValueCode : P01HaveValueCompositeNTM.HaveValueCompositeState → Nat
  | .start false => 0
  | .start true => 1
  | .peek false => 2
  | .peek true => 3
  | .pop false q => 4 + framePopCode q
  | .pop true q => 26 + framePopCode q
  | .push f q => 48 + framePushPairCode f q
  | .doneValue false => 209
  | .doneValue true => 210
  | .doneNeed => 211
  | .reject => 212

def haveValueDecode (n : Nat) : P01HaveValueCompositeNTM.HaveValueCompositeState :=
  if n = 0 then .start false
  else if n = 1 then .start true
  else if n = 2 then .peek false
  else if n = 3 then .peek true
  else if n < 26 then .pop false (framePopDecode (n - 4))
  else if n < 48 then .pop true (framePopDecode (n - 26))
  else if n < 209 then
    let p := framePushPairDecode (n - 48)
    .push p.1 p.2
  else if n = 209 then .doneValue false
  else if n = 210 then .doneValue true
  else if n = 211 then .doneNeed
  else .reject

@[simp] theorem haveValueDecode_code
    (q : P01HaveValueCompositeNTM.HaveValueCompositeState) :
    haveValueDecode (haveValueCode q) = q := by
  cases q with
  | start b => cases b <;> simp [haveValueDecode, haveValueCode]
  | peek b => cases b <;> simp [haveValueDecode, haveValueCode]
  | pop b q =>
      have h := framePopCode_lt q
      cases b <;> simp [haveValueDecode, haveValueCode, h, framePopDecode_code, Nat.add_sub_cancel_left] <;> omega
  | push f q =>
      have h := framePushPairCode_lt f q
      simp [haveValueDecode, haveValueCode, h, framePushPairDecode_code, Nat.add_sub_cancel_left] <;> omega
  | doneValue b => cases b <;> simp [haveValueDecode, haveValueCode]
  | doneNeed => simp [haveValueDecode, haveValueCode]
  | reject => simp [haveValueDecode, haveValueCode]

theorem haveValueCode_lt
    (q : P01HaveValueCompositeNTM.HaveValueCompositeState) :
    haveValueCode q < haveValueStateCount := by
  cases q with
  | start b => cases b <;> decide
  | peek b => cases b <;> decide
  | pop b q =>
      have h := framePopCode_lt q
      cases b <;> simp [haveValueCode, haveValueStateCount] <;> omega
  | push f q =>
      have h := framePushPairCode_lt f q
      simp [haveValueCode, haveValueStateCount]
      omega
  | doneValue b => cases b <;> decide
  | doneNeed => decide
  | reject => decide

def checkedEvalStateCount : Nat := 1847

def checkedEvalCode : P01CheckedEvalRunLoopNTM.CheckedEvalRunState → Nat
  | .need .cnf q => needExprCode q
  | .need .clause q => 401 + needExprCode q
  | .need .mustInput q => 802 + needExprCode q
  | .have .cnf q => 1203 + haveValueCode q
  | .have .clause q => 1416 + haveValueCode q
  | .have .mustInput q => 1629 + haveValueCode q
  | .checkSource false => 1842
  | .checkSource true => 1843
  | .final false => 1844
  | .final true => 1845
  | .reject => 1846

def checkedEvalDecode (n : Nat) : P01CheckedEvalRunLoopNTM.CheckedEvalRunState :=
  if n < 401 then .need .cnf (needExprDecode n)
  else if n < 802 then .need .clause (needExprDecode (n - 401))
  else if n < 1203 then .need .mustInput (needExprDecode (n - 802))
  else if n < 1416 then .have .cnf (haveValueDecode (n - 1203))
  else if n < 1629 then .have .clause (haveValueDecode (n - 1416))
  else if n < 1842 then .have .mustInput (haveValueDecode (n - 1629))
  else if n = 1842 then .checkSource false
  else if n = 1843 then .checkSource true
  else if n = 1844 then .final false
  else if n = 1845 then .final true
  else .reject

@[simp] theorem checkedEvalDecode_code
    (q : P01CheckedEvalRunLoopNTM.CheckedEvalRunState) :
    checkedEvalDecode (checkedEvalCode q) = q := by
  cases q with
  | need m q =>
      have h := needExprCode_lt q
      cases m <;>
        simp [checkedEvalDecode, checkedEvalCode, needExprStateCount, h, needExprDecode_code, Nat.add_sub_cancel_left] <;> omega
  | «have» m q =>
      have h := haveValueCode_lt q
      cases m <;>
        simp [checkedEvalDecode, checkedEvalCode, haveValueStateCount, h, haveValueDecode_code, Nat.add_sub_cancel_left] <;> omega
  | checkSource b => cases b <;> simp [checkedEvalDecode, checkedEvalCode]
  | final b => cases b <;> simp [checkedEvalDecode, checkedEvalCode]
  | reject => simp [checkedEvalDecode, checkedEvalCode]

theorem checkedEvalCode_lt
    (q : P01CheckedEvalRunLoopNTM.CheckedEvalRunState) :
    checkedEvalCode q < checkedEvalStateCount := by
  cases q with
  | need m q =>
      have h := needExprCode_lt q
      cases m <;>
        simp [checkedEvalCode, checkedEvalStateCount, needExprStateCount] at * <;> omega
  | «have» m q =>
      have h := haveValueCode_lt q
      cases m <;>
        simp [checkedEvalCode, checkedEvalStateCount, haveValueStateCount] at * <;> omega
  | checkSource b => cases b <;> decide
  | final b => cases b <;> decide
  | reject => decide

#print axioms MCore.Real.P01ManualStateCodecComposite.needExprDecode_code
#print axioms MCore.Real.P01ManualStateCodecComposite.haveValueDecode_code
#print axioms MCore.Real.P01ManualStateCodecComposite.checkedEvalDecode_code

end P01ManualStateCodecComposite
end Real
end MCore
