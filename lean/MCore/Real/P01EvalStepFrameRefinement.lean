import MCore.Real.P01EvalFramePushMachine
import MCore.Real.P01EvalFramePopMachine

namespace MCore
namespace Real
namespace P01EvalStepFrameRefinement

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01FullVerifierPhysicalStackV2
open P01EvalFramePushMachine
open P01EvalFramePopMachine

/-- Exact physical refinement of semantic frame-stack push: three TM steps
prepend precisely the canonical three-bit code of the new EvalFrame. -/
theorem push_refines_frame_cons
    (witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat)
    (f : EvalFrame) :
    let final :=
      framePushMachine.run 3
        (framePushConfig f
          (physicalStackV2Tape witness source
            (encodeEvalFrames frames) padding))
    final.state = .halt ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames (f :: frames))
          (((padding - 1) - 1) - 1) := by
  dsimp
  simpa [encodeEvalFrames] using
    framePush_run_three witness source (encodeEvalFrames frames) padding f

/-- Exact physical refinement of semantic frame-stack pop/read: four TM steps
decode the head frame, erase exactly its three-bit code, and restore the
canonical physical representation of the tail frame stack. -/
theorem pop_refines_frame_tail
    (witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat)
    (f : EvalFrame) :
    let final :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrames (f :: frames)) padding))
    final.state = .halt f ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames frames) (padding + 3) := by
  dsimp
  simpa [encodeEvalFrames] using
    framePop_run_four witness source (encodeEvalFrames frames) padding f

/-- The semantic NOT-tag transition and its physical frame-stack action agree:
the logical step pushes .neg and the fixed physical machine pushes exactly the
canonical .neg frame code. -/
theorem evalStep_not_tag_refined
    (sigma : Assignment)
    (rest witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (false :: true :: true :: rest) frames) =
        some (needExpr rest (.neg :: frames)) ∧
    let final :=
      framePushMachine.run 3
        (framePushConfig .neg
          (physicalStackV2Tape witness source
            (encodeEvalFrames frames) padding))
    final.state = .halt ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames (.neg :: frames))
          (((padding - 1) - 1) - 1) := by
  constructor
  · rfl
  · exact push_refines_frame_cons witness source frames padding .neg

/-- The semantic AND-tag transition and its physical frame-stack action agree. -/
theorem evalStep_and_tag_refined
    (sigma : Assignment)
    (rest witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (true :: false :: false :: rest) frames) =
        some (needExpr rest (.andLeft :: frames)) ∧
    let final :=
      framePushMachine.run 3
        (framePushConfig .andLeft
          (physicalStackV2Tape witness source
            (encodeEvalFrames frames) padding))
    final.state = .halt ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames (.andLeft :: frames))
          (((padding - 1) - 1) - 1) := by
  constructor
  · rfl
  · exact push_refines_frame_cons witness source frames padding .andLeft

/-- The semantic OR-tag transition and its physical frame-stack action agree. -/
theorem evalStep_or_tag_refined
    (sigma : Assignment)
    (rest witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (true :: false :: true :: rest) frames) =
        some (needExpr rest (.orLeft :: frames)) ∧
    let final :=
      framePushMachine.run 3
        (framePushConfig .orLeft
          (physicalStackV2Tape witness source
            (encodeEvalFrames frames) padding))
    final.state = .halt ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames (.orLeft :: frames))
          (((padding - 1) - 1) - 1) := by
  constructor
  · rfl
  · exact push_refines_frame_cons witness source frames padding .orLeft

/-- Returning through a semantic frame is physically readable/removable with
the already-certified fixed pop machine.  This theorem covers every EvalFrame
constructor and is the common first half of neg/and/or return refinement. -/
theorem evalStep_return_frame_physically_decodable
    (witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat)
    (f : EvalFrame) :
    let final :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrames (f :: frames)) padding))
    final.state = .halt f ∧
      PhysicalStackRepV2 final.tape witness source
        (encodeEvalFrames frames) := by
  dsimp
  have h :=
    framePop_run_four_rep witness source
      (encodeEvalFrames frames) padding f
  simpa [encodeEvalFrames] using h

#print axioms MCore.Real.P01EvalStepFrameRefinement.push_refines_frame_cons
#print axioms MCore.Real.P01EvalStepFrameRefinement.pop_refines_frame_tail
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_not_tag_refined
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_and_tag_refined
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_or_tag_refined
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_return_frame_physically_decodable

end P01EvalStepFrameRefinement
end Real
end MCore
