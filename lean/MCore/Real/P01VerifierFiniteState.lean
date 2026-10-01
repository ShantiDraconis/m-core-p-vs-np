import Mathlib
import MCore.Real.P01VerifierEvalCompositeNTM
import MCore.Real.P01IntegratedAssembly

namespace MCore
namespace Real
namespace P01VerifierFiniteState

open P01IntegratedAssembly
open P01VerifierEvalCompositeNTM

/-
All control alphabets below are finite.  We derive the instances locally in
one place instead of hard-coding a fragile manual state count.
-/
deriving instance Fintype for P01EncodedStackEvaluator.EvalFrame
deriving instance Fintype for P01InputReturnMode.InputReturnMode
deriving instance Fintype for P01InputReturnMode.InputReturnClassifyState
deriving instance Fintype for P01InputIndexLookahead.InputIndexLookaheadState
deriving instance Fintype for P01WitnessIndexedReadPreserving.PreservingReadState
deriving instance Fintype for P01InputAfterReadReturn.InputAfterReadReturnState
deriving instance Fintype for P01InputNodeCompositeNTM.InputNodeCompositeState
deriving instance Fintype for P01EvalCursorMachine.CursorSeekState
deriving instance Fintype for P01EvalCursorRoundTrip.CursorReturnState
deriving instance Fintype for P01NeedExprTagDecode.NeedExprTag
deriving instance Fintype for P01NeedExprTagDecode.TagDecodeState
deriving instance Fintype for P01EvalFramePushMachine.FramePushState
deriving instance Fintype for P01EvalFramePopMachineV2.FramePopState
deriving instance Fintype for P01NeedExprCompositeNTM.NeedExprCompositeState
deriving instance Fintype for P01HaveValueCompositeNTM.HaveValueCompositeState
deriving instance Fintype for P01EvalRunLoopNTM.EvalRunLoopState
deriving instance Fintype for VerifierEvalState

/-- One spare state is intentionally left unused.  This makes the target
exactly `Fin (stateCount + 1)` without arithmetic on `card - 1`. -/
def verifierStateCount : Nat :=
  Fintype.card VerifierEvalState

noncomputable def verifierStateEquiv :
    VerifierEvalState ≃ Fin (Fintype.card VerifierEvalState) :=
  Fintype.equivFin VerifierEvalState

noncomputable def verifierStateEncode
    (q : VerifierEvalState) :
    Fin (verifierStateCount + 1) :=
  ⟨(verifierStateEquiv q).val,
    Nat.lt_succ_of_lt (verifierStateEquiv q).isLt⟩

noncomputable def verifierStateDecode
    (q : Fin (verifierStateCount + 1)) :
    VerifierEvalState :=
  if h : q.val < Fintype.card VerifierEvalState then
    verifierStateEquiv.symm ⟨q.val, h⟩
  else
    verifierEvalMachine.initial

theorem verifierStateDecode_encode
    (q : VerifierEvalState) :
    verifierStateDecode (verifierStateEncode q) = q := by
  unfold verifierStateDecode verifierStateEncode verifierStateCount
  simp [verifierStateEquiv]

/-- Concrete `Fin`-indexed verifier core obtained only by state relabelling.
The extra unused code decodes to the initial state; it is unreachable from any
encoded source state. -/
noncomputable def verifierFinMachine :
    NTM (Fin (verifierStateCount + 1)) (Option Bool) :=
  P01IntegratedAssembly.relabel
    verifierEvalMachine verifierStateEncode verifierStateDecode

@[simp] theorem verifierFinMachine_blank :
    verifierFinMachine.blank = none := rfl

theorem verifierFinMachine_haltsWithin_iff
    (n : Nat)
    (c : Configuration VerifierEvalState (Option Bool)) :
    verifierFinMachine.HaltsWithin n
        (P01NTMRunLaws.liftConfig verifierStateEncode c) ↔
      verifierEvalMachine.HaltsWithin n c := by
  exact P01IntegratedAssembly.relabel_haltsWithin_iff
    verifierEvalMachine verifierStateEncode verifierStateDecode
      verifierStateDecode_encode n c

theorem verifierFinMachine_acceptsWithin_iff
    (n : Nat)
    (c : Configuration VerifierEvalState (Option Bool)) :
    verifierFinMachine.AcceptsWithin n
        (P01NTMRunLaws.liftConfig verifierStateEncode c) ↔
      verifierEvalMachine.AcceptsWithin n c := by
  exact P01IntegratedAssembly.relabel_acceptsWithin_iff
    verifierEvalMachine verifierStateEncode verifierStateDecode
      verifierStateDecode_encode n c

#print axioms MCore.Real.P01VerifierFiniteState.verifierStateDecode_encode
#print axioms MCore.Real.P01VerifierFiniteState.verifierFinMachine_haltsWithin_iff
#print axioms MCore.Real.P01VerifierFiniteState.verifierFinMachine_acceptsWithin_iff

end P01VerifierFiniteState
end Real
end MCore
