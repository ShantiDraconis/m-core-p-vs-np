import MCore.Real.CanonicalSATFrameAttack
import MCore.Real.Semantics

namespace MCore
namespace Real
namespace P01PrefixFrameSemantics

open CircuitK1
open CanonicalSATFrameAttack

inductive EvalFrame where
  | neg
  | andLeft (rhs : Circuit)
  | andRight (lhs : Bool)
  | orLeft (rhs : Circuit)
  | orRight (lhs : Bool)
  deriving Repr

inductive EvalConfig where
  | descend (todo : Circuit) (frames : List EvalFrame)
  | ascend (value : Bool) (frames : List EvalFrame)
  | done (value : Bool)
  deriving Repr

mutual
  def evalWithFrames (sigma : Assignment) : Circuit -> List EvalFrame -> Bool
    | .input i, fs => finish sigma (sigma i) fs
    | .const b, fs => finish sigma b fs
    | .not c, fs => evalWithFrames sigma c (.neg :: fs)
    | .and a b, fs => evalWithFrames sigma a (.andLeft b :: fs)
    | .or a b, fs => evalWithFrames sigma a (.orLeft b :: fs)

  def finish (sigma : Assignment) : Bool -> List EvalFrame -> Bool
    | v, [] => v
    | v, .neg :: fs => finish sigma (!v) fs
    | v, .andLeft rhs :: fs =>
        evalWithFrames sigma rhs (.andRight v :: fs)
    | v, .andRight lhs :: fs =>
        finish sigma (Bool.and lhs v) fs
    | v, .orLeft rhs :: fs =>
        evalWithFrames sigma rhs (.orRight v :: fs)
    | v, .orRight lhs :: fs =>
        finish sigma (Bool.or lhs v) fs
end

mutual
  theorem evalWithFrames_correct_aux
      (sigma : Assignment) (c : Circuit) (fs : List EvalFrame) :
      evalWithFrames sigma c fs =
        finish sigma (evalCircuit sigma c) fs := by
    cases c with
    | input i => rfl
    | const b => rfl
    | not c =>
        simp only [evalWithFrames, evalCircuit]
        rw [evalWithFrames_correct_aux sigma c (.neg :: fs)]
        rfl
    | and a b =>
        simp only [evalWithFrames, evalCircuit]
        rw [evalWithFrames_correct_aux sigma a (.andLeft b :: fs)]
        simp only [finish]
        rw [evalWithFrames_correct_aux sigma b
          (.andRight (evalCircuit sigma a) :: fs)]
        rfl
    | or a b =>
        simp only [evalWithFrames, evalCircuit]
        rw [evalWithFrames_correct_aux sigma a (.orLeft b :: fs)]
        simp only [finish]
        rw [evalWithFrames_correct_aux sigma b
          (.orRight (evalCircuit sigma a) :: fs)]
        rfl

  theorem finish_correct_aux
      (sigma : Assignment) (v : Bool) (fs : List EvalFrame) :
      finish sigma v fs = finish sigma v fs := by
    rfl
end

theorem evalWithFrames_correct
    (sigma : Assignment) (c : Circuit) :
    evalWithFrames sigma c [] = evalCircuit sigma c := by
  rw [evalWithFrames_correct_aux sigma c []]
  rfl

theorem prefix_frame_semantics_is_verifier_semantics
    (sigma : Assignment) (c : Circuit) :
    evalWithFrames sigma c [] = evalCircuit sigma c :=
  evalWithFrames_correct sigma c

#print axioms MCore.Real.P01PrefixFrameSemantics.evalWithFrames_correct
#print axioms MCore.Real.P01PrefixFrameSemantics.prefix_frame_semantics_is_verifier_semantics

end P01PrefixFrameSemantics
end Real
end MCore
