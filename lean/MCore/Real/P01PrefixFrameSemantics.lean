import MCore.Real.CanonicalSATFrameAttack
import MCore.Real.Semantics

namespace MCore
namespace Real
namespace P01PrefixFrameSemantics

open CircuitK1
open CanonicalSATFrameAttack

/-- Continuation frame for direct prefix evaluation.  Values needed by the
right-hand side of binary nodes are finite tape data, not control-state data. -/
inductive EvalFrame where
  | neg
  | andLeft (rhs : Circuit)
  | andRight (lhs : Bool)
  | orLeft (rhs : Circuit)
  | orRight (lhs : Bool)
  deriving Repr

/-- Small-step configurations for a direct prefix evaluator. -/
inductive EvalConfig where
  | descend (todo : Circuit) (frames : List EvalFrame)
  | ascend (value : Bool) (frames : List EvalFrame)
  | done (value : Bool)
  deriving Repr

def step (sigma : Assignment) : EvalConfig -> EvalConfig
  | .descend (.input i) fs => .ascend (sigma i) fs
  | .descend (.const b) fs => .ascend b fs
  | .descend (.not c) fs => .descend c (.neg :: fs)
  | .descend (.and a b) fs => .descend a (.andLeft b :: fs)
  | .descend (.or a b) fs => .descend a (.orLeft b :: fs)
  | .ascend v [] => .done v
  | .ascend v (.neg :: fs) => .ascend (!v) fs
  | .ascend v (.andLeft rhs :: fs) => .descend rhs (.andRight v :: fs)
  | .ascend v (.andRight lhs :: fs) => .ascend (Bool.and lhs v) fs
  | .ascend v (.orLeft rhs :: fs) => .descend rhs (.orRight v :: fs)
  | .ascend v (.orRight lhs :: fs) => .ascend (Bool.or lhs v) fs
  | .done v => .done v

/-- Big-step reference for the same continuation discipline. -/
def evalWithFrames (sigma : Assignment) : Circuit -> List EvalFrame -> Bool
  | .input i, fs => finish sigma (sigma i) fs
  | .const b, fs => finish sigma b fs
  | .not c, fs => evalWithFrames sigma c (.neg :: fs)
  | .and a b, fs => evalWithFrames sigma a (.andLeft b :: fs)
  | .or a b, fs => evalWithFrames sigma a (.orLeft b :: fs)
where
  finish (sigma : Assignment) : Bool -> List EvalFrame -> Bool
    | v, [] => v
    | v, .neg :: fs => finish sigma (!v) fs
    | v, .andLeft rhs :: fs => evalWithFrames sigma rhs (.andRight v :: fs)
    | v, .andRight lhs :: fs => finish sigma (Bool.and lhs v) fs
    | v, .orLeft rhs :: fs => evalWithFrames sigma rhs (.orRight v :: fs)
    | v, .orRight lhs :: fs => finish sigma (Bool.or lhs v) fs
termination_by
  evalWithFrames _ c fs => CircuitK1.size c + fs.length
  finish _ _ fs => fs.length
decreasing_by
  all_goals simp [CircuitK1.size] <;> omega

/-- Direct prefix evaluation with an empty continuation is exactly the existing
circuit semantics. -/
theorem evalWithFrames_correct
    (sigma : Assignment) (c : Circuit) :
    evalWithFrames sigma c [] = evalCircuit sigma c := by
  induction c with
  | input i =>
      rfl
  | const b =>
      rfl
  | not c ih =>
      simp [evalWithFrames, evalWithFrames.finish, evalCircuit, ih]
  | and a b iha ihb =>
      simp [evalWithFrames, evalWithFrames.finish, evalCircuit, iha, ihb]
  | or a b iha ihb =>
      simp [evalWithFrames, evalWithFrames.finish, evalCircuit, iha, ihb]

/-- Therefore a physical machine refining this frame semantics may replace the
postorder materialization layer without changing verifier semantics. -/
theorem prefix_frame_semantics_is_verifier_semantics
    (sigma : Assignment) (c : Circuit) :
    evalWithFrames sigma c [] = evalCircuit sigma c :=
  evalWithFrames_correct sigma c

#print axioms MCore.Real.P01PrefixFrameSemantics.evalWithFrames_correct
#print axioms MCore.Real.P01PrefixFrameSemantics.prefix_frame_semantics_is_verifier_semantics

end P01PrefixFrameSemantics
end Real
end MCore
