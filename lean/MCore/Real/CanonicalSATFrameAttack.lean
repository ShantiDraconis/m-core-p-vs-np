import MCore.Real.CanonicalSATNatParserAttack

namespace MCore
namespace Real
namespace CanonicalSATFrameAttack

open CanonicalFinalProof

/-- Recursive parser continuation frames needed by prefix Circuit parsing.
    Binary constructors need two phases: waiting for the left child and then
    waiting for the right child. -/
inductive Frame where
  | neg
  | andLeft
  | andRight
  | orLeft
  | orRight
  deriving DecidableEq, Repr

/-- Fixed-width binary representation of parser frames. -/
def encodeFrame : Frame → List Bool
  | .neg      => [false, false, false]
  | .andLeft  => [false, false, true]
  | .andRight => [false, true, false]
  | .orLeft   => [false, true, true]
  | .orRight  => [true, false, false]

def decodeFrame : List Bool → Option Frame
  | [false, false, false] => some .neg
  | [false, false, true]  => some .andLeft
  | [false, true, false]  => some .andRight
  | [false, true, true]   => some .orLeft
  | [true, false, false]  => some .orRight
  | _ => none

@[simp] theorem decodeFrame_encodeFrame
    (f : Frame) :
    decodeFrame (encodeFrame f) = some f := by
  cases f <;> rfl

@[simp] theorem encodeFrame_length
    (f : Frame) :
    (encodeFrame f).length = 3 := by
  cases f <;> rfl

def encodeFrames : List Frame → List Bool
  | [] => []
  | f :: fs => encodeFrame f ++ encodeFrames fs

def decodeFrames : List Bool → Option (List Frame)
  | [] => some []
  | a :: b :: c :: rest => do
      let f ← decodeFrame [a,b,c]
      let fs ← decodeFrames rest
      some (f :: fs)
  | _ => none

theorem decodeFrames_encodeFrames
    (fs : List Frame) :
    decodeFrames (encodeFrames fs) = some fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      cases f <;>
        simp [encodeFrames, decodeFrames, decodeFrame, ih]

theorem encodeFrames_length
    (fs : List Frame) :
    (encodeFrames fs).length = 3 * fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      simp [encodeFrames, encodeFrame_length, ih]
      omega

theorem encoded_stack_linear_space
    (fs : List Frame)
    (inputLength : Nat)
    (hDepth : fs.length ≤ inputLength) :
    (encodeFrames fs).length ≤ 3 * inputLength := by
  rw [encodeFrames_length]
  exact Nat.mul_le_mul_left 3 hDepth

/-- Functional push representation; the machine-level implementation is still
    required separately. -/
theorem encodeFrames_push
    (f : Frame)
    (fs : List Frame) :
    encodeFrames (f :: fs) =
      encodeFrame f ++ encodeFrames fs := by
  rfl

/-- Functional pop round-trip after decoding a well-formed encoded stack. -/
theorem decodeFrames_push
    (f : Frame)
    (fs : List Frame) :
    decodeFrames (encodeFrame f ++ encodeFrames fs) =
      some (f :: fs) := by
  simpa [encodeFrames] using decodeFrames_encodeFrames (f :: fs)

/-- Exact next operational boundary: realize constant-width frame push/pop on
    the same canonical Option Bool tape with finite control and polynomial
    traversal overhead. No implementation is postulated here. -/
structure FrameTapeMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

def FrameTapeOperationalGap : Prop :=
  Nonempty FrameTapeMachineCertificate

#print axioms MCore.Real.CanonicalSATFrameAttack.decodeFrame_encodeFrame
#print axioms MCore.Real.CanonicalSATFrameAttack.decodeFrames_encodeFrames
#print axioms MCore.Real.CanonicalSATFrameAttack.encodeFrames_length
#print axioms MCore.Real.CanonicalSATFrameAttack.encoded_stack_linear_space
#print axioms MCore.Real.CanonicalSATFrameAttack.decodeFrames_push

end CanonicalSATFrameAttack
end Real
end MCore
