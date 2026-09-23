import Mathlib
import MCore.P012.P012Core

namespace MCore
namespace P012

/-- A rational state with fixed denominator 3, represented by its signed
numerator.  This avoids quotient-normalization issues while preserving the
exact arithmetic relevant to the transition -2/3 -> 3/3. -/
structure ThirdState where
  numerator : Int
  deriving DecidableEq, Repr

def thirdValueNumerator (s : ThirdState) : Int := s.numerator

def negTwoThirds : ThirdState := ⟨-2⟩
def negOneThird : ThirdState := ⟨-1⟩
def zeroThird : ThirdState := ⟨0⟩
def oneThird : ThirdState := ⟨1⟩
def twoThirds : ThirdState := ⟨2⟩
def threeThirds : ThirdState := ⟨3⟩
def negThreeThirds : ThirdState := ⟨-3⟩

/-- Displacement in numerator units; divide by 3 externally to recover the
rational displacement. -/
def displacementNumerator (a b : ThirdState) : Int :=
  b.numerator - a.numerator

theorem negTwo_to_three_displacement :
    displacementNumerator negTwoThirds threeThirds = 5 := by
  norm_num [displacementNumerator, negTwoThirds, threeThirds]

theorem two_to_three_displacement :
    displacementNumerator twoThirds threeThirds = 1 := by
  norm_num [displacementNumerator, twoThirds, threeThirds]

theorem two_to_negThree_displacement :
    displacementNumerator twoThirds negThreeThirds = -5 := by
  norm_num [displacementNumerator, twoThirds, negThreeThirds]

/-- Unit motion means exactly one numerator step, i.e. 1/3 in rational value. -/
def UnitThirdStep (a b : ThirdState) : Prop :=
  b.numerator = a.numerator + 1

theorem step_neg2_neg1 : UnitThirdStep negTwoThirds negOneThird := by
  norm_num [UnitThirdStep, negTwoThirds, negOneThird]

theorem step_neg1_zero : UnitThirdStep negOneThird zeroThird := by
  norm_num [UnitThirdStep, negOneThird, zeroThird]

theorem step_zero_one : UnitThirdStep zeroThird oneThird := by
  norm_num [UnitThirdStep, zeroThird, oneThird]

theorem step_one_two : UnitThirdStep oneThird twoThirds := by
  norm_num [UnitThirdStep, oneThird, twoThirds]

theorem step_two_three : UnitThirdStep twoThirds threeThirds := by
  norm_num [UnitThirdStep, twoThirds, threeThirds]

/-- The complete discrete path crossing zero. -/
def fullCrossingPath : List ThirdState :=
  [negTwoThirds, negOneThird, zeroThird, oneThird, twoThirds, threeThirds]

theorem fullCrossingPath_length :
    fullCrossingPath.length = 6 := by
  decide

/-- Orientation relative to zero. -/
inductive Orientation where
  | negative
  | neutral
  | positive
  deriving DecidableEq, Repr, BEq

def orientation (s : ThirdState) : Orientation :=
  if s.numerator < 0 then .negative
  else if s.numerator = 0 then .neutral
  else .positive

theorem orientation_negTwo :
    orientation negTwoThirds = .negative := by
  norm_num [orientation, negTwoThirds]

theorem orientation_zero :
    orientation zeroThird = .neutral := by
  norm_num [orientation, zeroThird]

theorem orientation_three :
    orientation threeThirds = .positive := by
  norm_num [orientation, threeThirds]

theorem orientation_two :
    orientation twoThirds = .positive := by
  norm_num [orientation, twoThirds]

theorem orientation_negThree :
    orientation negThreeThirds = .negative := by
  norm_num [orientation, negThreeThirds]

/-- The transition -2/3 -> 3/3 crosses orientation classes. -/
theorem negTwo_to_three_changes_orientation :
    orientation negTwoThirds ≠ orientation threeThirds := by
  simp [orientation_negTwo, orientation_three]

/-- The opposite transition 2/3 -> -3/3 also changes orientation classes. -/
theorem two_to_negThree_changes_orientation :
    orientation twoThirds ≠ orientation negThreeThirds := by
  simp [orientation_two, orientation_negThree]

#print axioms MCore.P012.negTwo_to_three_displacement
#print axioms MCore.P012.negTwo_to_three_changes_orientation

end P012
end MCore
