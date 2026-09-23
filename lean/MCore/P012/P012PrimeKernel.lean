import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import MCore.P012.P012PrimeTransitionBoundary

namespace MCore
namespace P012

/-- Prime operational kernel at fixed positive denominator q.
This is a P012 modeling choice: 2 is used because it is the least prime. -/
structure PrimeKernel where
  q : Nat
  hq : 0 < q

def kernelNumerator : Int := 2

def kernelState (K : PrimeKernel) : ThirdState := ⟨kernelNumerator⟩
def kernelMirrorState (K : PrimeKernel) : ThirdState := ⟨-kernelNumerator⟩

theorem two_is_prime : Nat.Prime 2 := by
  norm_num

theorem two_is_least_prime
    {p : Nat} (hp : Nat.Prime p) :
    2 ≤ p := by
  exact hp.two_le

/-- Reflection kernel on signed numerators. -/
def reflectNumerator (z : Int) : Int := -z

def reflectState (s : ThirdState) : ThirdState :=
  ⟨reflectNumerator s.numerator⟩

theorem reflect_involutive (s : ThirdState) :
    reflectState (reflectState s) = s := by
  cases s
  simp [reflectState, reflectNumerator]

theorem kernel_reflection :
    reflectState ⟨-2⟩ = ⟨2⟩ := by
  rfl

/-- Distance to the operational kernel is measured in absolute numerator units. -/
def kernelDistance (s : ThirdState) : Nat :=
  Int.natAbs s.numerator - 2

def CompressesTowardKernel (a b : ThirdState) : Prop :=
  2 ≤ Int.natAbs b.numerator ∧
  Int.natAbs b.numerator ≤ Int.natAbs a.numerator

def ExpandsFromKernel (a b : ThirdState) : Prop :=
  2 ≤ Int.natAbs a.numerator ∧
  Int.natAbs a.numerator ≤ Int.natAbs b.numerator

theorem compress_neg7_to_neg2 :
    CompressesTowardKernel ⟨-7⟩ ⟨-2⟩ := by
  norm_num [CompressesTowardKernel]

theorem expand_2_to_7 :
    ExpandsFromKernel ⟨2⟩ ⟨7⟩ := by
  norm_num [ExpandsFromKernel]

/-- The central prime-only reflection has numerator displacement 4. -/
theorem kernel_reflection_displacement :
    displacementNumerator ⟨-2⟩ ⟨2⟩ = 4 := by
  norm_num [displacementNumerator]

/-- At denominator q, numerator displacement 4 corresponds formally to 4/q.
We keep the exact integer numerator here and do not identify the kernel with 0 or 1. -/
theorem kernel_is_not_zero_numerator :
    kernelNumerator ≠ 0 := by
  norm_num [kernelNumerator]

theorem kernel_is_not_one_numerator :
    kernelNumerator ≠ 1 := by
  norm_num [kernelNumerator]

#print axioms MCore.P012.two_is_least_prime
#print axioms MCore.P012.kernel_reflection
#print axioms MCore.P012.compress_neg7_to_neg2
#print axioms MCore.P012.expand_2_to_7

end P012
end MCore
