import Mathlib.Tactic.NormNum
import MCore.P012.P012PrimeKernel

namespace MCore
namespace P012

/-- Odd-prime numerator states: absolute numerator is prime and different from 2. -/
def OddPrimeNumerator (z : Int) : Prop :=
  PrimeNumerator z ∧ z.natAbs ≠ 2

def OddPrimeThirdState (s : ThirdState) : Prop :=
  OddPrimeNumerator s.numerator

theorem five_is_odd_prime_numerator :
    OddPrimeNumerator 5 := by
  constructor
  · norm_num [PrimeNumerator]
  · norm_num

theorem negFive_is_odd_prime_numerator :
    OddPrimeNumerator (-5) := by
  constructor
  · norm_num [PrimeNumerator]
  · norm_num

theorem two_not_odd_prime_numerator :
    ¬ OddPrimeNumerator 2 := by
  intro h
  exact h.2 (by norm_num)

/-- For denominator 3, ±3 represent ±1 and are excluded from the pure
noninteger state space. -/
def PureOddPrimeThirdState (s : ThirdState) : Prop :=
  OddPrimeThirdState s ∧ s.numerator.natAbs ≠ 3

theorem negFive_pure :
    PureOddPrimeThirdState ⟨-5⟩ := by
  exact ⟨negFive_is_odd_prime_numerator, by norm_num⟩

theorem five_pure :
    PureOddPrimeThirdState ⟨5⟩ := by
  exact ⟨five_is_odd_prime_numerator, by norm_num⟩

theorem negThree_not_pure :
    ¬ PureOddPrimeThirdState ⟨-3⟩ := by
  intro h
  exact h.2 (by norm_num)

theorem three_not_pure :
    ¬ PureOddPrimeThirdState ⟨3⟩ := by
  intro h
  exact h.2 (by norm_num)

/-- Under the q=3 pure odd-prime convention, ±5 are the closest admissible
signed states around the excluded center. -/
theorem central_odd_prime_gap_displacement :
    displacementNumerator ⟨-5⟩ ⟨5⟩ = 10 := by
  norm_num [displacementNumerator]

/-- No unit-third chain through the canonical center can remain pure odd-prime,
because the mandatory zero state is not prime. -/
theorem no_pure_odd_prime_canonical_crossing :
    ¬ (∀ s ∈ fullCrossingPath, PureOddPrimeThirdState s) := by
  intro h
  have hz := h zeroThird (by simp [fullCrossingPath])
  exact zeroThird_not_prime hz.1.1

/-- Removing the prime 2 removes the operational kernel state used by the
prime-kernel model. -/
theorem operational_kernel_not_in_odd_prime_space :
    ¬ OddPrimeThirdState ⟨2⟩ := by
  exact two_not_odd_prime_numerator

#print axioms MCore.P012.central_odd_prime_gap_displacement
#print axioms MCore.P012.no_pure_odd_prime_canonical_crossing
#print axioms MCore.P012.operational_kernel_not_in_odd_prime_space

end P012
end MCore
