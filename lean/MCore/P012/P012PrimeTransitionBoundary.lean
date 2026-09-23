import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import MCore.P012.P012SignedThirdTransitions

namespace MCore
namespace P012

/-- Prime restriction on the absolute value of a signed numerator. -/
def PrimeNumerator (z : Int) : Prop :=
  Nat.Prime z.natAbs

theorem primeNumerator_negTwo :
    PrimeNumerator (-2) := by
  norm_num [PrimeNumerator]

theorem primeNumerator_two :
    PrimeNumerator 2 := by
  norm_num [PrimeNumerator]

theorem primeNumerator_three :
    PrimeNumerator 3 := by
  norm_num [PrimeNumerator]

theorem not_primeNumerator_negOne :
    ¬ PrimeNumerator (-1) := by
  norm_num [PrimeNumerator]

theorem not_primeNumerator_zero :
    ¬ PrimeNumerator 0 := by
  norm_num [PrimeNumerator]

theorem not_primeNumerator_one :
    ¬ PrimeNumerator 1 := by
  norm_num [PrimeNumerator]

def PrimeThirdState (s : ThirdState) : Prop :=
  PrimeNumerator s.numerator

theorem negTwoThirds_prime :
    PrimeThirdState negTwoThirds := by
  norm_num [PrimeThirdState, PrimeNumerator, negTwoThirds]

theorem twoThirds_prime :
    PrimeThirdState twoThirds := by
  norm_num [PrimeThirdState, PrimeNumerator, twoThirds]

theorem threeThirds_prime :
    PrimeThirdState threeThirds := by
  norm_num [PrimeThirdState, PrimeNumerator, threeThirds]

theorem negOneThird_not_prime :
    ¬ PrimeThirdState negOneThird := by
  norm_num [PrimeThirdState, PrimeNumerator, negOneThird]

theorem zeroThird_not_prime :
    ¬ PrimeThirdState zeroThird := by
  norm_num [PrimeThirdState, PrimeNumerator, zeroThird]

theorem oneThird_not_prime :
    ¬ PrimeThirdState oneThird := by
  norm_num [PrimeThirdState, PrimeNumerator, oneThird]

/-- A unit transition constrained to prime endpoints. -/
def PrimeUnitThirdStep (a b : ThirdState) : Prop :=
  PrimeThirdState a ∧ PrimeThirdState b ∧ UnitThirdStep a b

theorem no_prime_unit_step_neg2_neg1 :
    ¬ PrimeUnitThirdStep negTwoThirds negOneThird := by
  intro h
  exact negOneThird_not_prime h.2.1

theorem no_prime_unit_step_neg1_zero :
    ¬ PrimeUnitThirdStep negOneThird zeroThird := by
  intro h
  exact negOneThird_not_prime h.1

theorem no_prime_unit_step_zero_one :
    ¬ PrimeUnitThirdStep zeroThird oneThird := by
  intro h
  exact zeroThird_not_prime h.1

theorem no_prime_unit_step_one_two :
    ¬ PrimeUnitThirdStep oneThird twoThirds := by
  intro h
  exact oneThird_not_prime h.1

/-- The final 2/3 -> 3/3 unit step is admissible under the prime-numerator
restriction. -/
theorem prime_unit_step_two_three :
    PrimeUnitThirdStep twoThirds threeThirds := by
  exact ⟨twoThirds_prime, threeThirds_prime, step_two_three⟩

/-- The natural six-point zero-crossing path is not entirely prime-admissible. -/
theorem fullCrossingPath_contains_nonprime_transition_states :
    ¬ (∀ s ∈ fullCrossingPath, PrimeThirdState s) := by
  intro h
  have hzero : PrimeThirdState zeroThird := by
    exact h zeroThird (by simp [fullCrossingPath])
  exact zeroThird_not_prime hzero

/-- Prime-only numerators therefore do not support the canonical unit-step
crossing path from -2/3 to 3/3. This is a statement about this discrete path,
not about topological continuity in Q. -/
theorem canonical_unit_crossing_not_prime_only :
    ¬ (
      PrimeThirdState negTwoThirds ∧
      PrimeThirdState negOneThird ∧
      PrimeThirdState zeroThird ∧
      PrimeThirdState oneThird ∧
      PrimeThirdState twoThirds ∧
      PrimeThirdState threeThirds
    ) := by
  intro h
  exact zeroThird_not_prime h.2.2.1

#print axioms MCore.P012.fullCrossingPath_contains_nonprime_transition_states
#print axioms MCore.P012.canonical_unit_crossing_not_prime_only

end P012
end MCore
