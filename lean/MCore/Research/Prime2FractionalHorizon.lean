import Mathlib
import MCore.Research.Prime2ConservativeTransfer

namespace MCore
namespace Research
namespace Prime2

/-- A prime quotient is ordinary arithmetic data.  The numerator/denominator
remain standard natural primes; experimental nucleus information is separate. -/
structure PrimeQuotient where
  numerator : Nat
  denominator : Nat
  numerator_prime : Nat.Prime numerator
  denominator_prime : Nat.Prime denominator

/-- Pure quotient excludes the diagonal p=q, hence excludes the value 1. -/
def PrimeQuotient.Pure (Q : PrimeQuotient) : Prop :=
  Q.numerator ≠ Q.denominator

theorem pure_prime_quotient_coprime
    (Q : PrimeQuotient)
    (hPure : Q.Pure) :
    Nat.Coprime Q.numerator Q.denominator := by
  exact (Nat.coprime_primes Q.numerator_prime Q.denominator_prime).mpr hPure

/-- Decimal-horizon classification for a prime denominator.
For a reduced rational with prime denominator q, base-10 termination can occur
only at q=2 or q=5.  We store the arithmetic criterion rather than pretending
that every prime quotient has an infinite decimal tail. -/
def PrimeDecimalHorizon (q : Nat) : Prop :=
  Nat.Prime q ∧ q ≠ 2 ∧ q ≠ 5

theorem prime_decimal_horizon_not_two
    {q : Nat} (h : PrimeDecimalHorizon q) :
    q ≠ 2 :=
  h.2.1

theorem prime_decimal_horizon_not_five
    {q : Nat} (h : PrimeDecimalHorizon q) :
    q ≠ 5 :=
  h.2.2

/-- Experimental even shell.  This is metadata/research structure, not a new
standard prime predicate. -/
structure FractionalEvenShell where
  evenPart : Nat
  quotient : PrimeQuotient
  even : 2 ∣ evenPart

/-- Horizon-Prime observation package. -/
structure HorizonPrimeEvidence where
  quotient : PrimeQuotient
  pure : quotient.Pure
  decimalHorizon : PrimeDecimalHorizon quotient.denominator

/-- No HorizonPrimeEvidence item changes standard machine semantics by itself. -/
theorem horizon_evidence_does_not_change_correctAt
    (I : ConservativePrime2Interpretation)
    (_H : HorizonPrimeEvidence)
    (M : Real.CanonicalFinalProof.PolyDTMCandidate)
    (x : Real.CanonicalFinalProof.BitString) :
    Prime2CorrectAt (I.mapCandidate M) (I.mapInput x) ↔
      CorrectAtStd M x :=
  I.correct_iff M x

/-!
Research interpretation:
* q=2 or q=5 are terminating-decimal boundary denominators in base 10.
* prime q other than 2 and 5 is the candidate repeating-tail regime.
* proving an actual theorem about decimal expansions may be added independently.
* none of this receives G21 proof credit without Coverage.
-/

#print axioms MCore.Research.Prime2.pure_prime_quotient_coprime
#print axioms MCore.Research.Prime2.horizon_evidence_does_not_change_correctAt

end Prime2
end Research
end MCore
