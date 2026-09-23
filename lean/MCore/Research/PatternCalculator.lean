import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.NativeDecide
import MCore.Research.Prime2FractionalHorizon

namespace MCore
namespace Research
namespace PatternCalculator

open Prime2

/-- Research classification only.  None of these labels is a proof producer. -/
inductive ResearchLine where
  | prime2
  | horizonPrime
  | g21WitnessMap
  | complexityBoundary
  | encodingInvariant
  | geometricP012
  | negativeResult
  deriving DecidableEq, Repr, BEq

inductive EvidenceStrength where
  | observation
  | finitePattern
  | kernelTheorem
  | counterexample
  deriving DecidableEq, Repr, BEq

structure PrimeHorizonInput where
  denominator : Nat
  excludeTwo : Bool
  excludeDiagonal : Bool
  deriving Repr

structure PrimeHorizonResult where
  denominator : Nat
  denominatorPrime : Bool
  twoAvailable : Bool
  diagonalExcluded : Bool
  decimalRepeatingCandidate : Bool
  kernelNumerator : Option Nat
  centralBoundaryNumerator : Option Nat
  centralGapNumerator : Option Nat
  lines : List ResearchLine
  deriving Repr

/-- Small deterministic primality search used only by the research calculator. -/
def firstPrimeFrom (n : Nat) : Nat :=
  Nat.find (Nat.exists_infinite_primes n)

theorem firstPrimeFrom_prime (n : Nat) :
    Nat.Prime (firstPrimeFrom n) := by
  exact (Nat.find_spec (Nat.exists_infinite_primes n)).1

theorem firstPrimeFrom_ge (n : Nat) :
    n ≤ firstPrimeFrom n := by
  exact (Nat.find_spec (Nat.exists_infinite_primes n)).2

/-- First admissible positive prime numerator for a fixed denominator under the
current research exclusions.  The diagonal exclusion removes p=q. -/
def firstAdmissibleNumerator (I : PrimeHorizonInput) : Nat :=
  let start := if I.excludeTwo then 3 else 2
  let p := firstPrimeFrom start
  if I.excludeDiagonal && p = I.denominator then
    firstPrimeFrom (p + 1)
  else p

def horizonLines (I : PrimeHorizonInput) : List ResearchLine :=
  let base := [ResearchLine.horizonPrime, .prime2]
  let base := if I.denominator = 3 then .geometricP012 :: base else base
  let base := if I.excludeTwo then .negativeResult :: base else base
  .encodingInvariant :: base

def calculatePrimeHorizon (I : PrimeHorizonInput) : PrimeHorizonResult :=
  let p := firstAdmissibleNumerator I
  { denominator := I.denominator
    denominatorPrime := decide (Nat.Prime I.denominator)
    twoAvailable := !I.excludeTwo
    diagonalExcluded := I.excludeDiagonal
    decimalRepeatingCandidate :=
      decide (Nat.Prime I.denominator ∧ I.denominator ≠ 2 ∧ I.denominator ≠ 5)
    kernelNumerator := if I.excludeTwo then none else some 2
    centralBoundaryNumerator := some p
    centralGapNumerator := some (2 * p)
    lines := horizonLines I }

/-- q=3 with 2 available: the operational kernel is ±2/3 and the central
reflection displacement has numerator 4. -/
def q3WithKernel : PrimeHorizonResult :=
  calculatePrimeHorizon
    { denominator := 3, excludeTwo := false, excludeDiagonal := true }

/-- q=3 with 2 excluded and p=q excluded: first admissible numerator is 5,
hence the symmetric central gap has numerator 10. -/
def q3OddPure : PrimeHorizonResult :=
  calculatePrimeHorizon
    { denominator := 3, excludeTwo := true, excludeDiagonal := true }

theorem q3_with_kernel_numerator :
    q3WithKernel.kernelNumerator = some 2 := by
  native_decide

theorem q3_with_kernel_boundary :
    q3WithKernel.centralBoundaryNumerator = some 2 := by
  native_decide

theorem q3_with_kernel_gap :
    q3WithKernel.centralGapNumerator = some 4 := by
  native_decide

theorem q3_odd_pure_boundary :
    q3OddPure.centralBoundaryNumerator = some 5 := by
  native_decide

theorem q3_odd_pure_gap :
    q3OddPure.centralGapNumerator = some 10 := by
  native_decide

/-- A counterexample witness discovered by any heuristic may only enter the
standard semantic lane through its raw BitString.  The tag is recorded for
analysis but ignored by CorrectAt. -/
structure TaggedWitnessObservation where
  raw : Real.CanonicalFinalProof.BitString
  tag : Option Nucleus
  sourceLine : ResearchLine
  strength : EvidenceStrength
  deriving Repr

def TaggedWitnessObservation.toPrime2Input
    (W : TaggedWitnessObservation) : Prime2BitString :=
  { raw := W.raw, nucleusTag := W.tag }

theorem tag_irrelevant_to_sat
    (W : TaggedWitnessObservation) :
    Prime2SAT W.toPrime2Input ↔
      Real.P02G21G22Attack.SATTarget W.raw := by
  rfl

theorem tag_irrelevant_to_correctAt
    (M : Prime2Candidate)
    (W : TaggedWitnessObservation) :
    Prime2CorrectAt M W.toPrime2Input ↔
      M.raw.CorrectAt Real.P02G21G22Attack.SATTarget W.raw := by
  rfl

/-- Suggested research lines are metadata only. -/
def linesForWitness (W : TaggedWitnessObservation) : List ResearchLine :=
  [W.sourceLine, .g21WitnessMap, .encodingInvariant]

#print axioms MCore.Research.PatternCalculator.q3_with_kernel_gap
#print axioms MCore.Research.PatternCalculator.q3_odd_pure_gap
#print axioms MCore.Research.PatternCalculator.tag_irrelevant_to_sat
#print axioms MCore.Research.PatternCalculator.tag_irrelevant_to_correctAt

end PatternCalculator
end Research
end MCore
