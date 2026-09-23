import MCore.Research.Prime2FractionalHorizon

namespace MCore
namespace Research
namespace PatternCalculator

open Prime2
open MCore.P012

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

def firstPrimeFromAux (n fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if decide (PrimeNat n) then some n
      else firstPrimeFromAux (n + 1) fuel

def firstPrimeFrom (n : Nat) : Option Nat :=
  firstPrimeFromAux n 4096

def firstAdmissibleNumerator (I : PrimeHorizonInput) : Option Nat :=
  let start := if I.excludeTwo then 3 else 2
  match firstPrimeFrom start with
  | none => none
  | some p =>
      if I.excludeDiagonal && p = I.denominator then
        firstPrimeFrom (p + 1)
      else some p

def horizonLines (I : PrimeHorizonInput) : List ResearchLine :=
  let base := [ResearchLine.horizonPrime, .prime2]
  let base := if I.denominator = 3 then .geometricP012 :: base else base
  let base := if I.excludeTwo then .negativeResult :: base else base
  .encodingInvariant :: base

def calculatePrimeHorizon (I : PrimeHorizonInput) : PrimeHorizonResult :=
  let p := firstAdmissibleNumerator I
  { denominator := I.denominator
    denominatorPrime := decide (PrimeNat I.denominator)
    twoAvailable := !I.excludeTwo
    diagonalExcluded := I.excludeDiagonal
    decimalRepeatingCandidate :=
      decide (PrimeNat I.denominator ∧ I.denominator ≠ 2 ∧ I.denominator ≠ 5)
    kernelNumerator := if I.excludeTwo then none else some 2
    centralBoundaryNumerator := p
    centralGapNumerator := p.map (fun n => 2 * n)
    lines := horizonLines I }

def q3WithKernel : PrimeHorizonResult :=
  calculatePrimeHorizon
    { denominator := 3, excludeTwo := false, excludeDiagonal := true }

def q3OddPure : PrimeHorizonResult :=
  calculatePrimeHorizon
    { denominator := 3, excludeTwo := true, excludeDiagonal := true }

theorem q3_with_kernel_numerator :
    q3WithKernel.kernelNumerator = some 2 := by decide

theorem q3_with_kernel_boundary :
    q3WithKernel.centralBoundaryNumerator = some 2 := by decide

theorem q3_with_kernel_gap :
    q3WithKernel.centralGapNumerator = some 4 := by decide

theorem q3_odd_pure_boundary :
    q3OddPure.centralBoundaryNumerator = some 5 := by decide

theorem q3_odd_pure_gap :
    q3OddPure.centralGapNumerator = some 10 := by decide

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

def linesForWitness (W : TaggedWitnessObservation) : List ResearchLine :=
  [W.sourceLine, .g21WitnessMap, .encodingInvariant]

#print axioms MCore.Research.PatternCalculator.q3_with_kernel_gap
#print axioms MCore.Research.PatternCalculator.q3_odd_pure_gap
#print axioms MCore.Research.PatternCalculator.tag_irrelevant_to_sat
#print axioms MCore.Research.PatternCalculator.tag_irrelevant_to_correctAt

end PatternCalculator
end Research
end MCore
