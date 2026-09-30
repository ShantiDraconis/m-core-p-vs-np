import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P01CoreFailureClassification

open CanonicalFinalProof
open CanonicalCircuitBits
open CircuitK1

/-- Exhaustive causes of failure of the actual bounded circuit decoder.
No endpoint proposition is stored here: each constructor records one concrete
branch of the recursive definition of `decodeCircuitCore`. -/
inductive CoreFailureCause : Nat → BitString → Type
  | fuelZero (bits : BitString) :
      CoreFailureCause 0 bits
  | short0 (fuel : Nat) :
      CoreFailureCause (fuel + 1) []
  | short1 (fuel : Nat) (b0 : Bool) :
      CoreFailureCause (fuel + 1) [b0]
  | short2 (fuel : Nat) (b0 b1 : Bool) :
      CoreFailureCause (fuel + 1) [b0, b1]
  | invalid110 (fuel : Nat) (rest : BitString) :
      CoreFailureCause (fuel + 1) (true :: true :: false :: rest)
  | invalid111 (fuel : Nat) (rest : BitString) :
      CoreFailureCause (fuel + 1) (true :: true :: true :: rest)
  | inputUnary (fuel : Nat) (rest : BitString)
      (h : decodeNat rest = none) :
      CoreFailureCause (fuel + 1) (false :: false :: false :: rest)
  | negChild (fuel : Nat) (rest : BitString)
      (h : decodeCircuitCore fuel rest = none) :
      CoreFailureCause (fuel + 1) (false :: true :: true :: rest)
  | andLeft (fuel : Nat) (rest : BitString)
      (h : decodeCircuitCore fuel rest = none) :
      CoreFailureCause (fuel + 1) (true :: false :: false :: rest)
  | andRight (fuel : Nat) (rest : BitString)
      (a : Circuit) (rest' : BitString)
      (hleft : decodeCircuitCore fuel rest = some (a, rest'))
      (hright : decodeCircuitCore fuel rest' = none) :
      CoreFailureCause (fuel + 1) (true :: false :: false :: rest)
  | orLeft (fuel : Nat) (rest : BitString)
      (h : decodeCircuitCore fuel rest = none) :
      CoreFailureCause (fuel + 1) (true :: false :: true :: rest)
  | orRight (fuel : Nat) (rest : BitString)
      (a : Circuit) (rest' : BitString)
      (hleft : decodeCircuitCore fuel rest = some (a, rest'))
      (hright : decodeCircuitCore fuel rest' = none) :
      CoreFailureCause (fuel + 1) (true :: false :: true :: rest)

/-- Every failure of the repository's real decoder has one of the concrete
causes above.  This theorem is a direct inversion of `decodeCircuitCore`. -/
def classifyCoreFailure :
    ∀ (fuel : Nat) (bits : BitString),
      decodeCircuitCore fuel bits = none →
      CoreFailureCause fuel bits
  | 0, bits, _ =>
      .fuelZero bits
  | fuel + 1, bits, h => by
      cases bits with
      | nil =>
          exact .short0 fuel
      | cons b0 r0 =>
          cases r0 with
          | nil =>
              exact .short1 fuel b0
          | cons b1 r1 =>
              cases r1 with
              | nil =>
                  exact .short2 fuel b0 b1
              | cons b2 rest =>
                  cases b0 <;> cases b1 <;> cases b2
                  · have hn : decodeNat rest = none := by
                      simpa [decodeCircuitCore] using h
                    exact .inputUnary fuel rest hn
                  · simp [decodeCircuitCore] at h
                  · simp [decodeCircuitCore] at h
                  · cases hc : decodeCircuitCore fuel rest with
                    | none =>
                        exact .negChild fuel rest hc
                    | some p =>
                        rcases p with ⟨c, tail⟩
                        simp [decodeCircuitCore, hc] at h
                  · cases hl : decodeCircuitCore fuel rest with
                    | none =>
                        exact .andLeft fuel rest hl
                    | some p =>
                        rcases p with ⟨a, rest'⟩
                        cases hr : decodeCircuitCore fuel rest' with
                        | none =>
                            exact .andRight fuel rest a rest' hl hr
                        | some q =>
                            rcases q with ⟨b, tail⟩
                            simp [decodeCircuitCore, hl, hr] at h
                  · cases hl : decodeCircuitCore fuel rest with
                    | none =>
                        exact .orLeft fuel rest hl
                    | some p =>
                        rcases p with ⟨a, rest'⟩
                        cases hr : decodeCircuitCore fuel rest' with
                        | none =>
                            exact .orRight fuel rest a rest' hl hr
                        | some q =>
                            rcases q with ⟨b, tail⟩
                            simp [decodeCircuitCore, hl, hr] at h
                  · exact .invalid110 fuel rest
                  · exact .invalid111 fuel rest

/-- For the actual whole-source fuel, fuel exhaustion itself is impossible
unless the source is empty only after recursive consumption; the classifier
therefore exposes every remaining recursive failure branch explicitly. -/
theorem wholeSource_core_failure_classified
    (bits : BitString)
    (h : decodeCircuitCore (bits.length + 1) bits = none) :
    CoreFailureCause (bits.length + 1) bits :=
  classifyCoreFailure (bits.length + 1) bits h

#print axioms MCore.Real.P01CoreFailureClassification.classifyCoreFailure
#print axioms MCore.Real.P01CoreFailureClassification.wholeSource_core_failure_classified

end P01CoreFailureClassification
end Real
end MCore
