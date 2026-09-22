import Mathlib
import MCore.Real.P02UniversalFailureAlgebra

namespace MCore.Real.OpenMathCore

open CanonicalFinalProof

def bitNat : Bool → Nat
  | false => 0
  | true => 1

def bitWeight (x : BitString) : Nat :=
  x.foldl (fun acc b => acc + bitNat b) 0

def bitLength (x : BitString) : Nat := x.length

def arithmeticMass (x : BitString) : Nat :=
  bitLength x + bitWeight x

@[simp] theorem bitLength_nil : bitLength ([] : BitString) = 0 := rfl

@[simp] theorem bitLength_append (x y : BitString) :
    bitLength (x ++ y) = bitLength x + bitLength y := by
  simp [bitLength]

theorem bitWeight_le_length (x : BitString) :
    bitWeight x ≤ bitLength x := by
  unfold bitWeight bitLength
  induction x with
  | nil => simp
  | cons b xs ih =>
      simp [List.foldl_cons, bitNat]
      cases b <;> simp_all <;> omega

structure ArithmeticLaw where
  measure : BitString → Nat
  nonnegative : ∀ x, 0 ≤ measure x
  append_bound : ∀ x y, measure (x ++ y) ≤ measure x + measure y + (x.length + y.length)

def arithmeticMassLaw : ArithmeticLaw where
  measure := arithmeticMass
  nonnegative := by intro x; omega
  append_bound := by
    intro x y
    unfold arithmeticMass bitLength
    have hx := bitWeight_le_length x
    have hy := bitWeight_le_length y
    simp [bitWeight]
    omega

end MCore.Real.OpenMathCore
