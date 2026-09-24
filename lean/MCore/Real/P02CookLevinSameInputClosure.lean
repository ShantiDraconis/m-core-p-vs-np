import MCore.Real.P02KleeneCookLevinBridge
import MCore.Real.P02ResidualSameInputBridge

namespace MCore
namespace Real
namespace P02CookLevinSameInputClosure

open CanonicalFinalProof
open CanonicalCircuitBits
open P02KleeneBridge
open P02KleeneCookLevinBridge

structure CookLevinCarrierData
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M) where
  circuitOf : Nat.Partrec.Code → CircuitK1.Circuit
  selfInput : Nat.Partrec.Code → BitString

def CookLevinCorrect
    {M : PolyDTMCandidate}
    {K : EffectiveDiagonalCompiler M}
    (C : CookLevinCarrierData M K) : Prop :=
  ∀ c,
    SATTarget (encodeCircuit (C.circuitOf c)) ↔
      ¬ AcceptsAtDeclaredBound M (C.selfInput c)

def SameInputOfFixed
    {M : PolyDTMCandidate}
    {K : EffectiveDiagonalCompiler M}
    (C : CookLevinCarrierData M K) : Prop :=
  ∀ c,
    Nat.Partrec.Code.eval c = K.f c →
      C.selfInput c = encodeCircuit (C.circuitOf c)

def assembleCookLevinSameInputData
    {M : PolyDTMCandidate}
    {K : EffectiveDiagonalCompiler M}
    (C : CookLevinCarrierData M K)
    (hCook : CookLevinCorrect C)
    (hSame : SameInputOfFixed C) :
    CookLevinSameInputData M K where
  circuitOf := C.circuitOf
  selfInput := C.selfInput
  cook_levin_correct := hCook
  same_input_of_fixed := hSame

theorem closes_flips_of_fixed
    {M : PolyDTMCandidate}
    {K : EffectiveDiagonalCompiler M}
    (C : CookLevinCarrierData M K)
    (hCook : CookLevinCorrect C)
    (hSame : SameInputOfFixed C)
    (c : Nat.Partrec.Code)
    (hfixed : Nat.Partrec.Code.eval c = K.f c) :
    SATTarget ((assembleCookLevinSameInputData C hCook hSame).bitsOf c) ↔
      ¬ AcceptsAtDeclaredBound M
        ((assembleCookLevinSameInputData C hCook hSame).bitsOf c) :=
  (assembleCookLevinSameInputData C hCook hSame).flips_of_fixed c hfixed

/-
cook_levin_correct requires:
- a concrete effective tableau/circuit construction for bounded execution;
- proof that canonical SAT of the encoded circuit is equivalent to the
  intended negated bounded acceptance statement;
- encoder/decoder correctness and size/time bookkeeping;
- no endpoint proposition as an assumption.

same_input_of_fixed requires:
- selfInput tied to the same code/circuit carrier;
- transport from Kleene equality eval c = K.f c to concrete BitString equality;
- compiler/self-code/canonical-encoder extensional agreement;
- no literal BitString fixed-point assumption.

ResidualRotation may contribute only by constructing the already-defined
ResidualSameInputInvariant; it cannot replace SameInputOfFixed.
-/

#print axioms MCore.Real.P02CookLevinSameInputClosure.closes_flips_of_fixed

end P02CookLevinSameInputClosure
end Real
end MCore
