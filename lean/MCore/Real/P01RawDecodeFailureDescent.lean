import MCore.Real.P01RawDecodeFailureShape
import MCore.Real.P01RawDecoderSound

namespace MCore
namespace Real
namespace P01RawDecodeFailureDescent

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open P01RawDecodeFailureShape
open P01RawDecoderSound

/-- Every circuit encoding consumes at least three source bits. -/
theorem three_le_encodeCircuit_length
    (phi : Circuit) :
    3 ≤ (encodeCircuit phi).length := by
  cases phi <;> simp [encodeCircuit]

/-- Parent/child relation for exactly the five recursive decoder-failure
constructors.  Local failures (short tag, invalid tag, bad unary) have no
child and are handled by direct physical rejectors. -/
inductive RawFailureChild : BitString → BitString → Prop
  | notChild
      (fuel : Nat) (rest : BitString)
      (h : decodeCircuitCore fuel rest = none) :
      RawFailureChild
        (false :: true :: true :: rest) rest
  | andLeft
      (fuel : Nat) (rest : BitString)
      (h : decodeCircuitCore fuel rest = none) :
      RawFailureChild
        (true :: false :: false :: rest) rest
  | andRight
      (fuel : Nat) (rest : BitString)
      (left : Circuit) (rightSource : BitString)
      (hleft :
        decodeCircuitCore fuel rest = some (left, rightSource))
      (hright :
        decodeCircuitCore fuel rightSource = none) :
      RawFailureChild
        (true :: false :: false :: rest) rightSource
  | orLeft
      (fuel : Nat) (rest : BitString)
      (h : decodeCircuitCore fuel rest = none) :
      RawFailureChild
        (true :: false :: true :: rest) rest
  | orRight
      (fuel : Nat) (rest : BitString)
      (left : Circuit) (rightSource : BitString)
      (hleft :
        decodeCircuitCore fuel rest = some (left, rightSource))
      (hright :
        decodeCircuitCore fuel rightSource = none) :
      RawFailureChild
        (true :: false :: true :: rest) rightSource

/-- Recursive decoder failure always shrinks the raw source strictly.
This is the forward-only / no-loop measure for raw totalization. -/
theorem rawFailureChild_length_lt
    {parent child : BitString}
    (h : RawFailureChild parent child) :
    child.length < parent.length := by
  cases h with
  | notChild fuel rest hnone =>
      simp
  | andLeft fuel rest hnone =>
      simp
  | orLeft fuel rest hnone =>
      simp
  | andRight fuel rest left rightSource hleft hright =>
      have hs :
          rest = encodeCircuit left ++ rightSource :=
        decodeCircuitCore_success_sound
          fuel rest left rightSource hleft
      have hlen := three_le_encodeCircuit_length left
      rw [hs]
      simp [List.length_append]
      omega
  | orRight fuel rest left rightSource hleft hright =>
      have hs :
          rest = encodeCircuit left ++ rightSource :=
        decodeCircuitCore_success_sound
          fuel rest left rightSource hleft
      have hlen := three_le_encodeCircuit_length left
      rw [hs]
      simp [List.length_append]
      omega

/-- Unary decoder failure is exactly an unterminated all-true unary word. -/
theorem decodeNat_none_replicate_true :
    ∀ (bits : BitString),
      decodeNat bits = none →
        ∃ k : Nat, bits = List.replicate k true := by
  intro bits
  induction bits with
  | nil =>
      intro h
      exact ⟨0, rfl⟩
  | cons b rest ih =>
      intro h
      cases b with
      | false =>
          simp [decodeNat] at h
      | true =>
          cases hr : decodeNat rest with
          | none =>
              rcases ih (by simpa using hr) with ⟨k, hk⟩
              refine ⟨k + 1, ?_⟩
              simp [hk, List.replicate_succ]
          | some p =>
              simp [decodeNat, hr] at h

/-- The inputUnary failure constructor therefore has exactly the physical
source shape consumed by prepared_truncated_unary_fail_closed. -/
theorem inputUnary_source_shape
    (fuel : Nat) (rest : BitString)
    (h : decodeNat rest = none) :
    ∃ k : Nat,
      (false :: false :: false :: rest) =
        false :: false :: false :: List.replicate k true := by
  rcases decodeNat_none_replicate_true rest h with ⟨k, rfl⟩
  exact ⟨k, rfl⟩

#print axioms MCore.Real.P01RawDecodeFailureDescent.rawFailureChild_length_lt
#print axioms MCore.Real.P01RawDecodeFailureDescent.decodeNat_none_replicate_true
#print axioms MCore.Real.P01RawDecodeFailureDescent.inputUnary_source_shape

end P01RawDecodeFailureDescent
end Real
end MCore
