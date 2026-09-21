import MCore.Real.CanonicalCircuitBitsInverse

namespace MCore
namespace Real
namespace CanonicalSATSlotParserSpec

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalCircuitBitsInverse

/-- Parse exactly one constructor token and return its arity plus the remaining
bitstring. INPUT consumes its unary natural-number payload here; no Nat is
stored in machine control. -/
def tokenArity : BitString → Option (Nat × BitString)
  | false :: false :: false :: rest =>
      match decodeNat rest with
      | some (_, tail) => some (0, tail)
      | none => none
  | false :: false :: true :: rest => some (0, rest)
  | false :: true :: false :: rest => some (0, rest)
  | false :: true :: true :: rest => some (1, rest)
  | true :: false :: false :: rest => some (2, rest)
  | true :: false :: true :: rest => some (2, rest)
  | _ => none

/-- Prefix-tree slot recognizer. The slot count is the number of subtrees still
required. A token consumes one slot and opens arity new slots. -/
def slotParseCore : Nat → Nat → BitString → Bool
  | 0, _, _ => false
  | _ + 1, 0, bits => bits.isEmpty
  | fuel + 1, slots + 1, bits =>
      match tokenArity bits with
      | none => false
      | some (arity, rest) =>
          slotParseCore fuel (slots + arity) rest

/-- Public total recognizer. Input length supplies more fuel than the number
of AST nodes because every constructor uses at least three bits. -/
def slotAccept (bits : BitString) : Bool :=
  slotParseCore (bits.length + 1) 1 bits

@[simp] theorem tokenArity_input
    (i : Nat) (tail : BitString) :
    tokenArity (encodeCircuit (.input i) ++ tail) = some (0, tail) := by
  simp [tokenArity, encodeCircuit, decodeNat_encodeNat_append, List.append_assoc]

@[simp] theorem tokenArity_const
    (b : Bool) (tail : BitString) :
    tokenArity (encodeCircuit (.const b) ++ tail) = some (0, tail) := by
  cases b <;> simp [tokenArity, encodeCircuit]

@[simp] theorem tokenArity_not
    (c : Circuit) (tail : BitString) :
    tokenArity (encodeCircuit (.not c) ++ tail) =
      some (1, encodeCircuit c ++ tail) := by
  simp [tokenArity, encodeCircuit, List.append_assoc]

@[simp] theorem tokenArity_and
    (a b : Circuit) (tail : BitString) :
    tokenArity (encodeCircuit (.and a b) ++ tail) =
      some (2, encodeCircuit a ++ encodeCircuit b ++ tail) := by
  simp [tokenArity, encodeCircuit, List.append_assoc]

@[simp] theorem tokenArity_or
    (a b : Circuit) (tail : BitString) :
    tokenArity (encodeCircuit (.or a b) ++ tail) =
      some (2, encodeCircuit a ++ encodeCircuit b ++ tail) := by
  simp [tokenArity, encodeCircuit, List.append_assoc]

/-- Strong compositional theorem: parsing one canonical Circuit consumes
exactly size c macro steps and exactly one outstanding slot, independently
of the surrounding forest represented by slots and tail. -/
theorem slotParseCore_encode_append
    (c : Circuit)
    (tail : BitString)
    (slots fuel : Nat) :
    slotParseCore (CircuitK1.size c + fuel) (slots + 1)
        (encodeCircuit c ++ tail) =
      slotParseCore fuel slots tail := by
  induction c generalizing tail slots fuel with
  | input i =>
      simp [CircuitK1.size, slotParseCore, tokenArity_input,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | const b =>
      cases b <;>
        simp [CircuitK1.size, slotParseCore, tokenArity_const,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | not c ih =>
      simp [CircuitK1.size, slotParseCore, tokenArity_not, ih,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, List.append_assoc]
  | and a b iha ihb =>
      simp [CircuitK1.size, slotParseCore, tokenArity_and, iha, ihb,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, List.append_assoc]
  | or a b iha ihb =>
      simp [CircuitK1.size, slotParseCore, tokenArity_or, iha, ihb,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, List.append_assoc]

/-- Every canonical encoding is accepted by the slot recognizer. -/
theorem slotAccept_encodeCircuit
    (c : Circuit) :
    slotAccept (encodeCircuit c) = true := by
  have hSize :
      CircuitK1.size c ≤ (encodeCircuit c).length :=
    size_le_encodeCircuit_length c
  obtain ⟨extra, hEq⟩ :
      ∃ extra : Nat,
        (encodeCircuit c).length + 1 =
          CircuitK1.size c + (extra + 1) := by
    use (encodeCircuit c).length - CircuitK1.size c
    omega
  unfold slotAccept
  rw [hEq]
  rw [slotParseCore_encode_append c [] 0 (extra + 1)]
  simp [slotParseCore]

/-- Invalid constructor prefix 11 is rejected for every positive fuel. -/
theorem slotParse_invalid_11
    (fuel slots : Nat)
    (third : Bool)
    (tail : BitString) :
    slotParseCore (fuel + 1) (slots + 1)
      (true :: true :: third :: tail) = false := by
  simp [slotParseCore, tokenArity]

/-- A truncated tag cannot be accepted. -/
theorem slotParse_truncated_tag
    (fuel slots : Nat)
    (b1 b2 : Bool) :
    slotParseCore (fuel + 1) (slots + 1) [b1, b2] = false := by
  cases b1 <;> cases b2 <;> simp [slotParseCore, tokenArity]

/-- An INPUT token whose unary payload never reaches its false terminator is
rejected. -/
theorem tokenArity_truncated_input
    (ones : Nat) :
    tokenArity
      ([false, false, false] ++ List.replicate ones true) = none := by
  induction ones with
  | zero =>
      simp [tokenArity, decodeNat]
  | succ n ih =>
      simp [tokenArity, decodeNat, List.replicate_succ, ih]

#print axioms MCore.Real.CanonicalSATSlotParserSpec.tokenArity_input
#print axioms MCore.Real.CanonicalSATSlotParserSpec.slotParseCore_encode_append
#print axioms MCore.Real.CanonicalSATSlotParserSpec.slotAccept_encodeCircuit
#print axioms MCore.Real.CanonicalSATSlotParserSpec.slotParse_invalid_11
#print axioms MCore.Real.CanonicalSATSlotParserSpec.slotParse_truncated_tag
#print axioms MCore.Real.CanonicalSATSlotParserSpec.tokenArity_truncated_input

end CanonicalSATSlotParserSpec
end Real
end MCore
