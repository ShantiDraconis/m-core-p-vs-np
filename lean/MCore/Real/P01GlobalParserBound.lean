import MCore.Real.P01GlobalParserRuntime

namespace MCore
namespace Real
namespace P01GlobalParserBound

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATParserHeadProof
open CanonicalSATSlotParserSpec
open CanonicalSATSlotLog
open MachineRunLemmas
open P01GlobalParserSimulation
open P01GlobalParserRuntime

/-- Local tape-footprint scale used only for the runtime proof. -/
def phaseRuntimeScale
    (pad : Nat) (log : SlotLog) (bits : BitString) : Nat :=
  pad + bits.length + log.length + 1

/-- One macro-step allowance at a fixed local footprint. -/
def phaseRuntimeUnit
    (pad : Nat) (log : SlotLog) (bits : BitString) : Nat :=
  16 * phaseRuntimeScale pad log bits

/-- Quadratic phase budget. Every successful head strictly shortens bits. -/
def phaseRuntimeBudget
    (pad : Nat) (log : SlotLog) (bits : BitString) : Nat :=
  phaseRuntimeUnit pad log bits * (bits.length + 1)

theorem phaseRuntimeScale_pos
    (pad : Nat) (hpad : 0 < pad)
    (log : SlotLog) (bits : BitString) :
    0 < phaseRuntimeScale pad log bits := by
  simp [phaseRuntimeScale]
  omega

theorem phaseRuntimeUnit_pos
    (pad : Nat) (hpad : 0 < pad)
    (log : SlotLog) (bits : BitString) :
    0 < phaseRuntimeUnit pad log bits := by
  unfold phaseRuntimeUnit
  have hs := phaseRuntimeScale_pos pad hpad log bits
  omega

/-- If the local footprint scale is unchanged, one unit pays for the concrete
prefix and the residual budget strictly decreases with unread-source length. -/
theorem budget_compose_same_scale
    (S parentLen childLen prefix : Nat)
    (hlt : childLen < parentLen)
    (hprefix : prefix ≤ 16 * S) :
    prefix + (16 * S * (childLen + 1)) ≤
      16 * S * (parentLen + 1) := by
  have hlen : childLen + 2 ≤ parentLen + 1 := by omega
  have hmul :
      16 * S * (childLen + 2) ≤
        16 * S * (parentLen + 1) :=
    Nat.mul_le_mul_left (16 * S) hlen
  calc
    prefix + (16 * S * (childLen + 1))
        ≤ 16 * S + (16 * S * (childLen + 1)) :=
      Nat.add_le_add_right hprefix _
    _ = 16 * S * (childLen + 2) := by ring
    _ ≤ 16 * S * (parentLen + 1) := hmul

/-- Binary heads add one tombstone-log cell but consume three source bits.
The extra scale cell is absorbed by the three-bit source decrease. -/
theorem budget_compose_scale_succ
    (S parentLen childLen prefix : Nat)
    (hchildScale : childLen + 1 ≤ S)
    (hconsume : childLen + 3 ≤ parentLen)
    (hprefix : prefix ≤ 16 * S) :
    prefix + (16 * (S + 1) * (childLen + 1)) ≤
      16 * S * (parentLen + 1) := by
  have hscale :
      (S + 1) * (childLen + 1) ≤ S * (childLen + 2) := by
    calc
      (S + 1) * (childLen + 1)
          = S * (childLen + 1) + (childLen + 1) := by ring
      _ ≤ S * (childLen + 1) + S :=
        Nat.add_le_add_left hchildScale _
      _ = S * (childLen + 2) := by ring
  have hscale16 :
      16 * ((S + 1) * (childLen + 1)) ≤
        16 * (S * (childLen + 2)) :=
    Nat.mul_le_mul_left 16 hscale
  have hchild :
      16 * (S + 1) * (childLen + 1) ≤
        16 * S * (childLen + 2) := by
    simpa [Nat.mul_assoc] using hscale16
  have hprechild :
      prefix + (16 * (S + 1) * (childLen + 1)) ≤
        16 * S + (16 * S * (childLen + 2)) :=
    Nat.add_le_add hprefix hchild
  have hlen : childLen + 3 ≤ parentLen + 1 := by omega
  have hmul :
      16 * S * (childLen + 3) ≤
        16 * S * (parentLen + 1) :=
    Nat.mul_le_mul_left (16 * S) hlen
  calc
    prefix + (16 * (S + 1) * (childLen + 1))
        ≤ 16 * S + (16 * S * (childLen + 2)) := hprechild
    _ = 16 * S * (childLen + 3) := by ring
    _ ≤ 16 * S * (parentLen + 1) := hmul

theorem phaseBudget_positive
    (pad : Nat) (hpad : 0 < pad)
    (log : SlotLog) (bits : BitString) :
    0 < phaseRuntimeBudget pad log bits := by
  unfold phaseRuntimeBudget
  have hu := phaseRuntimeUnit_pos pad hpad log bits
  omega

#print axioms MCore.Real.P01GlobalParserBound.budget_compose_same_scale
#print axioms MCore.Real.P01GlobalParserBound.budget_compose_scale_succ

end P01GlobalParserBound
end Real
end MCore
