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

theorem phaseRuntimeUnit_pos
    (pad : Nat) (hpad : 0 < pad)
    (log : SlotLog) (bits : BitString) :
    0 < phaseRuntimeUnit pad log bits := by
  unfold phaseRuntimeUnit
  exact Nat.mul_pos (by decide) (phaseRuntimeScale_pos pad hpad log bits)

/-- If the local footprint scale is unchanged, one unit pays for the concrete
prefix and the residual budget strictly decreases with unread-source length. -/
theorem budget_compose_same_scale
    (S parentLen childLen prefixSteps : Nat)
    (hlt : childLen < parentLen)
    (hprefix : prefixSteps ≤ 16 * S) :
    prefixSteps + (16 * S * (childLen + 1)) ≤
      16 * S * (parentLen + 1) := by
  have hlen : childLen + 2 ≤ parentLen + 1 := by omega
  have hmul :
      16 * S * (childLen + 2) ≤
        16 * S * (parentLen + 1) :=
    Nat.mul_le_mul_left (16 * S) hlen
  calc
    prefixSteps + (16 * S * (childLen + 1))
        ≤ 16 * S + (16 * S * (childLen + 1)) :=
      Nat.add_le_add_right hprefix _
    _ = 16 * S * (childLen + 2) := by
      rw [show childLen + 2 = Nat.succ (childLen + 1) by omega]
      rw [Nat.mul_succ]
      exact Nat.add_comm _ _
    _ ≤ 16 * S * (parentLen + 1) := hmul

/-- Binary heads add one tombstone-log cell but consume three source bits.
The extra scale cell is absorbed by the three-bit source decrease. -/
theorem budget_compose_scale_succ
    (S parentLen childLen prefixSteps : Nat)
    (hchildScale : childLen + 1 ≤ S)
    (hconsume : childLen + 3 ≤ parentLen)
    (hprefix : prefixSteps ≤ 16 * S) :
    prefixSteps + (16 * (S + 1) * (childLen + 1)) ≤
      16 * S * (parentLen + 1) := by
  have hscale :
      (S + 1) * (childLen + 1) ≤ S * (childLen + 2) := by
    calc
      (S + 1) * (childLen + 1)
          = S * (childLen + 1) + (childLen + 1) := by
        rw [show S + 1 = Nat.succ S by omega]
        rw [Nat.succ_mul]
      _ ≤ S * (childLen + 1) + S :=
        Nat.add_le_add_left hchildScale _
      _ = S * (childLen + 2) := by
        rw [show childLen + 2 = Nat.succ (childLen + 1) by omega]
        rw [Nat.mul_succ]
        simp only [Nat.mul_succ, Nat.add_assoc]
  have hscale16 :
      16 * ((S + 1) * (childLen + 1)) ≤
        16 * (S * (childLen + 2)) :=
    Nat.mul_le_mul_left 16 hscale
  have hchild :
      16 * (S + 1) * (childLen + 1) ≤
        16 * S * (childLen + 2) := by
    simpa [Nat.mul_assoc] using hscale16
  have hprechild :
      prefixSteps + (16 * (S + 1) * (childLen + 1)) ≤
        16 * S + (16 * S * (childLen + 2)) :=
    Nat.add_le_add hprefix hchild
  have hlen : childLen + 3 ≤ parentLen + 1 := by omega
  have hmul :
      16 * S * (childLen + 3) ≤
        16 * S * (parentLen + 1) :=
    Nat.mul_le_mul_left (16 * S) hlen
  calc
    prefixSteps + (16 * (S + 1) * (childLen + 1))
        ≤ 16 * S + (16 * S * (childLen + 2)) := hprechild
    _ = 16 * S * (childLen + 3) := by
      rw [show childLen + 3 = Nat.succ (childLen + 2) by omega]
      rw [Nat.mul_succ]
      exact Nat.add_comm _ _
    _ ≤ 16 * S * (parentLen + 1) := hmul

theorem phaseBudget_positive
    (pad : Nat) (hpad : 0 < pad)
    (log : SlotLog) (bits : BitString) :
    0 < phaseRuntimeBudget pad log bits := by
  unfold phaseRuntimeBudget
  exact Nat.mul_pos
    (phaseRuntimeUnit_pos pad hpad log bits)
    (by omega)

#print axioms MCore.Real.P01GlobalParserBound.budget_compose_same_scale
#print axioms MCore.Real.P01GlobalParserBound.budget_compose_scale_succ

end P01GlobalParserBound
end Real
end MCore
