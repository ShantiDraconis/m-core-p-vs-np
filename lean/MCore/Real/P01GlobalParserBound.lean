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
      simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
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
        simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
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
      simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ ≤ 16 * S * (parentLen + 1) := hmul

theorem phaseBudget_positive
    (pad : Nat) (hpad : 0 < pad)
    (log : SlotLog) (bits : BitString) :
    0 < phaseRuntimeBudget pad log bits := by
  unfold phaseRuntimeBudget
  exact Nat.mul_pos
    (phaseRuntimeUnit_pos pad hpad log bits)
    (by omega)


/-- One local runtime unit is always contained in the quadratic phase budget. -/
theorem phaseRuntimeUnit_le_budget
    (pad : Nat) (log : SlotLog) (bits : BitString) :
    phaseRuntimeUnit pad log bits ≤ phaseRuntimeBudget pad log bits := by
  unfold phaseRuntimeBudget
  have h : 1 ≤ bits.length + 1 := by omega
  have hm :=
    Nat.mul_le_mul_left (phaseRuntimeUnit pad log bits) h
  simpa using hm

/-- Every exact head/work/return prefix used by a recursive parser phase fits
inside one local runtime unit. -/
theorem phasePrefixLinear_le_unit
    (pad : Nat) (hpad : 0 < pad)
    (head : Head) (tail : BitString) (log : SlotLog) :
    CanonicalSATParserPhaseMacroProof.headWorkFuel
        head tail.length log.length +
      (log.length + tail.length + 2) ≤
        phaseRuntimeUnit pad log (head.encode ++ tail) := by
  unfold phaseRuntimeUnit phaseRuntimeScale
  unfold CanonicalSATParserPhaseMacroProof.headWorkFuel
  unfold CanonicalSATParserMacroProof.phaseWorkBound
  simp only [List.length_append]
  omega

theorem phasePrefixTerminal_le_unit
    (pad : Nat) (hpad : 0 < pad)
    (head : Head) (tail : BitString) (log : SlotLog) :
    CanonicalSATParserPhaseMacroProof.headWorkFuel
        head tail.length log.length +
      (log.length + 2) ≤
        phaseRuntimeUnit pad log (head.encode ++ tail) := by
  have h := phasePrefixLinear_le_unit pad hpad head tail log
  omega

theorem phasePrefixNot_le_unit
    (pad : Nat) (hpad : 0 < pad)
    (tail : BitString) (log : SlotLog) :
    (Head.encode .not).length ≤
      phaseRuntimeUnit pad log (Head.encode .not ++ tail) := by
  unfold phaseRuntimeUnit phaseRuntimeScale
  simp only [List.length_append]
  omega

theorem phaseRuntimeScale_same
    (pad : Nat) (head : Head)
    (tail : BitString) (log : SlotLog) :
    phaseRuntimeScale
        (pad + head.encode.length) log tail =
      phaseRuntimeScale pad log (head.encode ++ tail) := by
  unfold phaseRuntimeScale
  simp only [List.length_append]
  omega

theorem phaseRuntimeScale_pop_same
    (pad : Nat) (head : Head)
    (tail : BitString) (log log' : SlotLog)
    (hpop : popSlot log = some log') :
    phaseRuntimeScale
        (pad + head.encode.length) log' tail =
      phaseRuntimeScale pad log (head.encode ++ tail) := by
  have hlen := popSlot_length hpop
  unfold phaseRuntimeScale
  simp only [List.length_append]
  rw [hlen]
  omega

theorem phaseRuntimeScale_push_succ
    (pad : Nat) (head : Head)
    (tail : BitString) (log : SlotLog) :
    phaseRuntimeScale
        (pad + head.encode.length) (pushSlot log) tail =
      phaseRuntimeScale pad log (head.encode ++ tail) + 1 := by
  unfold phaseRuntimeScale
  simp [CanonicalSATSlotLog.pushSlot, List.length_append]
  omega

theorem parser_halts_after_exact_prefix
    (parent child : Configuration (Fin 25) (Option Bool))
    (prefixSteps childBudget : Nat)
    (hprefix :
      parserMachine.run prefixSteps parent = child)
    (hchild :
      parserMachine.HaltsWithin childBudget child) :
    parserMachine.HaltsWithin (prefixSteps + childBudget) parent := by
  unfold TM.HaltsWithin at hchild ⊢
  rw [MachineRunLemmas.run_add, hprefix]
  exact hchild

theorem parser_halts_after_rightBlank_prefix
    (parent child : Configuration (Fin 25) (Option Bool))
    (prefixSteps childBudget : Nat)
    (hprefix :
      ConfigRightBlankEq
        (parserMachine.run prefixSteps parent) child)
    (hchild :
      parserMachine.HaltsWithin childBudget child) :
    parserMachine.HaltsWithin (prefixSteps + childBudget) parent := by
  unfold TM.HaltsWithin at hchild ⊢
  rw [MachineRunLemmas.run_add]
  have hrun :=
    parser_run_respects_right_blank childBudget hprefix
  rw [hrun.1]
  exact hchild


theorem parser_terminal_halt_to_budget
    (pad : Nat) (log : SlotLog) (bits : BitString)
    (steps : Nat)
    (hsteps : steps ≤ phaseRuntimeUnit pad log bits)
    (hhalt :
      parserMachine.HaltsWithin steps (phaseConfig 4 pad bits log)) :
    parserMachine.HaltsWithin
      (phaseRuntimeBudget pad log bits)
      (phaseConfig 4 pad bits log) := by
  have hle :=
    le_trans hsteps (phaseRuntimeUnit_le_budget pad log bits)
  exact MachineRunLemmas.haltsWithin_mono
    parserMachine (phaseConfig 4 pad bits log) hle hhalt

theorem parser_compose_same_scale_exact_to_budget
    (parentPad childPad : Nat)
    (parentLog childLog : SlotLog)
    (parentBits childBits : BitString)
    (prefixSteps : Nat)
    (hlt : childBits.length < parentBits.length)
    (hscale :
      phaseRuntimeScale childPad childLog childBits =
        phaseRuntimeScale parentPad parentLog parentBits)
    (hprefixBound :
      prefixSteps ≤ phaseRuntimeUnit parentPad parentLog parentBits)
    (hprefix :
      parserMachine.run prefixSteps
          (phaseConfig 4 parentPad parentBits parentLog) =
        phaseConfig 4 childPad childBits childLog)
    (hchild :
      parserMachine.HaltsWithin
        (phaseRuntimeBudget childPad childLog childBits)
        (phaseConfig 4 childPad childBits childLog)) :
    parserMachine.HaltsWithin
      (phaseRuntimeBudget parentPad parentLog parentBits)
      (phaseConfig 4 parentPad parentBits parentLog) := by
  have hsmall :=
    parser_halts_after_exact_prefix
      (phaseConfig 4 parentPad parentBits parentLog)
      (phaseConfig 4 childPad childBits childLog)
      prefixSteps
      (phaseRuntimeBudget childPad childLog childBits)
      hprefix hchild
  have hbudget :
      prefixSteps + phaseRuntimeBudget childPad childLog childBits ≤
        phaseRuntimeBudget parentPad parentLog parentBits := by
    unfold phaseRuntimeBudget phaseRuntimeUnit
    rw [hscale]
    exact budget_compose_same_scale
      (phaseRuntimeScale parentPad parentLog parentBits)
      parentBits.length childBits.length prefixSteps
      hlt (by simpa [phaseRuntimeUnit] using hprefixBound)
  exact MachineRunLemmas.haltsWithin_mono
    parserMachine (phaseConfig 4 parentPad parentBits parentLog)
    hbudget hsmall

theorem parser_compose_same_scale_rightBlank_to_budget
    (parentPad childPad : Nat)
    (parentLog childLog : SlotLog)
    (parentBits childBits : BitString)
    (prefixSteps : Nat)
    (hlt : childBits.length < parentBits.length)
    (hscale :
      phaseRuntimeScale childPad childLog childBits =
        phaseRuntimeScale parentPad parentLog parentBits)
    (hprefixBound :
      prefixSteps ≤ phaseRuntimeUnit parentPad parentLog parentBits)
    (hprefix :
      ConfigRightBlankEq
        (parserMachine.run prefixSteps
          (phaseConfig 4 parentPad parentBits parentLog))
        (phaseConfig 4 childPad childBits childLog))
    (hchild :
      parserMachine.HaltsWithin
        (phaseRuntimeBudget childPad childLog childBits)
        (phaseConfig 4 childPad childBits childLog)) :
    parserMachine.HaltsWithin
      (phaseRuntimeBudget parentPad parentLog parentBits)
      (phaseConfig 4 parentPad parentBits parentLog) := by
  have hsmall :=
    parser_halts_after_rightBlank_prefix
      (phaseConfig 4 parentPad parentBits parentLog)
      (phaseConfig 4 childPad childBits childLog)
      prefixSteps
      (phaseRuntimeBudget childPad childLog childBits)
      hprefix hchild
  have hbudget :
      prefixSteps + phaseRuntimeBudget childPad childLog childBits ≤
        phaseRuntimeBudget parentPad parentLog parentBits := by
    unfold phaseRuntimeBudget phaseRuntimeUnit
    rw [hscale]
    exact budget_compose_same_scale
      (phaseRuntimeScale parentPad parentLog parentBits)
      parentBits.length childBits.length prefixSteps
      hlt (by simpa [phaseRuntimeUnit] using hprefixBound)
  exact MachineRunLemmas.haltsWithin_mono
    parserMachine (phaseConfig 4 parentPad parentBits parentLog)
    hbudget hsmall

theorem parser_compose_scale_succ_exact_to_budget
    (parentPad childPad : Nat)
    (parentLog childLog : SlotLog)
    (parentBits childBits : BitString)
    (prefixSteps : Nat)
    (hscale :
      phaseRuntimeScale childPad childLog childBits =
        phaseRuntimeScale parentPad parentLog parentBits + 1)
    (hchildScale :
      childBits.length + 1 ≤
        phaseRuntimeScale parentPad parentLog parentBits)
    (hconsume :
      childBits.length + 3 ≤ parentBits.length)
    (hprefixBound :
      prefixSteps ≤ phaseRuntimeUnit parentPad parentLog parentBits)
    (hprefix :
      parserMachine.run prefixSteps
          (phaseConfig 4 parentPad parentBits parentLog) =
        phaseConfig 4 childPad childBits childLog)
    (hchild :
      parserMachine.HaltsWithin
        (phaseRuntimeBudget childPad childLog childBits)
        (phaseConfig 4 childPad childBits childLog)) :
    parserMachine.HaltsWithin
      (phaseRuntimeBudget parentPad parentLog parentBits)
      (phaseConfig 4 parentPad parentBits parentLog) := by
  have hsmall :=
    parser_halts_after_exact_prefix
      (phaseConfig 4 parentPad parentBits parentLog)
      (phaseConfig 4 childPad childBits childLog)
      prefixSteps
      (phaseRuntimeBudget childPad childLog childBits)
      hprefix hchild
  have hbudget :
      prefixSteps + phaseRuntimeBudget childPad childLog childBits ≤
        phaseRuntimeBudget parentPad parentLog parentBits := by
    unfold phaseRuntimeBudget phaseRuntimeUnit
    rw [hscale]
    exact budget_compose_scale_succ
      (phaseRuntimeScale parentPad parentLog parentBits)
      parentBits.length childBits.length prefixSteps
      hchildScale hconsume
      (by simpa [phaseRuntimeUnit] using hprefixBound)
  exact MachineRunLemmas.haltsWithin_mono
    parserMachine (phaseConfig 4 parentPad parentBits parentLog)
    hbudget hsmall

#print axioms MCore.Real.P01GlobalParserBound.budget_compose_same_scale
#print axioms MCore.Real.P01GlobalParserBound.budget_compose_scale_succ

end P01GlobalParserBound
end Real
end MCore
