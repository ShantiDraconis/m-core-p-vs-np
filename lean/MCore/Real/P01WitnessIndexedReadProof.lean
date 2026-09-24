import MCore.Real.P01WitnessIndexedReadMachine

namespace MCore
namespace Real
namespace P01WitnessIndexedReadProof

open CanonicalFinalProof
open P01WitnessIndexedReadMachine

/-- State-3 configuration while crossing blank padding toward the selected
witness cell. `pad` counts additional blanks to the left of the current blank. -/
def witnessSeekConfig
    (pad : Nat) (b : Bool) (tail : BitString)
    (right : List (Option Bool)) :
    Configuration (Fin 6) (Option Bool) :=
  { state := 3
    tape :=
      { left := List.replicate pad none ++ some b :: tail.map some
        head := none
        right := right } }

@[simp] theorem witnessSeekConfig_state
    (pad : Nat) (b : Bool) (tail : BitString)
    (right : List (Option Bool)) :
    (witnessSeekConfig pad b tail right).state = (3 : Fin 6) := rfl

@[simp] theorem witnessIndexedReadMachine_not_halt3 :
    witnessIndexedReadMachine.halting (3 : Fin 6) = false := by decide

/-- One blank-crossing step decreases the physical padding by one. -/
theorem witnessSeek_step_succ
    (pad : Nat) (b : Bool) (tail : BitString)
    (right : List (Option Bool)) :
    witnessIndexedReadMachine.step
        (witnessSeekConfig (pad + 1) b tail right) =
      witnessSeekConfig pad b tail (none :: right) := by
  simp [witnessSeekConfig, witnessIndexedReadMachine, TM.step,
    Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

/-- With no additional padding, one step reaches the selected witness cell. -/
theorem witnessSeek_step_zero
    (b : Bool) (tail : BitString)
    (right : List (Option Bool)) :
    witnessIndexedReadMachine.step
        (witnessSeekConfig 0 b tail right) =
      { state := (3 : Fin 6),
        tape :=
          { left := tail.map some
            head := some b
            right := none :: right } } := by
  simp [witnessSeekConfig, witnessIndexedReadMachine, TM.step,
    Tape.write, Tape.move]

/-- The following state-3 step classifies the selected Boolean and halts. -/
theorem witnessSeek_classify
    (b : Bool) (tail : BitString)
    (right : List (Option Bool)) :
    (witnessIndexedReadMachine.step
      { state := (3 : Fin 6),
        tape :=
          { left := tail.map some
            head := some b
            right := right } }).state =
      (if b then (4 : Fin 6) else (5 : Fin 6)) := by
  cases b <;>
    simp [witnessIndexedReadMachine, TM.step, Tape.write, Tape.move]

/-- Exact physical macro: crossing arbitrary blank padding returns the selected
witness bit in the finite halting state 4=true / 5=false. -/
theorem witnessSeek_run_state
    (pad : Nat) (b : Bool) (tail : BitString)
    (right : List (Option Bool)) :
    (witnessIndexedReadMachine.run (pad + 2)
      (witnessSeekConfig pad b tail right)).state =
      (if b then (4 : Fin 6) else (5 : Fin 6)) := by
  induction pad generalizing right with
  | zero =>
      rw [show 0 + 2 = 1 + 1 by omega]
      simp only [TM.run.eq_def, witnessSeekConfig_state,
        witnessIndexedReadMachine_not_halt3, Bool.false_eq_true, if_false]
      rw [witnessSeek_step_zero]
      simp only [TM.run.eq_def, witnessIndexedReadMachine_not_halt3,
        Bool.false_eq_true, if_false]
      exact witnessSeek_classify b tail (none :: right)
  | succ pad ih =>
      rw [show Nat.succ pad + 2 = 1 + (pad + 2) by omega]
      simp only [TM.run.eq_def, witnessSeekConfig_state,
        witnessIndexedReadMachine_not_halt3, Bool.false_eq_true, if_false]
      have hs :
          witnessIndexedReadMachine.step
              (witnessSeekConfig (Nat.succ pad) b tail right) =
            witnessSeekConfig pad b tail (none :: right) := by
        simpa [Nat.succ_eq_add_one] using
          witnessSeek_step_succ pad b tail right
      rw [hs]
      exact ih (none :: right)

theorem witnessSeek_run_halts
    (pad : Nat) (b : Bool) (tail : BitString)
    (right : List (Option Bool)) :
    witnessIndexedReadMachine.HaltsWithin (pad + 2)
      (witnessSeekConfig pad b tail right) := by
  unfold TM.HaltsWithin
  rw [witnessSeek_run_state]
  cases b <;> simp [witnessIndexedReadMachine]

#print axioms MCore.Real.P01WitnessIndexedReadProof.witnessSeek_run_state
#print axioms MCore.Real.P01WitnessIndexedReadProof.witnessSeek_run_halts

end P01WitnessIndexedReadProof
end Real
end MCore
