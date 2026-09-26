import MCore.Real.P01PhysicalEmbeddedRun
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01PhysicalEmbeddedRunMulti

open P01PhysicalDispatcher
open P01PhysicalEmbeddedRun
open P01FullVerifierStackPrimitiveMachine
open P01WitnessIndexedReadMachine
open P01FullVerifierSourceRewind

/-- Exact multi-step embedding while the local machine stays non-halting
through every strict prefix of the run. -/
def StackPrefixNonHalting
    (fuel : Nat)
    (c : Configuration (Fin 8) (Option Bool)) : Prop :=
  ∀ k, k < fuel →
    stackPrimitiveMachine.halting
      (stackPrimitiveMachine.run k c).state = false

def WitnessPrefixNonHalting
    (fuel : Nat)
    (c : Configuration (Fin 6) (Option Bool)) : Prop :=
  ∀ k, k < fuel →
    witnessIndexedReadMachine.halting
      (witnessIndexedReadMachine.run k c).state = false

def RewindPrefixNonHalting
    (fuel : Nat)
    (c : Configuration (Fin 3) (Option Bool)) : Prop :=
  ∀ k, k < fuel →
    sourceRewindMachine.halting
      (sourceRewindMachine.run k c).state = false

theorem dispatcher_run_stack_of_prefix_nonhalting
    (fuel : Nat)
    (c : Configuration (Fin 8) (Option Bool))
    (hprefix : StackPrefixNonHalting fuel c) :
    physicalDispatcherMachine.run fuel (embedStackConfig c) =
      embedStackConfig (stackPrimitiveMachine.run fuel c) := by
  induction fuel generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      have h0 : stackPrimitiveMachine.halting c.state = false := by
        simpa [StackPrefixNonHalting, TM.run] using hprefix 0 (Nat.succ_pos n)
      rw [TM.run, TM.run]
      simp [physicalDispatcherMachine, embedStackConfig, h0, dispatcher_step_stack]
      apply ih
      intro k hk
      have hs : k + 1 < n + 1 := by omega
      have h := hprefix (k + 1) hs
      simpa [MachineRunLemmas.run_add, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using h

theorem dispatcher_run_witness_of_prefix_nonhalting
    (fuel : Nat)
    (c : Configuration (Fin 6) (Option Bool))
    (hprefix : WitnessPrefixNonHalting fuel c) :
    physicalDispatcherMachine.run fuel (embedWitnessConfig c) =
      embedWitnessConfig (witnessIndexedReadMachine.run fuel c) := by
  induction fuel generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      have h0 : witnessIndexedReadMachine.halting c.state = false := by
        simpa [WitnessPrefixNonHalting, TM.run] using hprefix 0 (Nat.succ_pos n)
      rw [TM.run, TM.run]
      simp [physicalDispatcherMachine, embedWitnessConfig, h0,
        dispatcher_step_witness]
      apply ih
      intro k hk
      have hs : k + 1 < n + 1 := by omega
      have h := hprefix (k + 1) hs
      simpa [MachineRunLemmas.run_add, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using h

theorem dispatcher_run_rewind_of_prefix_nonhalting
    (fuel : Nat)
    (c : Configuration (Fin 3) (Option Bool))
    (hprefix : RewindPrefixNonHalting fuel c) :
    physicalDispatcherMachine.run fuel (embedRewindConfig c) =
      embedRewindConfig (sourceRewindMachine.run fuel c) := by
  induction fuel generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      have h0 : sourceRewindMachine.halting c.state = false := by
        simpa [RewindPrefixNonHalting, TM.run] using hprefix 0 (Nat.succ_pos n)
      rw [TM.run, TM.run]
      simp [physicalDispatcherMachine, embedRewindConfig, h0,
        dispatcher_step_rewind]
      apply ih
      intro k hk
      have hs : k + 1 < n + 1 := by omega
      have h := hprefix (k + 1) hs
      simpa [MachineRunLemmas.run_add, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using h

#print axioms MCore.Real.P01PhysicalEmbeddedRunMulti.dispatcher_run_stack_of_prefix_nonhalting
#print axioms MCore.Real.P01PhysicalEmbeddedRunMulti.dispatcher_run_witness_of_prefix_nonhalting
#print axioms MCore.Real.P01PhysicalEmbeddedRunMulti.dispatcher_run_rewind_of_prefix_nonhalting

end P01PhysicalEmbeddedRunMulti
end Real
end MCore
