import MCore.Real.P01InputNodeCompositeNTM
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01InputNodeCompositeRun

open P01NTMRunLaws
open P01InputReturnMode
open P01InputIndexLookahead
open P01WitnessIndexedReadPreserving
open P01InputAfterReadReturn
open P01InputNodeCompositeNTM

abbrev CompositeConfig :=
  Configuration InputNodeCompositeState (Option Bool)

def lookConfig
    (c : Configuration InputIndexLookaheadState (Option Bool)) :
    CompositeConfig :=
  { state := .look c.state, tape := c.tape }

def readConfig
    (mode : InputReturnMode)
    (c : Configuration PreservingReadState (Option Bool)) :
    CompositeConfig :=
  { state := .read mode c.state, tape := c.tape }

def returnConfig
    (mode : InputReturnMode) (selected : Bool)
    (c : Configuration InputAfterReadReturnState (Option Bool)) :
    CompositeConfig :=
  { state := .ret mode selected c.state, tape := c.tape }

@[simp] theorem lookConfig_not_halted
    (c : Configuration InputIndexLookaheadState (Option Bool)) :
    ¬ Halted inputNodeCompositeMachine (lookConfig c) := by
  simp [Halted, lookConfig, inputNodeCompositeMachine]

@[simp] theorem readConfig_not_halted
    (mode : InputReturnMode)
    (c : Configuration PreservingReadState (Option Bool)) :
    ¬ Halted inputNodeCompositeMachine (readConfig mode c) := by
  simp [Halted, readConfig, inputNodeCompositeMachine]

@[simp] theorem returnConfig_not_halted
    (mode : InputReturnMode) (selected : Bool)
    (c : Configuration InputAfterReadReturnState (Option Bool)) :
    ¬ Halted inputNodeCompositeMachine (returnConfig mode selected c) := by
  simp [Halted, returnConfig, inputNodeCompositeMachine]

theorem look_successors_active
    (c : Configuration InputIndexLookaheadState (Option Bool))
    (h : inputIndexLookaheadMachine.halting c.state = false) :
    inputNodeCompositeMachine.successors (lookConfig c) =
      [lookConfig (inputIndexLookaheadMachine.step c)] := by
  unfold NTM.successors
  simp only [lookConfig]
  rw [look_transition_active c.state c.tape.head h]
  simp [lookConfig, NTM.stepBranch, TM.step,
    inputNodeCompositeMachine, inputIndexLookaheadMachine,
    Tape.write, Tape.move]

theorem read_successors_active
    (mode : InputReturnMode)
    (c : Configuration PreservingReadState (Option Bool))
    (h : preservingReadMachine.halting c.state = false) :
    inputNodeCompositeMachine.successors (readConfig mode c) =
      [readConfig mode (preservingReadMachine.step c)] := by
  unfold NTM.successors
  simp only [readConfig]
  rw [read_transition_active mode c.state c.tape.head h]
  simp [readConfig, NTM.stepBranch, TM.step,
    inputNodeCompositeMachine, preservingReadMachine,
    Tape.write, Tape.move]

theorem return_successors_active
    (mode : InputReturnMode) (selected : Bool)
    (c : Configuration InputAfterReadReturnState (Option Bool))
    (h : inputAfterReadReturnMachine.halting c.state = false) :
    inputNodeCompositeMachine.successors (returnConfig mode selected c) =
      [returnConfig mode selected (inputAfterReadReturnMachine.step c)] := by
  unfold NTM.successors
  simp only [returnConfig]
  rw [return_transition_active mode selected c.state c.tape.head h]
  simp [returnConfig, NTM.stepBranch, TM.step,
    inputNodeCompositeMachine, inputAfterReadReturnMachine,
    Tape.write, Tape.move]

/-- The lookahead phase's deterministic configuration after fuel `n` is
reachable in the composite in at most `n` steps.  If the source TM halts
early, the witness uses that earlier time instead of requiring minimal fuel. -/
theorem look_run_reachable :
    ∀ (n : Nat)
      (c : Configuration InputIndexLookaheadState (Option Bool)),
      ∃ m ≤ n,
        lookConfig (inputIndexLookaheadMachine.run n c) ∈
          inputNodeCompositeMachine.runBranches m [lookConfig c] := by
  intro n
  induction n with
  | zero =>
      intro c
      refine ⟨0, by omega, ?_⟩
      change lookConfig c ∈ [lookConfig c]
      simp
  | succ n ih =>
      intro c
      cases hhalt : inputIndexLookaheadMachine.halting c.state with
      | true =>
          have hr :=
            MachineRunLemmas.run_halted
              inputIndexLookaheadMachine c hhalt (n + 1)
          refine ⟨0, by omega, ?_⟩
          change
            lookConfig (inputIndexLookaheadMachine.run (n + 1) c) ∈
              [lookConfig c]
          rw [hr]
          simp
      | false =>
          obtain ⟨m, hm, hmem⟩ :=
            ih (inputIndexLookaheadMachine.step c)
          have hsucc :
              lookConfig (inputIndexLookaheadMachine.step c) ∈
                inputNodeCompositeMachine.successors (lookConfig c) := by
            rw [look_successors_active c hhalt]
            simp
          have hone :
              lookConfig (inputIndexLookaheadMachine.step c) ∈
                inputNodeCompositeMachine.runBranches 1 [lookConfig c] := by
            have := mem_runBranches_succ_of_successor
              inputNodeCompositeMachine 0 [lookConfig c]
              (lookConfig c)
              (lookConfig (inputIndexLookaheadMachine.step c))
              (by simp [NTM.runBranches])
              (lookConfig_not_halted c) hsucc
            simpa using this
          have htrans :=
            mem_runBranches_trans inputNodeCompositeMachine
              1 m [lookConfig c]
              (lookConfig (inputIndexLookaheadMachine.step c))
              (lookConfig
                (inputIndexLookaheadMachine.run n
                  (inputIndexLookaheadMachine.step c)))
              hone hmem
          refine ⟨1 + m, by omega, ?_⟩
          simpa [TM.run, hhalt] using htrans

theorem read_run_reachable
    (mode : InputReturnMode) :
    ∀ (n : Nat)
      (c : Configuration PreservingReadState (Option Bool)),
      ∃ m ≤ n,
        readConfig mode (preservingReadMachine.run n c) ∈
          inputNodeCompositeMachine.runBranches m [readConfig mode c] := by
  intro n
  induction n with
  | zero =>
      intro c
      refine ⟨0, by omega, ?_⟩
      change readConfig mode c ∈ [readConfig mode c]
      simp
  | succ n ih =>
      intro c
      cases hhalt : preservingReadMachine.halting c.state with
      | true =>
          have hr :=
            MachineRunLemmas.run_halted
              preservingReadMachine c hhalt (n + 1)
          refine ⟨0, by omega, ?_⟩
          change
            readConfig mode (preservingReadMachine.run (n + 1) c) ∈
              [readConfig mode c]
          rw [hr]
          simp
      | false =>
          obtain ⟨m, hm, hmem⟩ := ih (preservingReadMachine.step c)
          have hsucc :
              readConfig mode (preservingReadMachine.step c) ∈
                inputNodeCompositeMachine.successors (readConfig mode c) := by
            rw [read_successors_active mode c hhalt]
            simp
          have hone :
              readConfig mode (preservingReadMachine.step c) ∈
                inputNodeCompositeMachine.runBranches 1 [readConfig mode c] := by
            have := mem_runBranches_succ_of_successor
              inputNodeCompositeMachine 0 [readConfig mode c]
              (readConfig mode c)
              (readConfig mode (preservingReadMachine.step c))
              (by simp [NTM.runBranches])
              (readConfig_not_halted mode c) hsucc
            simpa using this
          have htrans :=
            mem_runBranches_trans inputNodeCompositeMachine
              1 m [readConfig mode c]
              (readConfig mode (preservingReadMachine.step c))
              (readConfig mode
                (preservingReadMachine.run n
                  (preservingReadMachine.step c)))
              hone hmem
          refine ⟨1 + m, by omega, ?_⟩
          simpa [TM.run, hhalt] using htrans

theorem return_run_reachable
    (mode : InputReturnMode) (selected : Bool) :
    ∀ (n : Nat)
      (c : Configuration InputAfterReadReturnState (Option Bool)),
      ∃ m ≤ n,
        returnConfig mode selected (inputAfterReadReturnMachine.run n c) ∈
          inputNodeCompositeMachine.runBranches m
            [returnConfig mode selected c] := by
  intro n
  induction n with
  | zero =>
      intro c
      refine ⟨0, by omega, ?_⟩
      change returnConfig mode selected c ∈ [returnConfig mode selected c]
      simp
  | succ n ih =>
      intro c
      cases hhalt : inputAfterReadReturnMachine.halting c.state with
      | true =>
          have hr :=
            MachineRunLemmas.run_halted
              inputAfterReadReturnMachine c hhalt (n + 1)
          refine ⟨0, by omega, ?_⟩
          change
            returnConfig mode selected
                (inputAfterReadReturnMachine.run (n + 1) c) ∈
              [returnConfig mode selected c]
          rw [hr]
          simp
      | false =>
          obtain ⟨m, hm, hmem⟩ :=
            ih (inputAfterReadReturnMachine.step c)
          have hsucc :
              returnConfig mode selected
                  (inputAfterReadReturnMachine.step c) ∈
                inputNodeCompositeMachine.successors
                  (returnConfig mode selected c) := by
            rw [return_successors_active mode selected c hhalt]
            simp
          have hone :
              returnConfig mode selected
                  (inputAfterReadReturnMachine.step c) ∈
                inputNodeCompositeMachine.runBranches 1
                  [returnConfig mode selected c] := by
            have := mem_runBranches_succ_of_successor
              inputNodeCompositeMachine 0 [returnConfig mode selected c]
              (returnConfig mode selected c)
              (returnConfig mode selected
                (inputAfterReadReturnMachine.step c))
              (by simp [NTM.runBranches])
              (returnConfig_not_halted mode selected c) hsucc
            simpa using this
          have htrans :=
            mem_runBranches_trans inputNodeCompositeMachine
              1 m [returnConfig mode selected c]
              (returnConfig mode selected
                (inputAfterReadReturnMachine.step c))
              (returnConfig mode selected
                (inputAfterReadReturnMachine.run n
                  (inputAfterReadReturnMachine.step c)))
              hone hmem
          refine ⟨1 + m, by omega, ?_⟩
          simpa [TM.run, hhalt] using htrans

#print axioms MCore.Real.P01InputNodeCompositeRun.look_successors_active
#print axioms MCore.Real.P01InputNodeCompositeRun.read_successors_active
#print axioms MCore.Real.P01InputNodeCompositeRun.return_successors_active
#print axioms MCore.Real.P01InputNodeCompositeRun.look_run_reachable
#print axioms MCore.Real.P01InputNodeCompositeRun.read_run_reachable
#print axioms MCore.Real.P01InputNodeCompositeRun.return_run_reachable

end P01InputNodeCompositeRun
end Real
end MCore
