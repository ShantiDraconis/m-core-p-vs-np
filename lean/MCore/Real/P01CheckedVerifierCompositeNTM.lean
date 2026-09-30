import MCore.Real.P01CheckedEvalRunBaseCases
import MCore.Real.P01FullVerifierTraversal
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01CheckedVerifierCompositeNTM

open CanonicalFinalProof
open P01WitnessPreservingPrep
open P01FullVerifierTraversal
open P01EvalCursorMachine
open P01CheckedEvalRunLoopNTM
open P01NTMRunLaws

/-- Prepared-tape verifier wrapper for the checked evaluator.

This wrapper performs the same certified source-end scan as the existing
verifier core, then enters the CNF-aware checked evaluator.  The checked loop
itself now contains the mandatory source-empty guard before any final state. -/
inductive CheckedVerifierState where
  | start
  | scan : Fin 2 → CheckedVerifierState
  | enter
  | eval : CheckedEvalRunState → CheckedVerifierState
  | reject
  deriving DecidableEq, Repr

abbrev CheckedVerifierConfig :=
  Configuration CheckedVerifierState (Option Bool)

def scanEmbed
    (c : Configuration (Fin 2) (Option Bool)) :
    CheckedVerifierConfig :=
  { state := .scan c.state, tape := c.tape }

def checkedEvalEmbed : CheckedEvalRunState → CheckedVerifierState
  | .final v => .eval (.final v)
  | .reject => .reject
  | q => .eval q

def checkedVerifierMachine :
    NTM CheckedVerifierState (Option Bool) where
  initial := .start
  blank := none
  transition := fun q symbol =>
    match q with
    | .start =>
        match symbol with
        | none => [(.reject, none, .stay)]
        | some b =>
            let t := sourceEndScanner.transition sourceEndScanner.initial (some b)
            [(.scan t.1, t.2.1, t.2.2)]
    | .scan qs =>
        if sourceEndScanner.halting qs then
          [(.enter, symbol, .stay)]
        else
          let t := sourceEndScanner.transition qs symbol
          [(.scan t.1, t.2.1, t.2.2)]
    | .enter =>
        [(.eval checkedEvalRunLoopMachine.initial, symbol, .right)]
    | .eval qe =>
        match qe with
        | .reject => [(.reject, symbol, .stay)]
        | _ =>
            (checkedEvalRunLoopMachine.transition qe symbol).map
              (fun t => (checkedEvalEmbed t.1, t.2.1, t.2.2))
    | .reject => []
  accepting := fun q =>
    match q with
    | .eval qe => checkedEvalRunLoopMachine.accepting qe
    | _ => false
  rejecting := fun q =>
    match q with
    | .eval qe => checkedEvalRunLoopMachine.rejecting qe
    | .reject => true
    | _ => false

@[simp] theorem checkedVerifierMachine_blank :
    checkedVerifierMachine.blank = none := rfl

@[simp] theorem checkedVerifierMachine_initial :
    checkedVerifierMachine.initial = .start := rfl

@[simp] theorem start_not_halted
    (tape : Tape (Option Bool)) :
    ¬ Halted checkedVerifierMachine
      ({ state := .start, tape := tape } : CheckedVerifierConfig) := by
  simp [Halted, checkedVerifierMachine]

@[simp] theorem scanEmbed_not_halted
    (c : Configuration (Fin 2) (Option Bool)) :
    ¬ Halted checkedVerifierMachine (scanEmbed c) := by
  simp [Halted, scanEmbed, checkedVerifierMachine]

@[simp] theorem enter_not_halted
    (tape : Tape (Option Bool)) :
    ¬ Halted checkedVerifierMachine
      ({ state := .enter, tape := tape } : CheckedVerifierConfig) := by
  simp [Halted, checkedVerifierMachine]

theorem scan_successors_active
    (c : Configuration (Fin 2) (Option Bool))
    (h : sourceEndScanner.halting c.state = false) :
    checkedVerifierMachine.successors (scanEmbed c) =
      [scanEmbed (sourceEndScanner.step c)] := by
  unfold NTM.successors
  simp [scanEmbed, checkedVerifierMachine, h,
    NTM.stepBranch, TM.step, Tape.write, Tape.move]

private theorem one_step_of_successor
    (a b : CheckedVerifierConfig)
    (ha : ¬ Halted checkedVerifierMachine a)
    (hs : b ∈ checkedVerifierMachine.successors a) :
    b ∈ checkedVerifierMachine.runBranches 1 [a] := by
  have h :=
    mem_runBranches_succ_of_successor
      checkedVerifierMachine 0 [a] a b
      (by simp [NTM.runBranches]) ha hs
  simpa using h

private theorem tm_scan_run_reachable :
    ∀ (n : Nat) (c : Configuration (Fin 2) (Option Bool)),
      ∃ m ≤ n,
        scanEmbed (sourceEndScanner.run n c) ∈
          checkedVerifierMachine.runBranches m [scanEmbed c] := by
  intro n
  induction n with
  | zero =>
      intro c
      refine ⟨0, by omega, ?_⟩
      simp [NTM.runBranches]
  | succ n ih =>
      intro c
      cases hhalt : sourceEndScanner.halting c.state with
      | true =>
          have hr := MachineRunLemmas.run_halted sourceEndScanner c hhalt (n + 1)
          refine ⟨0, by omega, ?_⟩
          rw [hr]
          simp [NTM.runBranches]
      | false =>
          obtain ⟨m, hm, hmem⟩ := ih (sourceEndScanner.step c)
          have hsucc :
              scanEmbed (sourceEndScanner.step c) ∈
                checkedVerifierMachine.successors (scanEmbed c) := by
            rw [scan_successors_active c hhalt]
            simp
          have hone :
              scanEmbed (sourceEndScanner.step c) ∈
                checkedVerifierMachine.runBranches 1 [scanEmbed c] :=
            one_step_of_successor
              (scanEmbed c) (scanEmbed (sourceEndScanner.step c))
              (scanEmbed_not_halted c) hsucc
          have htrans :=
            mem_runBranches_trans checkedVerifierMachine
              1 m [scanEmbed c]
              (scanEmbed (sourceEndScanner.step c))
              (scanEmbed (sourceEndScanner.run n (sourceEndScanner.step c)))
              hone hmem
          refine ⟨1 + m, by omega, ?_⟩
          simpa [TM.run, hhalt] using htrans

/-- The checked evaluator embeds terminal-soundly into the verifier wrapper. -/
def checkedEvalSimulation :
    P01NTMRunLaws.Simulation
      checkedEvalRunLoopMachine checkedVerifierMachine checkedEvalEmbed where
  accepting := by
    intro q
    cases q <;> rfl
  rejecting := by
    intro q
    cases q <;> rfl
  successors := by
    intro c hactive
    rcases c with ⟨q, tape⟩
    cases q <;>
      simp [Halted, checkedEvalEmbed, checkedVerifierMachine,
        checkedEvalRunLoopMachine, P01NTMRunLaws.liftConfig,
        NTM.successors, NTM.stepBranch, List.map_map, Function.comp_def,
        Tape.write, Tape.move] at hactive ⊢

theorem checked_eval_runBranches_map
    (n : Nat)
    (xs : List (Configuration CheckedEvalRunState (Option Bool))) :
    checkedVerifierMachine.runBranches n
      (xs.map (P01NTMRunLaws.liftConfig checkedEvalEmbed)) =
    (checkedEvalRunLoopMachine.runBranches n xs).map
      (P01NTMRunLaws.liftConfig checkedEvalEmbed) :=
  P01NTMRunLaws.runBranches_map
    checkedEvalRunLoopMachine checkedVerifierMachine
      checkedEvalEmbed checkedEvalSimulation n xs

#print axioms MCore.Real.P01CheckedVerifierCompositeNTM.scan_successors_active
#print axioms MCore.Real.P01CheckedVerifierCompositeNTM.checkedEvalSimulation
#print axioms MCore.Real.P01CheckedVerifierCompositeNTM.checked_eval_runBranches_map

end P01CheckedVerifierCompositeNTM
end Real
end MCore
