import MCore.Real.P01InputIndexLookahead
import MCore.Real.P01CheckedEvalRunInputTag
import MCore.Real.P01RawDeadEnd

namespace MCore
namespace Real
namespace P01RawMalformedUnary

open CanonicalFinalProof
open P01EvalCursorMachine
open P01WitnessIndexedReadPreserving
open P01InputReturnMode
open P01InputIndexLookahead
open P01InputNodeCompositeNTM
open P01InputNodeCompositeRun
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunInputTag
open P01NTMRunLaws
open MachineRunLemmas

/-- A 000 payload made only of unary true markers and followed by the physical
source separator has no terminating false marker. The real finite-control
lookahead therefore reaches its reject state after exactly k+1 steps. -/
theorem lookahead_truncated_unary_reject
    (witness frameStack : BitString)
    (consumed padding k : Nat) :
    (inputIndexLookaheadMachine.run (k + 1)
      { state := inputIndexLookaheadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (List.replicate k true) frameStack padding }).state =
      .reject := by
  let base : List (Option Bool) :=
    List.replicate consumed none ++ none :: witness.map some
  let suffix : List (Option Bool) :=
    none :: frameStack.reverse.map some ++
      none :: List.replicate padding none
  have hview :
      evalCursorReadTape witness consumed
          (List.replicate k true) frameStack padding =
        rightStreamTape base
          (List.replicate k (some true) ++ suffix) := by
    cases k with
    | zero =>
        simp [base, suffix, evalCursorReadTape, rightStreamTape,
          List.append_assoc]
    | succ k =>
        simp [base, suffix, evalCursorReadTape, rightStreamTape,
          List.map_replicate, List.replicate_succ,
          List.append_assoc]
  rw [hview]
  rw [run_add inputIndexLookaheadMachine k 1]
  rw [scanIndex_over_true k base suffix]
  simp [suffix, rightStreamTape, inputIndexLookaheadMachine,
    TM.run, TM.step, Tape.write, Tape.move]

/-- The same malformed unary payload reaches the dead lookahead-reject state
inside the actual input-node composite machine. -/
theorem inputComposite_truncated_unary_reaches_dead
    (witness frameStack : BitString)
    (consumed padding k : Nat) :
    ∃ m ≤ k + 1, ∃ tape,
      ({ state := .look .reject, tape := tape } :
        Configuration InputNodeCompositeState (Option Bool)) ∈
      inputNodeCompositeMachine.runBranches m
        [{ state := inputNodeCompositeMachine.initial,
           tape :=
             evalCursorReadTape witness consumed
               (List.replicate k true) frameStack padding }] := by
  let c0 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := inputIndexLookaheadMachine.initial,
      tape :=
        evalCursorReadTape witness consumed
          (List.replicate k true) frameStack padding }
  obtain ⟨m, hm, hmem⟩ :=
    look_run_reachable (k + 1) c0
  have hstate :
      (inputIndexLookaheadMachine.run (k + 1) c0).state = .reject := by
    simpa [c0] using
      lookahead_truncated_unary_reject
        witness frameStack consumed padding k
  let tape :=
    (inputIndexLookaheadMachine.run (k + 1) c0).tape
  have heq :
      inputIndexLookaheadMachine.run (k + 1) c0 =
        ({ state := .reject, tape := tape } :
          Configuration InputIndexLookaheadState (Option Bool)) := by
    apply Configuration.ext
    · exact hstate
    · rfl
  rw [heq] at hmem
  refine ⟨m, hm, tape, ?_⟩
  simpa [lookConfig] using hmem

/-- The malformed composite target is active but has no successors. This is a
fail-closed dead state rather than a labelled accepting/rejecting terminal. -/
theorem inputComposite_look_reject_is_dead
    (tape : Tape (Option Bool)) :
    ¬ Halted inputNodeCompositeMachine
        ({ state := .look .reject, tape := tape } :
          Configuration InputNodeCompositeState (Option Bool)) ∧
      inputNodeCompositeMachine.successors
        ({ state := .look .reject, tape := tape } :
          Configuration InputNodeCompositeState (Option Bool)) = [] := by
  constructor
  · simp [Halted, inputNodeCompositeMachine]
  · simp [inputNodeCompositeMachine, NTM.successors]

#print axioms MCore.Real.P01RawMalformedUnary.lookahead_truncated_unary_reject
#print axioms MCore.Real.P01RawMalformedUnary.inputComposite_truncated_unary_reaches_dead
#print axioms MCore.Real.P01RawMalformedUnary.inputComposite_look_reject_is_dead

end P01RawMalformedUnary
end Real
end MCore
