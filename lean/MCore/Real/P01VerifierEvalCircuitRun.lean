import MCore.Real.P01VerifierEvalCompositeNTM
import MCore.Real.P01EvalRunCircuitCertificate
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01VerifierEvalCircuitRun

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01NTMRunLaws
open P01EvalCursorMachine
open P01EvalRunLoopNTM
open P01EvalRunCircuitCertificate
open P01VerifierEvalCompositeNTM

abbrev VerifierConfig :=
  Configuration VerifierEvalState (Option Bool)

/-- Canonical witness bits agree pointwise with the semantic finite witness
below the circuit variable bound. -/
theorem witnessBits_getD_eq_assignment
    (phi : Circuit)
    (w : SATWitness phi)
    (i : Nat)
    (hi : i < varBound phi) :
    (witnessBits w).getD i false =
      assignmentOfWitness phi w i := by
  simp [witnessBits, assignmentOfWitness, hi]

/-- Membership transport from the global eval loop into the verifier wrapper. -/
theorem eval_mem_lift
    (n : Nat)
    (a b : Configuration EvalRunLoopState (Option Bool))
    (h : b ∈ evalRunLoopMachine.runBranches n [a]) :
    P01NTMRunLaws.liftConfig evalStateEmbed b ∈
      verifierEvalMachine.runBranches n
        [P01NTMRunLaws.liftConfig evalStateEmbed a] := by
  rw [show
      [P01NTMRunLaws.liftConfig evalStateEmbed a] =
        [a].map (P01NTMRunLaws.liftConfig evalStateEmbed) by rfl]
  rw [eval_runBranches_map]
  exact List.mem_map.mpr ⟨b, h, rfl⟩

/-- Semantic/run certificate for the concrete verifier wrapper.

Starting from the exact witness-preparation layout, the fixed verifier core
reaches an accepting state carrying precisely the semantic circuit value.
No runtime majorant is claimed here. -/
theorem verifier_reaches_semantic_final
    (phi : Circuit)
    (w : SATWitness phi) :
    ∃ m tape,
      ({ state :=
           VerifierEvalState.eval
             (.final (evalCircuit (assignmentOfWitness phi w) phi)),
         tape := tape } : VerifierConfig) ∈
        verifierEvalMachine.runBranches m
          [{ state := verifierEvalMachine.initial,
             tape := P01WitnessPreservingPrep.preparedTape (witnessBits w) (encodeCircuit phi) }] := by
  have hnonempty : encodeCircuit phi ≠ [] :=
    encodeCircuit_ne_nil phi
  cases hsrc : encodeCircuit phi with
  | nil =>
      exact False.elim (hnonempty hsrc)
  | cons b bs =>
      obtain ⟨mEntry, hmEntry, hEntry⟩ :=
        prepared_nonempty_reaches_eval_start
          (witnessBits w) b bs

      have hlen : varBound phi ≤ (witnessBits w).length := by
        simpa [witnessBits_length]

      have hread :
          ∀ i, i < varBound phi →
            (witnessBits w).getD i false =
              assignmentOfWitness phi w i := by
        intro i hi
        exact witnessBits_getD_eq_assignment phi w i hi

      obtain ⟨mEval, cfg, hEval, hOutcome⟩ :=
        circuit_certificate
          (assignmentOfWitness phi w)
          (witnessBits w) phi
          [] [] 0 0 hlen hread

      have hOutcome' :
          ∃ tape : Tape (Option Bool),
            cfg =
              { state :=
                  EvalRunLoopState.final
                    (evalCircuit (assignmentOfWitness phi w) phi),
                tape := tape } := by
        simpa [LoopOutcome] using hOutcome

      rcases hOutcome' with ⟨tape, rfl⟩

      have hEvalLift :
          ({ state :=
               VerifierEvalState.eval
                 (.final (evalCircuit (assignmentOfWitness phi w) phi)),
             tape := tape } : VerifierConfig) ∈
            verifierEvalMachine.runBranches mEval
              [{ state := .eval evalRunLoopMachine.initial,
                 tape :=
                   evalCursorStackEndTape
                     (witnessBits w) 0 (encodeCircuit phi) [] 0 }] := by
        have h :=
          eval_mem_lift mEval
            ({ state := evalRunLoopMachine.initial,
               tape :=
                 evalCursorStackEndTape
                   (witnessBits w) 0 (encodeCircuit phi) [] 0 } :
              Configuration EvalRunLoopState (Option Bool))
            ({ state :=
                 .final (evalCircuit (assignmentOfWitness phi w) phi),
               tape := tape } :
              Configuration EvalRunLoopState (Option Bool))
            (by
              simpa [evalRunLoopMachine,
                P01EncodedFrameTape.encodeEvalFrames] using hEval)
        simpa [P01NTMRunLaws.liftConfig, evalStateEmbed] using h

      have hEntry' :
          ({ state := .eval evalRunLoopMachine.initial,
             tape :=
               evalCursorStackEndTape
                 (witnessBits w) 0 (encodeCircuit phi) [] 0 } :
            VerifierConfig) ∈
          verifierEvalMachine.runBranches mEntry
            [{ state := verifierEvalMachine.initial,
               tape :=
                 P01WitnessPreservingPrep.preparedTape (witnessBits w) (encodeCircuit phi) }] := by
        simpa [hsrc] using hEntry

      have hAll :=
        mem_runBranches_trans verifierEvalMachine
          mEntry mEval
          [{ state := verifierEvalMachine.initial,
             tape :=
               P01WitnessPreservingPrep.preparedTape (witnessBits w) (encodeCircuit phi) }]
          ({ state := .eval evalRunLoopMachine.initial,
             tape :=
               evalCursorStackEndTape
                 (witnessBits w) 0 (encodeCircuit phi) [] 0 } :
            VerifierConfig)
          ({ state :=
               .eval
                 (.final
                   (evalCircuit (assignmentOfWitness phi w) phi)),
             tape := tape } :
            VerifierConfig)
          hEntry' hEvalLift

      exact ⟨mEntry + mEval, tape, hAll⟩

/-- The reached semantic final state is accepting in the verifier wrapper. -/
theorem verifier_reaches_accepting_iff_eval_true
    (phi : Circuit)
    (w : SATWitness phi) :
    ∃ m tape,
      ({ state :=
           VerifierEvalState.eval
             (.final (evalCircuit (assignmentOfWitness phi w) phi)),
         tape := tape } : VerifierConfig) ∈
        verifierEvalMachine.runBranches m
          [{ state := verifierEvalMachine.initial,
             tape := P01WitnessPreservingPrep.preparedTape (witnessBits w) (encodeCircuit phi) }] ∧
      (verifierEvalMachine.accepting
          (.eval (.final (evalCircuit (assignmentOfWitness phi w) phi))) =
            true ↔
        evalCircuit (assignmentOfWitness phi w) phi = true) := by
  obtain ⟨m, tape, hrun⟩ :=
    verifier_reaches_semantic_final phi w
  refine ⟨m, tape, hrun, ?_⟩
  simp [verifierEvalMachine, evalRunLoopMachine]

#print axioms MCore.Real.P01VerifierEvalCircuitRun.witnessBits_getD_eq_assignment
#print axioms MCore.Real.P01VerifierEvalCircuitRun.eval_mem_lift
#print axioms MCore.Real.P01VerifierEvalCircuitRun.verifier_reaches_semantic_final
#print axioms MCore.Real.P01VerifierEvalCircuitRun.verifier_reaches_accepting_iff_eval_true

end P01VerifierEvalCircuitRun
end Real
end MCore
