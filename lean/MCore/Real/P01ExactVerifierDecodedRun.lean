import MCore.Real.P01ExactBoundedReject
import MCore.Real.P01ExactVerifierGlobalBudget
import MCore.Real.P01ExactVerifierCanonicalRun
import MCore.Real.P01CheckedVerifierCompositeNTM
import MCore.Real.P01CheckedVerifierRun
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01ExactVerifierDecodedRun

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01CNFMode
open P01EvalCursorMachine
open P01EncodedStackEvaluator
open P01CheckedEvalRunLoopNTM
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierRun
open P01CheckedVerifierInvariant
open P01CheckedEvalRunBoundedCertificate
open P01ExactBoundedReject
open P01ExactVerifierGlobalBudget
open P01ExactVerifierCanonicalRun
open P01WitnessPreservingPrep
open P01NTMRunLaws

abbrev CheckedVerifierConfig :=
  Configuration CheckedVerifierState (Option Bool)

/-- Canonical sources that decode to a circuit but fail the root CNF grammar
reach the verifier's explicit reject state within the same uniform cubic
budget used by the positive exact evaluator. -/
theorem prepared_cnf_invalid_reaches_reject_within_exact_global
    (sigma : Assignment)
    (witness : BitString)
    (phi : Circuit)
    (hmode : modeCheck .cnf phi = false)
    (hlen : varBound phi ≤ witness.length)
    (hread :
      ∀ i, i < varBound phi →
        witness.getD i false = sigma i) :
    ∃ m ≤ checkedVerifierExactTimeBound (encodeCircuit phi).length,
      ∃ tape,
        ({ state := .reject, tape := tape } : CheckedVerifierConfig) ∈
          checkedVerifierMachine.runBranches m
            [{ state := checkedVerifierMachine.initial,
               tape := preparedTape witness (encodeCircuit phi) }] := by
  have hne : encodeCircuit phi ≠ [] :=
    P01ExactBoundedCircuitProducer.encodeCircuit_ne_nil phi
  cases hsrc : encodeCircuit phi with
  | nil =>
      exact False.elim (hne hsrc)
  | cons b bs =>
      let n := (b :: bs).length
      obtain ⟨m0, hm0, h0⟩ :=
        prepared_nonempty_reaches_eval_start witness b bs

      have hLayout :
          CheckedLayoutBound n 0
            (encodeCircuit phi ++ ([] : BitString))
            (P01EncodedFrameTape.encodeEvalFrames []) := by
        constructor
        · simp [n, hsrc]
        · simp

      have hcert :=
        circuit_exact_bounded_reject sigma witness phi .cnf
      obtain ⟨m1, hm1, cfg1, h1, hrej⟩ :=
        hcert hmode [] [] 0 0 n hLayout hlen hread

      have h1src :
          cfg1 ∈
            checkedEvalRunLoopMachine.runBranches m1
              [{ state := checkedEvalRunLoopMachine.initial,
                 tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 }] := by
        simpa [checkedEvalRunLoopMachine, hsrc] using h1

      rcases cfg1 with ⟨q1, tape1⟩
      simp only at hrej
      subst q1

      have hLift :
          ({ state := .reject, tape := tape1 } : CheckedVerifierConfig) ∈
            checkedVerifierMachine.runBranches m1
              [({ state := .eval checkedEvalRunLoopMachine.initial,
                  tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 } :
                CheckedVerifierConfig)] := by
        have hlift :=
          checked_eval_mem_lift m1
            ({ state := checkedEvalRunLoopMachine.initial,
               tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 } :
              Configuration CheckedEvalRunState (Option Bool))
            ({ state := .reject, tape := tape1 } :
              Configuration CheckedEvalRunState (Option Bool))
            h1src
        simpa [checkedEvalEmbed, P01NTMRunLaws.liftConfig] using hlift

      have hAll :=
        mem_runBranches_trans checkedVerifierMachine
          m0 m1
          [{ state := checkedVerifierMachine.initial,
             tape := preparedTape witness (b :: bs) }]
          ({ state := .eval checkedEvalRunLoopMachine.initial,
             tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 } :
            CheckedVerifierConfig)
          ({ state := .reject, tape := tape1 } : CheckedVerifierConfig)
          h0 hLift

      have hscan :
          m0 ≤ 256 * (n + 1) ^ 2 :=
        Nat.le_trans hm0 (scan_entry_le_exact_allowance n)

      have henc : (encodeCircuit phi).length ≤ n := by
        simp [n, hsrc]
      have hcap :=
        exact_evaluation_plus_scan_le_global n phi henc
      have hbudget :
          m0 + m1 ≤ checkedVerifierExactTimeBound n := by
        omega

      refine ⟨m0 + m1, ?_, tape1, ?_⟩
      · simpa [n, hsrc] using hbudget
      · simpa [hsrc] using hAll

#print axioms MCore.Real.P01ExactVerifierDecodedRun.prepared_cnf_invalid_reaches_reject_within_exact_global

end P01ExactVerifierDecodedRun
end Real
end MCore
