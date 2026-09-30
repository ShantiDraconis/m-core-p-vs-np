import MCore.Real.P01ExactBoundedCircuitProducer
import MCore.Real.P01ExactVerifierGlobalBudget
import MCore.Real.P01CheckedVerifierCompositeNTM
import MCore.Real.P01CheckedVerifierRun
import MCore.Real.P01CheckedVerifierDeterminism

namespace MCore
namespace Real
namespace P01ExactVerifierCanonicalRun

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01CNFMode
open P01EvalCursorMachine
open P01EncodedStackEvaluator
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBaseCases
open P01CheckedVerifierInvariant
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierRun
open P01CheckedVerifierDeterminism
open P01ExactBoundedCircuitProducer
open P01ExactVerifierGlobalBudget
open P01WitnessPreservingPrep
open P01NTMRunLaws

abbrev CheckedVerifierConfig :=
  Configuration CheckedVerifierState (Option Bool)

/-- The scanner/entry prefix is absorbed by the exact verifier's reserved
quadratic overhead. -/
theorem scan_entry_le_exact_allowance
    (n : Nat) :
    n + 3 ≤ 256 * (n + 1) ^ 2 := by
  have h1 : n + 3 ≤ 4 * (n + 1) := by omega
  have hsq : n + 1 ≤ (n + 1) ^ 2 := by
    have hpos : 1 ≤ n + 1 := by omega
    calc
      n + 1 = (n + 1) * 1 := by simp
      _ ≤ (n + 1) * (n + 1) :=
        Nat.mul_le_mul_left (n + 1) hpos
      _ = (n + 1) ^ 2 := by simp [pow_two]
  have h4 := Nat.mul_le_mul_left 4 hsq
  calc
    n + 3 ≤ 4 * (n + 1) := h1
    _ ≤ 4 * (n + 1) ^ 2 := h4
    _ ≤ 256 * (n + 1) ^ 2 := by
      exact Nat.mul_le_mul_right ((n + 1) ^ 2) (by omega)

/-- Valid canonical CNF sources reach the semantic final state within one
uniform cubic fuel.  This is the quantitative whole-verifier adapter from the
exact recursive producer. -/
theorem prepared_cnf_reaches_semantic_final_within_exact_global
    (sigma : Assignment)
    (witness : BitString)
    (phi : Circuit)
    (hmode : modeCheck .cnf phi = true)
    (hlen : varBound phi ≤ witness.length)
    (hread :
      ∀ i, i < varBound phi →
        witness.getD i false = sigma i) :
    ∃ m ≤ checkedVerifierExactTimeBound (encodeCircuit phi).length,
      ∃ tape,
        ({ state := .eval (.final (evalCircuit sigma phi)),
           tape := tape } : CheckedVerifierConfig) ∈
          checkedVerifierMachine.runBranches m
            [{ state := checkedVerifierMachine.initial,
               tape := preparedTape witness (encodeCircuit phi) }] := by
  have hne : encodeCircuit phi ≠ [] :=
    encodeCircuit_ne_nil phi
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
            (encodeEvalFrames []) := by
        constructor
        · simp [n, hsrc]
        · simp

      have hcert :=
        circuit_exact_bounded_certificate sigma witness phi .cnf
      obtain ⟨m1, hm1, cfg1, h1, hout1⟩ :=
        hcert hmode [] [] 0 0 n hLayout hlen hread

      have h1src :
          cfg1 ∈
            checkedEvalRunLoopMachine.runBranches m1
              [{ state := checkedEvalRunLoopMachine.initial,
                 tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 }] := by
        simpa [checkedEvalRunLoopMachine, hsrc] using h1

      simp [ExactCheckedLoopOutcome] at hout1
      rcases hout1 with ⟨tape1, hcfg1⟩
      subst cfg1

      have hLift :
          ({ state := .eval (.final (evalCircuit sigma phi)),
             tape := tape1 } : CheckedVerifierConfig) ∈
            checkedVerifierMachine.runBranches m1
              [({ state := .eval checkedEvalRunLoopMachine.initial,
                  tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 } :
                CheckedVerifierConfig)] := by
        have hlift :=
          checked_eval_mem_lift m1
            ({ state := checkedEvalRunLoopMachine.initial,
               tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 } :
              Configuration CheckedEvalRunState (Option Bool))
            ({ state := .final (evalCircuit sigma phi),
               tape := tape1 } :
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
          ({ state := .eval (.final (evalCircuit sigma phi)),
             tape := tape1 } : CheckedVerifierConfig)
          h0 hLift

      have hscan :
          m0 ≤ 256 * (n + 1) ^ 2 :=
        Nat.le_trans hm0 (scan_entry_le_exact_allowance n)

      have hbudget :
          m0 + m1 ≤ checkedVerifierExactTimeBound n := by
        have henc : (encodeCircuit phi).length ≤ n := by
          simp [n, hsrc]
        have hcap :=
          exact_evaluation_plus_scan_le_global n phi henc
        omega

      refine ⟨m0 + m1, ?_, tape1, ?_⟩
      · simpa [n, hsrc] using hbudget
      · simpa [hsrc] using hAll

#print axioms MCore.Real.P01ExactVerifierCanonicalRun.scan_entry_le_exact_allowance
#print axioms MCore.Real.P01ExactVerifierCanonicalRun.prepared_cnf_reaches_semantic_final_within_exact_global

end P01ExactVerifierCanonicalRun
end Real
end MCore
