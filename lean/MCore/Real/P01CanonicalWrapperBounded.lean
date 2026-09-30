import MCore.Real.P01ExactBoundedAll
import MCore.Real.P01CheckedVerifierCompositeNTM
import MCore.Real.P01CheckedVerifierDeterminism
import MCore.Real.P01MaterialGlobalBudget
import MCore.Real.P01CheckedVerifierInvariant

namespace MCore
namespace Real
namespace P01CanonicalWrapperBounded

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01CNFMode
open P01ExactBoundedCircuitProducer
open P01ExactBoundedAll
open P01CheckedVerifierInvariant
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierDeterminism
open P01CheckedEvalRunLoopNTM
open P01MaterialGlobalBudget
open P01NTMRunLaws

/-- Every canonical circuit encoding is nonempty. -/
theorem encodeCircuit_ne_nil (phi : Circuit) :
    encodeCircuit phi ≠ [] := by
  cases phi <;> simp [encodeCircuit]

/-- Exact physical terminal reachability for a canonical CNF circuit through
the complete checked verifier wrapper.

This theorem includes:
1. wrapper source scan,
2. evaluator handoff,
3. exact bounded recursive evaluation,
4. global cubic accounting.
-/
theorem canonical_cnf_reaches_final_bounded
    (phi : Circuit)
    (witness : BitString)
    (hCNF : IsCNF phi)
    (hlen : (encodeCircuit phi).length ≤ witness.length) :
    ∃ m ≤ materialVerifierGlobalTimeBound (encodeCircuit phi).length,
      ∃ tape : Tape (Option Bool),
        ({ state := .eval (.final
              (evalCircuit (fun i => witness.getD i false) phi)),
           tape := tape } :
          Configuration CheckedVerifierState (Option Bool)) ∈
        checkedVerifierMachine.runBranches m
          [{ state := checkedVerifierMachine.initial,
             tape := preparedTape witness (encodeCircuit phi) }] := by
  have hmode : modeCheck .cnf phi = true :=
    (modeCheck_cnf_iff phi).2 hCNF

  have hvar : varBound phi ≤ witness.length :=
    Nat.le_trans (varBound_le_encoded_length phi) hlen

  have hread :
      ∀ i, i < varBound phi →
        witness.getD i false =
          (fun j => witness.getD j false) i := by
    intro i hi
    rfl

  have hLayout :
      CheckedLayoutBound (encodeCircuit phi).length 0
        (encodeCircuit phi ++ []) (encodeEvalFrames []) := by
    simpa using CheckedLayoutBound.root (encodeCircuit phi)

  obtain ⟨me, hme, cfg, hEval, hOutcome⟩ :=
    exact_bounded_all
      (fun i => witness.getD i false) witness phi .cnf
      hmode [] [] 0 0 (encodeCircuit phi).length
      hLayout hvar hread

  rcases hOutcome with ⟨terminalTape, hcfg⟩
  subst cfg

  have hEvalWrapped :
      ({ state := .eval (.final
            (evalCircuit (fun i => witness.getD i false) phi)),
         tape := terminalTape } :
        Configuration CheckedVerifierState (Option Bool)) ∈
      checkedVerifierMachine.runBranches me
        [{ state := .eval checkedEvalRunLoopMachine.initial,
           tape :=
             evalCursorStackEndTape witness 0
               (encodeCircuit phi) [] 0 }] := by
    have hmap :=
      checked_eval_runBranches_map me
        [({ state := checkedEvalRunLoopMachine.initial,
            tape :=
              evalCursorStackEndTape witness 0
                (encodeCircuit phi) [] 0 } :
          Configuration CheckedEvalRunState (Option Bool))]
    rw [hmap]
    apply List.mem_map.mpr
    refine ⟨({ state := .final
          (evalCircuit (fun i => witness.getD i false) phi),
        tape := terminalTape } :
      Configuration CheckedEvalRunState (Option Bool)), ?_, ?_⟩
    · simpa using hEval
    · rfl

  cases hbits : encodeCircuit phi with
  | nil =>
      exact (encodeCircuit_ne_nil phi hbits).elim
  | cons b bs =>
      obtain ⟨mp, hmp, hPrep⟩ :=
        prepared_nonempty_reaches_eval_start witness b bs

      have hPrep' :
          ({ state := .eval checkedEvalRunLoopMachine.initial,
             tape :=
               evalCursorStackEndTape witness 0
                 (encodeCircuit phi) [] 0 } :
            Configuration CheckedVerifierState (Option Bool)) ∈
          checkedVerifierMachine.runBranches mp
            [{ state := checkedVerifierMachine.initial,
               tape := preparedTape witness (encodeCircuit phi) }] := by
        simpa [hbits] using hPrep

      have hAll :=
        mem_runBranches_trans checkedVerifierMachine
          mp me
          [{ state := checkedVerifierMachine.initial,
             tape := preparedTape witness (encodeCircuit phi) }]
          ({ state := .eval checkedEvalRunLoopMachine.initial,
             tape :=
               evalCursorStackEndTape witness 0
                 (encodeCircuit phi) [] 0 } :
            Configuration CheckedVerifierState (Option Bool))
          ({ state := .eval (.final
              (evalCircuit (fun i => witness.getD i false) phi)),
             tape := terminalTape } :
            Configuration CheckedVerifierState (Option Bool))
          hPrep' hEvalWrapped

      have hsum :
          mp + me ≤
            (encodeCircuit phi).length + 3 +
              checkedCircuitBudget phi (encodeCircuit phi).length := by
        omega

      have hglobal :=
        entry_plus_checkedCircuitBudget_le_material
          (encodeCircuit phi).length phi (by exact Nat.le_refl _)

      refine ⟨mp + me, Nat.le_trans hsum hglobal, terminalTape, ?_⟩
      exact hAll

/-- Canonical wrapper executions halt within the material cubic bound,
independently of the Boolean result. -/
theorem canonical_cnf_halts_bounded
    (phi : Circuit)
    (witness : BitString)
    (hCNF : IsCNF phi)
    (hlen : (encodeCircuit phi).length ≤ witness.length) :
    checkedVerifierMachine.HaltsWithin
      (materialVerifierGlobalTimeBound (encodeCircuit phi).length)
      { state := checkedVerifierMachine.initial,
        tape := preparedTape witness (encodeCircuit phi) } := by
  obtain ⟨m, hm, tape, hreach⟩ :=
    canonical_cnf_reaches_final_bounded phi witness hCNF hlen
  have hhalt :
      Halted checkedVerifierMachine
        ({ state := .eval (.final
              (evalCircuit (fun i => witness.getD i false) phi)),
           tape := tape } :
          Configuration CheckedVerifierState (Option Bool)) := by
    simp [Halted, checkedVerifierMachine, checkedEvalRunLoopMachine]
  have hsmall :=
    haltsWithin_of_reaches_halted m
      ({ state := checkedVerifierMachine.initial,
         tape := preparedTape witness (encodeCircuit phi) } :
        Configuration CheckedVerifierState (Option Bool))
      ({ state := .eval (.final
          (evalCircuit (fun i => witness.getD i false) phi)),
         tape := tape } :
        Configuration CheckedVerifierState (Option Bool))
      hreach hhalt
  exact haltsWithin_mono_le checkedVerifierMachine m
    (materialVerifierGlobalTimeBound (encodeCircuit phi).length)
    _ hm hsmall

#print axioms MCore.Real.P01CanonicalWrapperBounded.canonical_cnf_reaches_final_bounded
#print axioms MCore.Real.P01CanonicalWrapperBounded.canonical_cnf_halts_bounded

end P01CanonicalWrapperBounded
end Real
end MCore
