import MCore.Real.P01RawVerifierMaterialCore
import MCore.Real.P01MalformedRawBoundedReject
import MCore.Real.P01CanonicalWrapperBounded
import MCore.Real.P01CheckedEvalRejectBounded
import MCore.Real.P01DecodeCoreLaws
import MCore.Real.P01CheckedVerifierDeterminism
import MCore.Real.P01MaterialInhabitantFrontier

namespace MCore
namespace Real
namespace P01RawVerifierFromCoreReject

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01CNFMode
open P01WitnessPreservingPrep
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedVerifierInvariant
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierDeterminism
open P01CheckedEvalRejectBounded
open P01MalformedRawBoundedReject
open P01CanonicalWrapperBounded
open P01MaterialGlobalBudget
open P01DecodeCoreLaws
open P01RawVerifierMaterialCore
open P01NTMRunLaws

abbrev VConfig :=
  Configuration CheckedVerifierState (Option Bool)

abbrev EConfig :=
  Configuration CheckedEvalRunState (Option Bool)

private theorem wrapper_reject_not_accepts
    (T m : Nat) (start terminal : VConfig)
    (hm : m ≤ T)
    (hmem : terminal ∈ checkedVerifierMachine.runBranches m [start])
    (hrej : terminal.state = .reject) :
    ¬ checkedVerifierMachine.AcceptsWithin T start := by
  rcases terminal with ⟨q, tape⟩
  simp only at hrej
  subst q
  let terminal : VConfig := { state := .reject, tape := tape }
  have hmem' :
      terminal ∈ checkedVerifierMachine.runBranches m [start] := by
    simpa [terminal] using hmem
  have hhalt : Halted checkedVerifierMachine terminal := by
    simp [terminal, Halted, checkedVerifierMachine]
  have hp :=
    mem_runBranches_persist checkedVerifierMachine
      m (T - m) [start] terminal hmem' hhalt
  have hpT : terminal ∈ checkedVerifierMachine.runBranches T [start] := by
    rwa [show m + (T - m) = T by omega] at hp
  have heq :=
    runBranches_eq_singleton_of_mem T start terminal hpT
  intro hacc
  rcases hacc with ⟨z, hz, hza⟩
  rw [heq] at hz
  simp only [List.mem_singleton] at hz
  subst z
  simp [terminal, checkedVerifierMachine] at hza

private theorem wrapper_final_accepts_iff
    (T m : Nat) (start : VConfig)
    (value : Bool) (tape : Tape (Option Bool))
    (hm : m ≤ T)
    (hmem :
      ({ state := .eval (.final value), tape := tape } : VConfig) ∈
        checkedVerifierMachine.runBranches m [start]) :
    checkedVerifierMachine.AcceptsWithin T start ↔ value = true := by
  let terminal : VConfig := { state := .eval (.final value), tape := tape }
  have hhalt : Halted checkedVerifierMachine terminal := by
    cases value <;>
      simp [terminal, Halted, checkedVerifierMachine,
        checkedEvalRunLoopMachine]
  have hp :=
    mem_runBranches_persist checkedVerifierMachine
      m (T - m) [start] terminal (by simpa [terminal] using hmem) hhalt
  have hpT : terminal ∈ checkedVerifierMachine.runBranches T [start] := by
    rwa [show m + (T - m) = T by omega] at hp
  have heq :=
    runBranches_eq_singleton_of_mem T start terminal hpT
  constructor
  · rintro ⟨z,hz,hacc⟩
    rw [heq] at hz
    simp only [List.mem_singleton] at hz
    subst z
    cases value <;>
      simp [terminal, checkedVerifierMachine, checkedEvalRunLoopMachine] at hacc ⊢
  · intro hv
    subst value
    refine ⟨terminal, hpT, ?_⟩
    simp [terminal, checkedVerifierMachine, checkedEvalRunLoopMachine]

private theorem empty_wrapper_reaches_reject
    (witness : BitString) :
    ({ state := .reject, tape := preparedTape witness [] } : VConfig) ∈
      checkedVerifierMachine.runBranches 1
        [{ state := checkedVerifierMachine.initial,
           tape := preparedTape witness [] }] := by
  have hactive :
      ¬ Halted checkedVerifierMachine
        ({ state := checkedVerifierMachine.initial,
           tape := preparedTape witness [] } : VConfig) := by
    simp [Halted, checkedVerifierMachine, preparedTape]
  have hsucc :
      ({ state := .reject, tape := preparedTape witness [] } : VConfig) ∈
        checkedVerifierMachine.successors
          { state := checkedVerifierMachine.initial,
            tape := preparedTape witness [] } := by
    simp [checkedVerifierMachine, NTM.successors, NTM.stepBranch,
      preparedTape, Tape.write, Tape.move]
  have h :=
    mem_runBranches_succ_of_successor checkedVerifierMachine
      0
      [({ state := checkedVerifierMachine.initial,
          tape := preparedTape witness [] } : VConfig)]
      ({ state := checkedVerifierMachine.initial,
          tape := preparedTape witness [] } : VConfig)
      ({ state := .reject, tape := preparedTape witness [] } : VConfig)
      (by simp [NTM.runBranches]) hactive hsucc
  simpa using h

/-- Lift an evaluator-level rejection of a nonempty source through the physical
source scanner into the complete verifier wrapper. -/
private theorem lift_eval_reject_to_wrapper
    (witness bs : BitString)
    (hne : bs ≠ [])
    (me : Nat) (cfg : EConfig)
    (hme : me ≤ materialVerifierGlobalTimeBound bs.length)
    (hrun :
      cfg ∈ checkedEvalRunLoopMachine.runBranches me
        [{ state := .need .cnf needExprCompositeMachine.initial,
           tape := evalCursorStackEndTape witness 0 bs [] 0 }])
    (hrej : cfg.state = .reject) :
    ∃ m ≤ terminalVerifierTimeBound bs.length, ∃ terminal : VConfig,
      terminal ∈ checkedVerifierMachine.runBranches m
        [{ state := checkedVerifierMachine.initial,
           tape := preparedTape witness bs }] ∧
      terminal.state = .reject := by
  cases hbs : bs with
  | nil =>
      exact (hne hbs).elim
  | cons b rest =>
      obtain ⟨mp,hmp,hprep⟩ :=
        prepared_nonempty_reaches_eval_start witness b rest

      rcases cfg with ⟨q,tape⟩
      simp only at hrej
      subst q

      have hembed :
          ({ state := .reject, tape := tape } : VConfig) ∈
            checkedVerifierMachine.runBranches me
              [{ state := .eval checkedEvalRunLoopMachine.initial,
                 tape := evalCursorStackEndTape witness 0 bs [] 0 }] := by
        have hmap :=
          checked_eval_runBranches_map me
            [({ state := checkedEvalRunLoopMachine.initial,
                tape := evalCursorStackEndTape witness 0 bs [] 0 } : EConfig)]
        rw [hmap]
        apply List.mem_map.mpr
        refine ⟨({ state := .reject, tape := tape } : EConfig), ?_, rfl⟩
        exact hrun

      have hprep' :
          ({ state := .eval checkedEvalRunLoopMachine.initial,
             tape := evalCursorStackEndTape witness 0 bs [] 0 } : VConfig) ∈
            checkedVerifierMachine.runBranches mp
              [{ state := checkedVerifierMachine.initial,
                 tape := preparedTape witness bs }] := by
        simpa [hbs] using hprep

      have hall :=
        mem_runBranches_trans checkedVerifierMachine mp me
          [{ state := checkedVerifierMachine.initial,
             tape := preparedTape witness bs }]
          ({ state := .eval checkedEvalRunLoopMachine.initial,
             tape := evalCursorStackEndTape witness 0 bs [] 0 } : VConfig)
          ({ state := .reject, tape := tape } : VConfig)
          hprep' hembed

      have hsum :
          mp + me ≤ bs.length + 3 +
            materialVerifierGlobalTimeBound bs.length := by
        omega
      refine ⟨mp + me,
        Nat.le_trans hsum (entry_plus_material_le_terminal bs.length),
        ({ state := .reject, tape := tape } : VConfig), hall, rfl⟩

/-- Decoder failure produces a complete-wrapper reject branch. -/
theorem decode_none_wrapper_reject
    (K : CoreDecodeFailurePhysicalReject)
    (witness bs : BitString)
    (hw : witness.length = bs.length)
    (hdecode : decodeCircuit bs = none) :
    ∃ m ≤ terminalVerifierTimeBound bs.length, ∃ terminal : VConfig,
      terminal ∈ checkedVerifierMachine.runBranches m
        [{ state := checkedVerifierMachine.initial,
           tape := preparedTape witness bs }] ∧
      terminal.state = .reject := by
  cases hbs : bs with
  | nil =>
      refine ⟨1, ?_, ({ state := .reject,
        tape := preparedTape witness [] } : VConfig), ?_, rfl⟩
      · unfold terminalVerifierTimeBound
        omega
      · exact empty_wrapper_reaches_reject witness
  | cons b rest =>
      obtain ⟨me,hme,cfg,hrun,hrej⟩ :=
        malformed_raw_reaches_reject_bounded_of_core
          K witness (b :: rest) hw hdecode
      exact lift_eval_reject_to_wrapper
        witness (b :: rest) (by simp) me cfg hme hrun hrej

/-- A successfully decoded but non-CNF circuit is physically rejected by the
bounded structural-rejection induction. -/
theorem decoded_noncnf_wrapper_reject
    (witness bs : BitString)
    (hw : witness.length = bs.length)
    (phi : Circuit)
    (hdecode : decodeCircuit bs = some phi)
    (hnot : ¬ IsCNF phi) :
    ∃ m ≤ terminalVerifierTimeBound bs.length, ∃ terminal : VConfig,
      terminal ∈ checkedVerifierMachine.runBranches m
        [{ state := checkedVerifierMachine.initial,
           tape := preparedTape witness bs }] ∧
      terminal.state = .reject := by
  have hshape : bs = encodeCircuit phi :=
    decodeCircuit_sound bs phi hdecode
  have hmode : modeCheck .cnf phi = false := by
    cases hm : modeCheck .cnf phi with
    | false => rfl
    | true =>
        exact False.elim (hnot ((modeCheck_cnf_iff phi).1 hm))
  let sigma : Assignment := fun i => witness.getD i false
  have hlen : varBound phi ≤ witness.length := by
    rw [hw, hshape]
    exact varBound_le_encoded_length phi
  have hread :
      ∀ i, i < varBound phi →
        witness.getD i false = sigma i := by
    intro i hi
    rfl
  have hLayout :
      CheckedLayoutBound bs.length 0
        (encodeCircuit phi ++ []) (encodeEvalFrames []) := by
    simpa [hshape] using CheckedLayoutBound.root bs
  obtain ⟨me,hme,cfg,hrun,hrej⟩ :=
    bounded_circuit_reject_certificate sigma witness phi .cnf
      hmode [] [] 0 0 bs.length hLayout hlen hread
  have henc : (encodeCircuit phi).length ≤ bs.length := by
    rw [hshape]
  have h6144 :=
    checkedCircuitBudget_le_6144_cubic bs.length phi henc
  have hmat :
      checkedCircuitBudget phi bs.length ≤
        materialVerifierGlobalTimeBound bs.length := by
    exact Nat.le_trans h6144 (by
      unfold materialVerifierGlobalTimeBound
      exact Nat.mul_le_mul_right ((bs.length + 1)^3) (by omega))
  have hme' : me ≤ materialVerifierGlobalTimeBound bs.length :=
    Nat.le_trans hme hmat
  exact lift_eval_reject_to_wrapper
    witness bs (by
      intro hz
      rw [hz] at hshape
      cases phi <;> simp [encodeCircuit] at hshape)
    me cfg hme' (by simpa [hshape] using hrun) hrej

/-- The only remaining physical premise for the raw verifier is recursive core
decoder failure.  All other verifier semantics are now derived. -/
def rawVerifierMaterialCoreOfCoreReject
    (K : CoreDecodeFailurePhysicalReject) :
    RawVerifierMaterialCore where
  halts := by
    intro bs witness hw
    cases hdec : decodeCircuit bs with
    | none =>
        obtain ⟨m,hm,terminal,hmem,hrej⟩ :=
          decode_none_wrapper_reject K witness bs hw hdec
        have hhalt : Halted checkedVerifierMachine terminal := by
          rcases terminal with ⟨q,tape⟩
          simp only at hrej
          subst q
          simp [Halted, checkedVerifierMachine]
        have hs :=
          haltsWithin_of_reaches_halted m
            ({ state := checkedVerifierMachine.initial,
               tape := preparedTape witness bs } : VConfig)
            terminal hmem hhalt
        exact haltsWithin_mono_le checkedVerifierMachine m
          (terminalVerifierTimeBound bs.length) _ hm hs
    | some phi =>
        by_cases hCNF : IsCNF phi
        · have hshape := decodeCircuit_sound bs phi hdec
          have hlen : (encodeCircuit phi).length ≤ witness.length := by
            rw [← hshape, hw]
          have hs :=
            canonical_cnf_halts_bounded phi witness hCNF hlen
          rw [hshape] at hs
          exact haltsWithin_mono_le checkedVerifierMachine
            (materialVerifierGlobalTimeBound bs.length)
            (terminalVerifierTimeBound bs.length)
            _ (material_le_terminal bs.length) hs
        · obtain ⟨m,hm,terminal,hmem,hrej⟩ :=
            decoded_noncnf_wrapper_reject witness bs hw phi hdec hCNF
          have hhalt : Halted checkedVerifierMachine terminal := by
            rcases terminal with ⟨q,tape⟩
            simp only at hrej
            subst q
            simp [Halted, checkedVerifierMachine]
          have hs :=
            haltsWithin_of_reaches_halted m
              ({ state := checkedVerifierMachine.initial,
                 tape := preparedTape witness bs } : VConfig)
              terminal hmem hhalt
          exact haltsWithin_mono_le checkedVerifierMachine m
            (terminalVerifierTimeBound bs.length) _ hm hs
  correct := by
    intro bs witness hw
    cases hdec : decodeCircuit bs with
    | none =>
        obtain ⟨m,hm,terminal,hmem,hrej⟩ :=
          decode_none_wrapper_reject K witness bs hw hdec
        have hnotAcc :=
          wrapper_reject_not_accepts
            (terminalVerifierTimeBound bs.length) m
            ({ state := checkedVerifierMachine.initial,
               tape := preparedTape witness bs } : VConfig)
            terminal hm hmem hrej
        have hnotVerify : ¬ VerifyBits bs witness :=
          verifyBits_false_of_decode_none bs witness hdec
        constructor
        · intro h
          exact False.elim (hnotAcc h)
        · intro h
          exact False.elim (hnotVerify h)
    | some phi =>
        by_cases hCNF : IsCNF phi
        · have hshape := decodeCircuit_sound bs phi hdec
          have hlen : (encodeCircuit phi).length ≤ witness.length := by
            rw [← hshape, hw]
          obtain ⟨m,hm,tape,hreach⟩ :=
            canonical_cnf_reaches_final_bounded phi witness hCNF hlen
          have hmT :
              m ≤ terminalVerifierTimeBound bs.length := by
            rw [hshape]
            exact Nat.le_trans hm (material_le_terminal (encodeCircuit phi).length)
          have hiff :=
            wrapper_final_accepts_iff
              (terminalVerifierTimeBound bs.length) m
              ({ state := checkedVerifierMachine.initial,
                 tape := preparedTape witness bs } : VConfig)
              (evalCircuit (fun i => witness.getD i false) phi)
              tape hmT (by simpa [hshape] using hreach)
          rw [hiff]
          constructor
          · intro heval
            exact ⟨phi, hdec, hCNF, heval⟩
          · rintro ⟨phi',hdec',hcnf',heval'⟩
            rw [hdec] at hdec'
            injection hdec' with hphi
            subst phi'
            exact heval'
        · obtain ⟨m,hm,terminal,hmem,hrej⟩ :=
            decoded_noncnf_wrapper_reject witness bs hw phi hdec hCNF
          have hnotAcc :=
            wrapper_reject_not_accepts
              (terminalVerifierTimeBound bs.length) m
              ({ state := checkedVerifierMachine.initial,
                 tape := preparedTape witness bs } : VConfig)
              terminal hm hmem hrej
          have hnotVerify : ¬ VerifyBits bs witness := by
            intro hv
            rcases hv with ⟨phi',hdec',hcnf',heval'⟩
            rw [hdec] at hdec'
            injection hdec' with hphi
            subst phi'
            exact hCNF hcnf'
          constructor
          · intro h
            exact False.elim (hnotAcc h)
          · intro h
            exact False.elim (hnotVerify h)

theorem p01_of_core_decode_failure_physical_reject
    (K : CoreDecodeFailurePhysicalReject) :
    P01FinalCertificate.P01ConstructionGap :=
  P01MaterialInhabitantFrontier.p01_of_raw_material_core
    (rawVerifierMaterialCoreOfCoreReject K)

#print axioms MCore.Real.P01RawVerifierFromCoreReject.rawVerifierMaterialCoreOfCoreReject
#print axioms MCore.Real.P01RawVerifierFromCoreReject.p01_of_core_decode_failure_physical_reject

end P01RawVerifierFromCoreReject
end Real
end MCore
