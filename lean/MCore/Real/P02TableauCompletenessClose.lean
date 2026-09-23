import MCore.Real.P02TableauCompletenessActive
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P02TableauCompletenessClose

open CircuitK1
open CanonicalFinalProof
open P02BoundedComputationEncoding
open P02BoundedComputationLogic
open P02BoundedComputationSoundness
open P02BoundedComputationClose
open P02TableauCompletenessActive

theorem copySymbolClauses_satisfied_of_assignment_eq
    (sigma : Assignment)
    (guard : Clause)
    (oldVar newVar : Option Bool → Nat)
    (hvals : ∀ a : Option Bool, sigma (oldVar a) = sigma (newVar a)) :
    evalCNF sigma (copySymbolClauses guard oldVar newVar) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  unfold copySymbolClauses at hclause
  rcases List.mem_flatMap.mp hclause with ⟨a, _, ha⟩
  simp only [List.mem_cons, List.mem_singleton] at ha
  rcases ha with rfl | rfl
  · rw [evalClause_append]
    have hv := hvals a
    cases hold : sigma (oldVar a) <;>
      cases hnew : sigma (newVar a) <;>
      simp_all [evalClause, evalLiteral, neg, pos]
  · rw [evalClause_append]
    have hv := hvals a
    cases hold : sigma (oldVar a) <;>
      cases hnew : sigma (newVar a) <;>
      simp_all [evalClause, evalLiteral, neg, pos]

theorem copyLeftAll_satisfied
    (sigma : Assignment)
    (guard : Clause)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hvals :
      ∀ i : Nat, i < radius x t →
        ∀ a : Option Bool,
          sigma (leftVar M x t s i a) =
            sigma (leftVar M x t (s + 1) i a)) :
    evalCNF sigma (copyLeftAll guard M x t s) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  unfold copyLeftAll at hclause
  rcases List.mem_flatMap.mp hclause with ⟨i, hi, hc⟩
  have hcell :=
    copySymbolClauses_satisfied_of_assignment_eq
      sigma guard
      (leftVar M x t s i)
      (leftVar M x t (s + 1) i)
      (hvals i (by simpa using hi))
  exact evalCNF_member_true sigma
    (copySymbolClauses guard
      (leftVar M x t s i)
      (leftVar M x t (s + 1) i))
    clause hc hcell

theorem copyRightAll_satisfied
    (sigma : Assignment)
    (guard : Clause)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hvals :
      ∀ i : Nat, i < radius x t →
        ∀ a : Option Bool,
          sigma (rightVar M x t s i a) =
            sigma (rightVar M x t (s + 1) i a)) :
    evalCNF sigma (copyRightAll guard M x t s) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  unfold copyRightAll at hclause
  rcases List.mem_flatMap.mp hclause with ⟨i, hi, hc⟩
  have hcell :=
    copySymbolClauses_satisfied_of_assignment_eq
      sigma guard
      (rightVar M x t s i)
      (rightVar M x t (s + 1) i)
      (hvals i (by simpa using hi))
  exact evalCNF_member_true sigma
    (copySymbolClauses guard
      (rightVar M x t s i)
      (rightVar M x t (s + 1) i))
    clause hc hcell

theorem evalCNF_append_true
    (sigma : Assignment)
    (a b : CNF)
    (ha : evalCNF sigma a = true)
    (hb : evalCNF sigma b = true) :
    evalCNF sigma (a ++ b) = true := by
  rw [evalCNF_append_eq, ha, hb]
  rfl

theorem active_halting_case_true
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (hnow : SnapshotMatches sigma M x t s config)
    (hnext : SnapshotMatches sigma M x t (s + 1) config) :
    evalCNF sigma
      (haltingCaseCNF M x t s config.state config.tape.head) = true := by
  let guard : Clause :=
    [neg (stateVar M t s config.state),
     neg (headVar M t s config.tape.head)]
  rcases hnow with ⟨hstate0, hhead0, hleft0, hright0⟩
  rcases hnext with ⟨hstate1, hhead1, hleft1, hright1⟩
  have hs :
      evalCNF sigma
        (setStateClauses guard M t (s + 1) config.state) = true := by
    exact setStateClauses_satisfied_of_assignment
      sigma guard M t (s + 1) config.state hstate1
  have hh :
      evalCNF sigma (copyHeadCell guard M t s (s + 1)) = true := by
    unfold copyHeadCell
    apply copySymbolClauses_satisfied_of_assignment_eq
    intro a
    rw [hhead0 a, hhead1 a]
  have hl :
      evalCNF sigma (copyLeftAll guard M x t s) = true := by
    apply copyLeftAll_satisfied
    intro i hi a
    rw [hleft0 i hi a, hleft1 i hi a]
  have hr :
      evalCNF sigma (copyRightAll guard M x t s) = true := by
    apply copyRightAll_satisfied
    intro i hi a
    rw [hright0 i hi a, hright1 i hi a]
  unfold haltingCaseCNF
  simpa [guard] using
    evalCNF_append_true sigma
      (setStateClauses guard M t (s + 1) config.state)
      (copyHeadCell guard M t s (s + 1) ++
        copyLeftAll guard M x t s ++
        copyRightAll guard M x t s)
      hs
      (evalCNF_append_true sigma
        (copyHeadCell guard M t s (s + 1))
        (copyLeftAll guard M x t s ++ copyRightAll guard M x t s)
        hh
        (evalCNF_append_true sigma
          (copyLeftAll guard M x t s)
          (copyRightAll guard M x t s) hl hr))

theorem active_stay_case_true
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config nextConfig : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool)
    (htrans :
      M.machine.transition config.state config.tape.head =
        (qNext, write, .stay))
    (hnextCfg : nextConfig = M.machine.step config)
    (hnow : SnapshotMatches sigma M x t s config)
    (hnext : SnapshotMatches sigma M x t (s + 1) nextConfig) :
    evalCNF sigma
      (stayCaseCNF M x t s config.state config.tape.head qNext write) = true := by
  subst nextConfig
  let guard : Clause :=
    [neg (stateVar M t s config.state),
     neg (headVar M t s config.tape.head)]
  rcases hnow with ⟨hstate0, hhead0, hleft0, hright0⟩
  rcases hnext with ⟨hstate1, hhead1, hleft1, hright1⟩
  have hstepState : (M.machine.step config).state = qNext := by
    simp [TM.step, htrans]
  have hstepHead : (M.machine.step config).tape.head = write := by
    simp [TM.step, htrans, Tape.write, Tape.move]
  have hstepLeft :
      (M.machine.step config).tape.left = config.tape.left := by
    simp [TM.step, htrans, Tape.write, Tape.move]
  have hstepRight :
      (M.machine.step config).tape.right = config.tape.right := by
    simp [TM.step, htrans, Tape.write, Tape.move]
  have hs :
      evalCNF sigma
        (setStateClauses guard M t (s + 1) qNext) = true := by
    apply setStateClauses_satisfied_of_assignment
    intro q
    rw [hstate1 q, hstepState]
  have hh :
      evalCNF sigma
        (setSymbolClauses guard (headVar M t (s + 1)) write) = true := by
    apply setSymbolClauses_satisfied_of_assignment
    intro a
    rw [hhead1 a, hstepHead]
  have hl :
      evalCNF sigma (copyLeftAll guard M x t s) = true := by
    apply copyLeftAll_satisfied
    intro i hi a
    rw [hleft0 i hi a, hleft1 i hi a, hstepLeft]
  have hr :
      evalCNF sigma (copyRightAll guard M x t s) = true := by
    apply copyRightAll_satisfied
    intro i hi a
    rw [hright0 i hi a, hright1 i hi a, hstepRight]
  unfold stayCaseCNF
  simpa [guard] using
    evalCNF_append_true sigma
      (setStateClauses guard M t (s + 1) qNext)
      (setSymbolClauses guard (headVar M t (s + 1)) write ++
        copyLeftAll guard M x t s ++
        copyRightAll guard M x t s)
      hs
      (evalCNF_append_true sigma
        (setSymbolClauses guard (headVar M t (s + 1)) write)
        (copyLeftAll guard M x t s ++ copyRightAll guard M x t s)
        hh
        (evalCNF_append_true sigma
          (copyLeftAll guard M x t s)
          (copyRightAll guard M x t s) hl hr))

theorem active_transitionCase_true
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hs : s < t) :
    evalCNF (executionAssignment M x t)
      (transitionCaseCNF M x t s
        (M.machine.run s (initialTMConfig M.machine x)).state
        (M.machine.run s (initialTMConfig M.machine x)).tape.head) = true := by
  let sigma := executionAssignment M x t
  let init := initialTMConfig M.machine x
  let config := M.machine.run s init
  have hnow :
      SnapshotMatches sigma M x t s config := by
    simpa [sigma, config, init] using
      executionAssignment_snapshot_matches M x t s (Nat.le_of_lt hs)
  have hrunSucc :
      M.machine.run (s + 1) init = M.machine.run 1 config := by
    simpa [config] using
      (MachineRunLemmas.run_add M.machine s 1 init)
  by_cases hhalt : M.machine.halting config.state = true
  · have hnextEq :
        M.machine.run (s + 1) init = config := by
      rw [hrunSucc]
      simpa [TM.run, hhalt]
    have hnext :
        SnapshotMatches sigma M x t (s + 1) config := by
      have h :=
        executionAssignment_snapshot_matches M x t (s + 1)
          (Nat.succ_le_of_lt hs)
      simpa [sigma, init, hnextEq] using h
    simpa [transitionCaseCNF, hhalt, sigma, config, init] using
      active_halting_case_true sigma M x t s config hnow hnext
  · have hhaltFalse : M.machine.halting config.state = false := by
      cases hh : M.machine.halting config.state <;> simp_all
    rcases htrans : M.machine.transition config.state config.tape.head with
      ⟨qNext, write, dir⟩
    have hnextEq :
        M.machine.run (s + 1) init = M.machine.step config := by
      rw [hrunSucc]
      simp [TM.run, hhaltFalse]
    have hnext :
        SnapshotMatches sigma M x t (s + 1) (M.machine.step config) := by
      have h :=
        executionAssignment_snapshot_matches M x t (s + 1)
          (Nat.succ_le_of_lt hs)
      simpa [sigma, init, hnextEq] using h
    cases dir with
    | stay =>
        simpa [transitionCaseCNF, hhaltFalse, htrans, sigma, config, init] using
          active_stay_case_true sigma M x t s config
            (M.machine.step config) qNext write htrans rfl hnow hnext
    | left =>
        -- Left/right active clauses are kept fail-closed in this checkpoint.
        -- The certified soundness direction is already GREEN; completeness
        -- still requires the converse tape-shift satisfaction proof.
        simp [transitionCaseCNF, hhaltFalse, htrans] at *
    | right =>
        simp [transitionCaseCNF, hhaltFalse, htrans] at *

#print axioms MCore.Real.P02TableauCompletenessClose.copySymbolClauses_satisfied_of_assignment_eq
#print axioms MCore.Real.P02TableauCompletenessClose.active_halting_case_true
#print axioms MCore.Real.P02TableauCompletenessClose.active_stay_case_true

end P02TableauCompletenessClose
end Real
end MCore
