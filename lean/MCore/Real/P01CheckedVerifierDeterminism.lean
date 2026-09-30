import MCore.Real.P01CheckedVerifierFiniteState
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01CheckedVerifierDeterminism

open P01NTMRunLaws
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierFiniteState

/-- The checked verifier is operationally deterministic at the transition
table: every control/head-symbol pair has at most one outgoing move.

This is a finite statement because the control alphabet and Option Bool are
finite.  It is checked by the kernel after native reduction; no semantic
endpoint is used. -/
theorem checkedVerifier_transition_length_le_one :
    ∀ (q : CheckedVerifierState) (symbol : Option Bool),
      (checkedVerifierMachine.transition q symbol).length ≤ 1 := by
  native_decide

/-- Hence every concrete configuration has at most one successor. -/
theorem checkedVerifier_successors_length_le_one
    (c : Configuration CheckedVerifierState (Option Bool)) :
    (checkedVerifierMachine.successors c).length ≤ 1 := by
  rcases c with ⟨q, tape⟩
  simpa [NTM.successors] using
    checkedVerifier_transition_length_le_one q tape.head

/-- Operational determinism propagates to every finite run from a singleton
configuration. -/
theorem checkedVerifier_runBranches_length_le_one :
    ∀ (n : Nat) (c : Configuration CheckedVerifierState (Option Bool)),
      (checkedVerifierMachine.runBranches n [c]).length ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro c
      simp [NTM.runBranches]
  | succ n ih =>
      intro c
      by_cases hh : Halted checkedVerifierMachine c
      · rw [runBranches_singleton_halted checkedVerifierMachine (n + 1) c hh]
        simp
      · rw [runBranches_singleton_active checkedVerifierMachine n c hh]
        have hlen := checkedVerifier_successors_length_le_one c
        cases hs : checkedVerifierMachine.successors c with
        | nil =>
            simp [hs, runBranches_nil]
        | cons d ds =>
            cases ds with
            | nil =>
                simpa [hs] using ih d
            | cons e es =>
                simp [hs] at hlen

/-- Reusable singleton principle specialized to the checked verifier. -/
theorem runBranches_eq_singleton_of_mem
    (n : Nat)
    (start terminal :
      Configuration CheckedVerifierState (Option Bool))
    (hmem :
      terminal ∈ checkedVerifierMachine.runBranches n [start]) :
    checkedVerifierMachine.runBranches n [start] = [terminal] := by
  apply P01InputNodeCompositeRun.list_eq_singleton_of_mem_length_le_one
  · exact hmem
  · exact checkedVerifier_runBranches_length_le_one n start

/-- Any terminal reached by the checked verifier at fuel n exhausts the whole
run at that same fuel.  This is the bridge needed later for HaltsWithin. -/
theorem haltsWithin_of_reaches_halted
    (n : Nat)
    (start terminal :
      Configuration CheckedVerifierState (Option Bool))
    (hmem :
      terminal ∈ checkedVerifierMachine.runBranches n [start])
    (hhalt : Halted checkedVerifierMachine terminal) :
    checkedVerifierMachine.HaltsWithin n start := by
  rw [haltsWithin_iff_halted]
  intro z hz
  have heq := runBranches_eq_singleton_of_mem n start terminal hmem
  rw [heq] at hz
  simp only [List.mem_singleton] at hz
  subst z
  exact hhalt

#print axioms MCore.Real.P01CheckedVerifierDeterminism.checkedVerifier_transition_length_le_one
#print axioms MCore.Real.P01CheckedVerifierDeterminism.checkedVerifier_successors_length_le_one
#print axioms MCore.Real.P01CheckedVerifierDeterminism.checkedVerifier_runBranches_length_le_one
#print axioms MCore.Real.P01CheckedVerifierDeterminism.haltsWithin_of_reaches_halted

end P01CheckedVerifierDeterminism
end Real
end MCore
