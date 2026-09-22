import MCore.Real.P02BoundedComputationSoundness

namespace MCore
namespace Real
namespace P02BoundedComputationClose

open CircuitK1
open CanonicalFinalProof
open P02BoundedComputationEncoding
open P02BoundedComputationSoundness
open P02BoundedComputationLogic

structure TransitionSoundnessCertificate where
  step :
    ∀ (sigma : Assignment) (M : PolyDTMCandidate) (x : BitString)
      (t s : Nat), s < t →
      evalCNF sigma (boundedExecTableauCNF M x t) = true →
      SnapshotMatches sigma M x t s
        (M.machine.run s (initialTMConfig M.machine x)) →
      SnapshotMatches sigma M x t (s + 1)
        (M.machine.run (s + 1) (initialTMConfig M.machine x))

structure TableauCompletenessCertificate where
  assignment :
    ∀ (M : PolyDTMCandidate) (x : BitString) (t : Nat),
      AcceptsAtFuel M x t → Assignment
  satisfies :
    ∀ (M : PolyDTMCandidate) (x : BitString) (t : Nat)
      (hacc : AcceptsAtFuel M x t),
      evalCNF (assignment M x t hacc)
        (boundedExecTableauCNF M x t) = true


theorem transitionCaseCNF_mem_transitionsCNF
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hs : s < t)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (c : Clause)
    (hc : c ∈ transitionCaseCNF M x t s q a) :
    c ∈ transitionsCNF M x t := by
  unfold transitionsCNF
  simp only [List.mem_flatMap, List.mem_range]
  refine ⟨s, hs, ?_⟩
  unfold transitionStepCNF
  simp only [List.mem_flatten, List.mem_ofFn, List.mem_flatMap]
  refine ⟨alphabet.flatMap fun a' => transitionCaseCNF M x t s q a', ?_, ?_⟩
  · exact ⟨q, rfl⟩
  · refine ⟨a, ?_, hc⟩
    cases a with
    | none => simp [alphabet]
    | some b =>
        cases b <;> simp [alphabet]

theorem active_transition_case_true
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hs : s < t)
    (htableau : evalCNF sigma (boundedExecTableauCNF M x t) = true)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool)) :
    evalCNF sigma
      (transitionCaseCNF M x t s config.state config.tape.head) = true := by
  apply evalCNF_subset_true sigma
    (transitionCaseCNF M x t s config.state config.tape.head)
    (boundedExecTableauCNF M x t)
    htableau
  intro c hc
  simp only [boundedExecTableauCNF, List.mem_append]
  exact Or.inr (Or.inl
    (transitionCaseCNF_mem_transitionsCNF M x t s hs
      config.state config.tape.head c hc))

theorem snapshots_all
    (S : TransitionSoundnessCertificate)
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hs : s ≤ t)
    (htableau : evalCNF sigma (boundedExecTableauCNF M x t) = true) :
    SnapshotMatches sigma M x t s
      (M.machine.run s (initialTMConfig M.machine x)) := by
  induction s with
  | zero =>
      simpa [TM.run] using
        boundedExecTableau_initial_sound sigma M x t htableau
  | succ s ih =>
      have hslt : s < t := Nat.lt_of_succ_le hs
      exact S.step sigma M x t s hslt htableau
        (ih (Nat.le_trans (Nat.le_succ s) hs))

theorem tableau_sound
    (S : TransitionSoundnessCertificate)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    SATLanguage (boundedExecCircuit M x t) →
      AcceptsAtFuel M x t := by
  intro hsat
  rcases (satLanguage_cnfCircuit_iff
    (boundedExecTableauCNF M x t)).mp hsat with ⟨sigma, htableau⟩
  have hmatch :=
    snapshots_all S sigma M x t t (Nat.le_refl t) htableau
  exact boundedExecTableau_final_acceptance_sound
    sigma M x t
    (M.machine.run t (initialTMConfig M.machine x))
    hmatch htableau

theorem tableau_complete
    (C : TableauCompletenessCertificate)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    AcceptsAtFuel M x t →
      SATLanguage (boundedExecCircuit M x t) := by
  intro hacc
  apply (satLanguage_cnfCircuit_iff
    (boundedExecTableauCNF M x t)).mpr
  exact ⟨C.assignment M x t hacc, C.satisfies M x t hacc⟩

theorem certificates_close_boundedExecCorrectness
    (S : TransitionSoundnessCertificate)
    (C : TableauCompletenessCertificate) :
    BoundedExecCorrectness := by
  intro M x t
  constructor
  · exact tableau_sound S M x t
  · exact tableau_complete C M x t

def TransitionSoundnessGap : Prop :=
  Nonempty TransitionSoundnessCertificate

def TableauCompletenessGap : Prop :=
  Nonempty TableauCompletenessCertificate

#print axioms MCore.Real.P02BoundedComputationClose.transitionCaseCNF_mem_transitionsCNF
#print axioms MCore.Real.P02BoundedComputationClose.active_transition_case_true
#print axioms MCore.Real.P02BoundedComputationClose.snapshots_all
#print axioms MCore.Real.P02BoundedComputationClose.tableau_sound
#print axioms MCore.Real.P02BoundedComputationClose.tableau_complete
#print axioms MCore.Real.P02BoundedComputationClose.certificates_close_boundedExecCorrectness

end P02BoundedComputationClose
end Real
end MCore
