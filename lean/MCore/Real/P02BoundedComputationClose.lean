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
  apply List.mem_flatMap.mpr
  refine ⟨s, by simpa using hs, ?_⟩
  unfold transitionStepCNF
  apply List.mem_flatten.mpr
  let block : List Clause :=
    alphabet.flatMap fun a' => transitionCaseCNF M x t s q a'
  refine ⟨block, ?_, ?_⟩
  · unfold block
    exact List.mem_ofFn.mpr ⟨q, rfl⟩
  · unfold block
    apply List.mem_flatMap.mpr
    refine ⟨a, ?_, hc⟩
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
  exact Or.inl (Or.inr
    (transitionCaseCNF_mem_transitionsCNF M x t s hs
      config.state config.tape.head c hc))


theorem stay_case_preserves_snapshot
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool)
    (hhalt : M.machine.halting config.state = false)
    (htrans :
      M.machine.transition config.state config.tape.head =
        (qNext, write, .stay))
    (hmatch : SnapshotMatches sigma M x t s config)
    (hcase :
      evalCNF sigma
        (transitionCaseCNF M x t s config.state config.tape.head) = true) :
    SnapshotMatches sigma M x t (s + 1) (M.machine.step config) := by
  let guard : Clause :=
    [neg (stateVar M t s config.state),
     neg (headVar M t s config.tape.head)]
  have hguard : evalClause sigma guard = false := by
    simpa [guard] using
      snapshot_transition_guard_false sigma M x t s config hmatch
  have hstay :
      evalCNF sigma
        (stayCaseCNF M x t s config.state config.tape.head qNext write) = true := by
    simpa [transitionCaseCNF, hhalt, htrans] using hcase
  have hstate :
      evalCNF sigma
        (setStateClauses guard M t (s + 1) qNext) = true := by
    apply evalCNF_subset_true sigma _ _ hstay
    intro cl hcl
    simp [stayCaseCNF, guard, hcl]
  have hhead :
      evalCNF sigma
        (setSymbolClauses guard (headVar M t (s + 1)) write) = true := by
    apply evalCNF_subset_true sigma _ _ hstay
    intro cl hcl
    simp [stayCaseCNF, guard, hcl]
  have hleft :
      evalCNF sigma (copyLeftAll guard M x t s) = true := by
    apply evalCNF_subset_true sigma _ _ hstay
    intro cl hcl
    simp [stayCaseCNF, guard, hcl]
  have hright :
      evalCNF sigma (copyRightAll guard M x t s) = true := by
    apply evalCNF_subset_true sigma _ _ hstay
    intro cl hcl
    simp [stayCaseCNF, guard, hcl]
  rcases hmatch with ⟨hstateOld, hheadOld, hleftOld, hrightOld⟩
  unfold SnapshotMatches
  constructor
  · intro q
    have hf :=
      setStateClauses_forces sigma guard M t (s + 1) qNext q
        hguard hstate
    simpa [TM.step, htrans, Tape.write, Tape.move] using hf
  constructor
  · intro a
    have hf :=
      setSymbolClauses_forces sigma guard (headVar M t (s + 1))
        write a hguard hhead
    simpa [TM.step, htrans, Tape.write, Tape.move] using hf
  constructor
  · intro i hi a
    have hcell :
        evalCNF sigma
          (copyLeftCell guard M x t s i (s + 1) i) = true := by
      apply evalCNF_subset_true sigma _ _ hleft
      intro cl hcl
      unfold copyLeftAll
      simp only [List.mem_flatMap, List.mem_range]
      exact ⟨i, hi, hcl⟩
    have hf :=
      copySymbolClauses_forces sigma guard
        (leftVar M x t s i) (leftVar M x t (s + 1) i)
        a hguard hcell
    rw [hf, hleftOld i hi a]
    simp [TM.step, htrans, Tape.write, Tape.move]
  · intro i hi a
    have hcell :
        evalCNF sigma
          (copyRightCell guard M x t s i (s + 1) i) = true := by
      apply evalCNF_subset_true sigma _ _ hright
      intro cl hcl
      unfold copyRightAll
      simp only [List.mem_flatMap, List.mem_range]
      exact ⟨i, hi, hcl⟩
    have hf :=
      copySymbolClauses_forces sigma guard
        (rightVar M x t s i) (rightVar M x t (s + 1) i)
        a hguard hcell
    rw [hf, hrightOld i hi a]
    simp [TM.step, htrans, Tape.write, Tape.move]

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
#print axioms MCore.Real.P02BoundedComputationClose.stay_case_preserves_snapshot
#print axioms MCore.Real.P02BoundedComputationClose.snapshots_all
#print axioms MCore.Real.P02BoundedComputationClose.tableau_sound
#print axioms MCore.Real.P02BoundedComputationClose.tableau_complete
#print axioms MCore.Real.P02BoundedComputationClose.certificates_close_boundedExecCorrectness

end P02BoundedComputationClose
end Real
end MCore
