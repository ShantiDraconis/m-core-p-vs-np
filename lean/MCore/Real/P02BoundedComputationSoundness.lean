import MCore.Real.P02BoundedComputationLogic
import MCore.Real.P02BoundedComputationTape

namespace MCore
namespace Real
namespace P02BoundedComputationSoundness

open CircuitK1
open CanonicalFinalProof
open P02BoundedComputationEncoding
open P02BoundedComputationLogic

def SnapshotMatches
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool)) : Prop :=
  (∀ q : Fin (M.stateCount + 1),
      sigma (stateVar M t s q) = decide (q = config.state)) ∧
  (∀ a : Option Bool,
      sigma (headVar M t s a) = decide (a = config.tape.head)) ∧
  (∀ i : Nat, i < radius x t →
      ∀ a : Option Bool,
        sigma (leftVar M x t s i a) =
          decide (a = config.tape.left.getD i M.machine.blank)) ∧
  (∀ i : Nat, i < radius x t →
      ∀ a : Option Bool,
        sigma (rightVar M x t s i a) =
          decide (a = config.tape.right.getD i M.machine.blank))

theorem initialCNF_sound
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat)
    (hinit : evalCNF sigma (initialCNF M x t) = true) :
    SnapshotMatches sigma M x t 0 (initialTMConfig M.machine x) := by
  have hstate :
      evalCNF sigma
        (setStateClauses [] M t 0 M.machine.initial) = true := by
    apply evalCNF_subset_true sigma _ (initialCNF M x t) hinit
    intro c hc
    simp [initialCNF, hc]
  have hhead :
      evalCNF sigma
        (setSymbolClauses [] (headVar M t 0) (inputTape x).head) = true := by
    apply evalCNF_subset_true sigma _ (initialCNF M x t) hinit
    intro c hc
    simp [initialCNF, hc]
  unfold SnapshotMatches
  dsimp [initialTMConfig]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q
    exact setStateClauses_forces
      sigma [] M t 0 M.machine.initial q rfl hstate
  · intro a
    exact setSymbolClauses_forces
      sigma [] (headVar M t 0) (inputTape x).head a rfl hhead
  · intro i hi a
    let target := (inputTape x).left.getD i M.machine.blank
    have hcell :
        evalCNF sigma
          (setLeftCell [] M x t 0 i target) = true := by
      apply evalCNF_subset_true sigma _ (initialCNF M x t) hinit
      intro c hc
      simp only [initialCNF, List.mem_append, List.mem_flatMap,
        List.mem_range]
      exact Or.inl (Or.inr
        ⟨i, hi, by simpa [target] using hc⟩)
    exact setSymbolClauses_forces
      sigma [] (leftVar M x t 0 i) target a rfl hcell
  · intro i hi a
    let target := (inputTape x).right.getD i M.machine.blank
    have hcell :
        evalCNF sigma
          (setRightCell [] M x t 0 i target) = true := by
      apply evalCNF_subset_true sigma _ (initialCNF M x t) hinit
      intro c hc
      simp only [initialCNF, List.mem_append, List.mem_flatMap,
        List.mem_range]
      exact Or.inr
        ⟨i, hi, by simpa [target] using hc⟩
    exact setSymbolClauses_forces
      sigma [] (rightVar M x t 0 i) target a rfl hcell

theorem snapshot_transition_guard_false
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (hmatch : SnapshotMatches sigma M x t s config) :
    evalClause sigma
      [neg (stateVar M t s config.state),
       neg (headVar M t s config.tape.head)] = false := by
  rcases hmatch with ⟨hstate, hhead, _, _⟩
  have hs :
      sigma (stateVar M t s config.state) = true := by
    simpa using hstate config.state
  have hh :
      sigma (headVar M t s config.tape.head) = true := by
    simpa using hhead config.tape.head
  simp [evalClause, evalLiteral, neg, hs, hh]


theorem boundedExecTableau_initial_sound
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat)
    (h : evalCNF sigma (boundedExecTableauCNF M x t) = true) :
    SnapshotMatches sigma M x t 0 (initialTMConfig M.machine x) := by
  apply initialCNF_sound
  apply evalCNF_subset_true sigma _ (boundedExecTableauCNF M x t) h
  intro c hc
  simp [boundedExecTableauCNF, hc]


theorem snapshot_state_true
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (hmatch : SnapshotMatches sigma M x t s config) :
    sigma (stateVar M t s config.state) = true := by
  simpa using hmatch.1 config.state

theorem snapshot_head_true
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (hmatch : SnapshotMatches sigma M x t s config) :
    sigma (headVar M t s config.tape.head) = true := by
  simpa using hmatch.2.1 config.tape.head


#print axioms MCore.Real.P02BoundedComputationSoundness.snapshot_transition_guard_false
#print axioms MCore.Real.P02BoundedComputationSoundness.snapshot_state_true
#print axioms MCore.Real.P02BoundedComputationSoundness.snapshot_head_true
#print axioms MCore.Real.P02BoundedComputationSoundness.boundedExecTableau_initial_sound


#print axioms MCore.Real.P02BoundedComputationSoundness.initialCNF_sound

end P02BoundedComputationSoundness
end Real
end MCore
