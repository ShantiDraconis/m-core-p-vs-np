import MCore.Real.P02BoundedComputationLogic

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
      have hiMem : i ∈ List.range (radius x t) := by
        simpa using hi
      have hflat :
          c ∈ (List.range (radius x t)).flatMap
            (fun j =>
              setLeftCell [] M x t 0 j
                ((inputTape x).left.getD j M.machine.blank)) := by
        exact List.mem_flatMap_of_mem hiMem hc
      simp [initialCNF, hflat]
    exact setSymbolClauses_forces
      sigma [] (leftVar M x t 0 i) target a rfl hcell
  · intro i hi a
    let target := (inputTape x).right.getD i M.machine.blank
    have hcell :
        evalCNF sigma
          (setRightCell [] M x t 0 i target) = true := by
      apply evalCNF_subset_true sigma _ (initialCNF M x t) hinit
      intro c hc
      have hiMem : i ∈ List.range (radius x t) := by
        simpa using hi
      have hflat :
          c ∈ (List.range (radius x t)).flatMap
            (fun j =>
              setRightCell [] M x t 0 j
                ((inputTape x).right.getD j M.machine.blank)) := by
        exact List.mem_flatMap_of_mem hiMem hc
      simp [initialCNF, hflat]
    exact setSymbolClauses_forces
      sigma [] (rightVar M x t 0 i) target a rfl hcell

#print axioms MCore.Real.P02BoundedComputationSoundness.initialCNF_sound

end P02BoundedComputationSoundness
end Real
end MCore
