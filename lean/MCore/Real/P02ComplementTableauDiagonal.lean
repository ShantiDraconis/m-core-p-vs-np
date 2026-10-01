import MCore.Real.P02SemanticFlipCore
import MCore.Real.P02TableauCompletenessClose

namespace MCore
namespace Real
namespace P02ComplementTableauDiagonal

open CanonicalFinalProof
open P02UniversalFailureMinCut
open P02TotalCandidateSemanticCore
open P02SemanticFlipCore
open P02BoundedComputationEncoding
open P02TableauCompletenessClose

abbrev SATTarget : BitLanguage :=
  P02UniversalFailureMinCut.CanonicalSAT

/-- Same deterministic machine and polynomial clock, with only the final
acceptance bit complemented. -/
def complementCandidate
    (M : PolyDTMCandidate) :
    PolyDTMCandidate :=
  { stateCount := M.stateCount
    machine := M.machine
    blank_none := M.blank_none
    accepting := fun q => ! M.accepting q
    timeBound := M.timeBound
    time_poly := M.time_poly }

@[simp] theorem complementCandidate_machine
    (M : PolyDTMCandidate) :
    (complementCandidate M).machine = M.machine := rfl

@[simp] theorem complementCandidate_timeBound
    (M : PolyDTMCandidate) :
    (complementCandidate M).timeBound = M.timeBound := rfl

theorem complement_acceptsAtFuel_iff_not
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    AcceptsAtFuel (complementCandidate M) x t ↔
      ¬ M.accepting
          (M.machine.run t
            (initialTMConfig M.machine x)).state = true := by
  unfold AcceptsAtFuel complementCandidate
  change
    (! M.accepting
        (M.machine.run t
          (initialTMConfig M.machine x)).state = true) ↔
      ¬ M.accepting
          (M.machine.run t
            (initialTMConfig M.machine x)).state = true
  cases h :
      M.accepting
        (M.machine.run t
          (initialTMConfig M.machine x)).state <;>
    simp [h]

/-- Canonical SAT instance encoding the bounded execution of the complemented
candidate on x at M's own declared clock. -/
def diagonalBits
    (M : PolyDTMCandidate)
    (x : BitString) : BitString :=
  boundedExecBits
    (complementCandidate M) x
    (M.timeBound x.length)

theorem diagonalBits_valid
    (M : PolyDTMCandidate)
    (x : BitString) :
    ∃ phi : CircuitK1.Circuit,
      CanonicalCircuitBits.decodeCircuit (diagonalBits M x) = some phi := by
  exact boundedExecBits_valid
    (complementCandidate M) x
    (M.timeBound x.length)

/-- The recovered tableau theorem gives the exact semantic diagonal compiler:
SAT of diagonalBits(M,x) is the complement of M's declared answer on x. -/
theorem diagonalBits_sat_iff_not_declaredAccepts
    (M : PolyDTMCandidate)
    (x : BitString) :
    SATTarget (diagonalBits M x) ↔
      ¬ DeclaredAccepts M x := by
  rw [show SATTarget (diagonalBits M x) =
      SATBits CanonicalCircuitBits.circuitBitEncoding (diagonalBits M x) by rfl]
  rw [boundedExecCorrectness_to_bits
      boundedExecCorrectness_closed
      (complementCandidate M) x
      (M.timeBound x.length)]
  exact complement_acceptsAtFuel_iff_not
    M x (M.timeBound x.length)

/-- The extensional same-answer condition is strictly weaker than requiring
literal bitstring fixed points. -/
def AcceptanceAligned
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  DeclaredAccepts M (diagonalBits M x) ↔
    DeclaredAccepts M x

theorem semanticFlip_diagonalBits_of_alignment
    (M : PolyDTMCandidate)
    (x : BitString)
    (hAlign : AcceptanceAligned M x) :
    SemanticFlip M (diagonalBits M x) := by
  unfold SemanticFlip
  rw [diagonalBits_sat_iff_not_declaredAccepts M x]
  constructor
  · intro hNotX hDiag
    exact hNotX (hAlign.mp hDiag)
  · intro hNotDiag hX
    exact hNotDiag (hAlign.mpr hX)

/-- Exact post-tableau open core: for every candidate already known to respect
its declared clock, find one input whose answer is preserved by diagonalBits.
No literal x = diagonalBits M x is required. -/
def TotalCandidateAcceptanceAlignmentCore : Prop :=
  ∀ M : PolyDTMCandidate,
    DeclaredClockTotal M →
      ∃ x : BitString, AcceptanceAligned M x

theorem alignment_core_implies_semantic_flip_core
    (H : TotalCandidateAcceptanceAlignmentCore) :
    TotalCandidateSemanticFlipCore := by
  intro M hTotal
  rcases H M hTotal with ⟨x, hAlign⟩
  exact ⟨diagonalBits M x,
    semanticFlip_diagonalBits_of_alignment M x hAlign⟩

theorem alignment_core_implies_universal_failure
    (H : TotalCandidateAcceptanceAlignmentCore) :
    UniversalFailure SATTarget :=
  (semantic_flip_core_iff_universal_failure).mp
    (alignment_core_implies_semantic_flip_core H)

theorem alignment_core_closes_internal_endpoint
    (H : TotalCandidateAcceptanceAlignmentCore) :
    PneqNP :=
  semantic_flip_core_closes_internal_endpoint
    (alignment_core_implies_semantic_flip_core H)

#print axioms MCore.Real.P02ComplementTableauDiagonal.complement_acceptsAtFuel_iff_not
#print axioms MCore.Real.P02ComplementTableauDiagonal.diagonalBits_sat_iff_not_declaredAccepts
#print axioms MCore.Real.P02ComplementTableauDiagonal.semanticFlip_diagonalBits_of_alignment
#print axioms MCore.Real.P02ComplementTableauDiagonal.alignment_core_implies_semantic_flip_core
#print axioms MCore.Real.P02ComplementTableauDiagonal.alignment_core_implies_universal_failure
#print axioms MCore.Real.P02ComplementTableauDiagonal.alignment_core_closes_internal_endpoint

end P02ComplementTableauDiagonal
end Real
end MCore
