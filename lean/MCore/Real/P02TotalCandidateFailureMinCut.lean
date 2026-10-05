import MCore.Real.CanonicalCircuitBits
import MCore.Real.CanonicalSATBoundary
import MCore.Real.FailProofAllGaps

namespace MCore
namespace Real
namespace P02TotalCandidateFailureMinCut

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open FailProofAllGaps

abbrev CanonicalSAT : BitLanguage :=
  SATBits circuitBitEncoding

/-- A candidate is total at exactly the polynomial clock it declares. -/
def DeclaredClockTotal (M : PolyDTMCandidate) : Prop :=
  ∀ x : BitString,
    M.machine.HaltsWithin
      (M.timeBound x.length)
      (initialTMConfig M.machine x)

/-- The only lower-bound content left after timeout failures are discharged:
for every candidate that really halts at its declared clock, produce one input
where its Boolean answer disagrees with canonical SAT. -/
structure TotalSemanticFailureProducer where
  counterexample :
    ∀ (M : PolyDTMCandidate), DeclaredClockTotal M → BitString
  disagrees :
    ∀ (M : PolyDTMCandidate) (hTotal : DeclaredClockTotal M),
      let x := counterexample M hTotal
      ¬ (M.accepting
          (M.machine.run
            (M.timeBound x.length)
            (initialTMConfig M.machine x)).state = true ↔
        CanonicalSAT x)

/-- A total semantic-failure producer gives the full FailureGenerator.
Non-total candidates need no new mathematics: classical witness extraction
selects an input where their declared polynomial clock already fails. -/
noncomputable def TotalSemanticFailureProducer.toFailureGenerator
    (P : TotalSemanticFailureProducer) :
    FailureGenerator CanonicalSAT := by
  classical
  let pick : PolyDTMCandidate → BitString :=
    fun M =>
      if h : DeclaredClockTotal M then
        P.counterexample M h
      else
        Classical.choose (show ∃ x : BitString,
            ¬ M.machine.HaltsWithin
              (M.timeBound x.length)
              (initialTMConfig M.machine x) by
          by_contra hnone
          push_neg at hnone
          exact h hnone)
  refine
    { counterexample := pick
      fails := ?_ }
  intro M
  by_cases hTotal : DeclaredClockTotal M
  · have hPick : pick M = P.counterexample M hTotal := by
      simp [pick, hTotal]
    rw [hPick]
    intro hCorrect
    exact P.disagrees M hTotal hCorrect.2
  · have hex : ∃ x : BitString,
        ¬ M.machine.HaltsWithin
          (M.timeBound x.length)
          (initialTMConfig M.machine x) := by
      by_contra hnone
      push_neg at hnone
      exact hTotal hnone
    have hPick :
        ¬ M.machine.HaltsWithin
          (M.timeBound (pick M).length)
          (initialTMConfig M.machine (pick M)) := by
      simp only [pick, hTotal, dite_false]
      exact Classical.choose_spec hex
    intro hCorrect
    exact hPick hCorrect.1

theorem totalSemanticFailureProducer_implies_universalFailure
    (P : TotalSemanticFailureProducer) :
    UniversalFailure CanonicalSAT :=
  failure_generator_implies_universal_failure P.toFailureGenerator

theorem totalSemanticFailureProducer_closes_internal_endpoint
    (hNP : InNP CanonicalSAT)
    (P : TotalSemanticFailureProducer) :
    PneqNP :=
  target_failure_implies_p_ne_np hNP
    (totalSemanticFailureProducer_implies_universalFailure P)

/-- This is the narrowed material frontier. It contains no not-in-P field,
UniversalFailure field, or endpoint proposition. -/
def TOTAL_SEMANTIC_FAILURE_OPEN_MATH : Prop :=
  Nonempty TotalSemanticFailureProducer

#print axioms MCore.Real.P02TotalCandidateFailureMinCut.TotalSemanticFailureProducer.toFailureGenerator
#print axioms MCore.Real.P02TotalCandidateFailureMinCut.totalSemanticFailureProducer_implies_universalFailure
#print axioms MCore.Real.P02TotalCandidateFailureMinCut.totalSemanticFailureProducer_closes_internal_endpoint

end P02TotalCandidateFailureMinCut
end Real
end MCore
