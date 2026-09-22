import MCore.Real.P02G21G22Attack
import MCore.Real.P02SemanticSelfEmbedding

namespace MCore
namespace Real
namespace P02UniversalFailureAlgebra

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02G21G22Attack
open P02SemanticSelfEmbedding

/-- Candidate halts within its own declared polynomial clock on one input. -/
def DeclaredHalts
    (M : PolyDTMCandidate) (x : BitString) : Prop :=
  M.machine.HaltsWithin
    (M.timeBound x.length)
    (initialTMConfig M.machine x)

/-- Candidate's declared acceptance bit agrees with canonical SAT on one input. -/
def DeclaredSATMatch
    (M : PolyDTMCandidate) (x : BitString) : Prop :=
  AcceptsAtDeclaredBound M x ↔ SATBits circuitBitEncoding x

/-- Semantic disagreement, split into the two Boolean directions. -/
def SemanticMismatch
    (M : PolyDTMCandidate) (x : BitString) : Prop :=
  (AcceptsAtDeclaredBound M x ∧ ¬ SATBits circuitBitEncoding x) ∨
  (¬ AcceptsAtDeclaredBound M x ∧ SATBits circuitBitEncoding x)

/-- Totality at the candidate's own declared clock. -/
def DeclaredClockTotal (M : PolyDTMCandidate) : Prop :=
  ∀ x : BitString, DeclaredHalts M x

/-- Semantic SAT correctness at the candidate's own declared clock. -/
def DeclaredSATCorrect (M : PolyDTMCandidate) : Prop :=
  ∀ x : BitString, DeclaredSATMatch M x

theorem correctAt_iff_declared_halts_and_match
    (M : PolyDTMCandidate) (x : BitString) :
    M.CorrectAt (SATBits circuitBitEncoding) x ↔
      DeclaredHalts M x ∧ DeclaredSATMatch M x := by
  rfl

theorem not_correctAt_iff_clock_or_match_failure
    (M : PolyDTMCandidate) (x : BitString) :
    ¬ M.CorrectAt (SATBits circuitBitEncoding) x ↔
      ¬ DeclaredHalts M x ∨ ¬ DeclaredSATMatch M x := by
  rw [correctAt_iff_declared_halts_and_match]
  tauto

theorem not_declaredSATMatch_iff_semanticMismatch
    (M : PolyDTMCandidate) (x : BitString) :
    ¬ DeclaredSATMatch M x ↔ SemanticMismatch M x := by
  unfold DeclaredSATMatch SemanticMismatch
  tauto

theorem not_correctAt_iff_clock_or_semantic_mismatch
    (M : PolyDTMCandidate) (x : BitString) :
    ¬ M.CorrectAt (SATBits circuitBitEncoding) x ↔
      ¬ DeclaredHalts M x ∨ SemanticMismatch M x := by
  rw [not_correctAt_iff_clock_or_match_failure,
      not_declaredSATMatch_iff_semanticMismatch]

/-- Pointwise G21 in its exact normalized two-mode form. -/
def ClockOrSemanticFailure : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ x : BitString,
      ¬ DeclaredHalts M x ∨ SemanticMismatch M x

theorem g21_iff_clock_or_semantic_failure :
    G21Pointwise ↔ ClockOrSemanticFailure := by
  constructor
  · intro h M
    rcases h M with ⟨x, hx⟩
    exact ⟨x, (not_correctAt_iff_clock_or_semantic_mismatch M x).mp hx⟩
  · intro h M
    rcases h M with ⟨x, hx⟩
    exact ⟨x, (not_correctAt_iff_clock_or_semantic_mismatch M x).mpr hx⟩

theorem not_declaredClockTotal_iff_exists_clock_failure
    (M : PolyDTMCandidate) :
    ¬ DeclaredClockTotal M ↔
      ∃ x : BitString, ¬ DeclaredHalts M x := by
  unfold DeclaredClockTotal
  push_neg
  rfl

theorem total_candidate_failure_iff_exists_semanticMismatch
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    (∃ x : BitString,
      ¬ M.CorrectAt (SATBits circuitBitEncoding) x) ↔
    (∃ x : BitString, SemanticMismatch M x) := by
  constructor
  · rintro ⟨x, hx⟩
    have hsplit :=
      (not_correctAt_iff_clock_or_semantic_mismatch M x).mp hx
    rcases hsplit with hclock | hmismatch
    · exact False.elim (hclock (hTotal x))
    · exact ⟨x, hmismatch⟩
  · rintro ⟨x, hmismatch⟩
    exact ⟨x,
      (not_correctAt_iff_clock_or_semantic_mismatch M x).mpr
        (Or.inr hmismatch)⟩

/-- Universal G21 reduces exactly to: every candidate either violates its
declared total clock, or has a semantic SAT mismatch. -/
def TotalityOrSemanticCounterexample : Prop :=
  ∀ M : PolyDTMCandidate,
    ¬ DeclaredClockTotal M ∨
      ∃ x : BitString, SemanticMismatch M x

theorem clock_or_semantic_failure_iff_totality_or_semantic :
    ClockOrSemanticFailure ↔ TotalityOrSemanticCounterexample := by
  constructor
  · intro h M
    by_cases hTotal : DeclaredClockTotal M
    · right
      rcases h M with ⟨x, hx⟩
      rcases hx with hclock | hmismatch
      · exact False.elim (hclock (hTotal x))
      · exact ⟨x, hmismatch⟩
    · exact Or.inl hTotal
  · intro h M
    rcases h M with hNotTotal | hMismatch
    · rcases (not_declaredClockTotal_iff_exists_clock_failure M).mp hNotTotal with
        ⟨x, hx⟩
      exact ⟨x, Or.inl hx⟩
    · rcases hMismatch with ⟨x, hx⟩
      exact ⟨x, Or.inr hx⟩

theorem g21_iff_totality_or_semantic_counterexample :
    G21Pointwise ↔ TotalityOrSemanticCounterexample := by
  exact g21_iff_clock_or_semantic_failure.trans
    clock_or_semantic_failure_iff_totality_or_semantic

/-- A semantic self-code witness always supplies the semantic-mismatch branch;
literal string fixed points are unnecessary for this implication. -/
theorem self_embed_witness_gives_semanticMismatch
    (M : PolyDTMCandidate)
    (x : BitString)
    (hflip :
      SATBits circuitBitEncoding x ↔
        ¬ AcceptsAtDeclaredBound M x) :
    SemanticMismatch M x := by
  unfold SemanticMismatch
  by_cases hacc : AcceptsAtDeclaredBound M x
  · left
    refine ⟨hacc, ?_⟩
    intro hsat
    exact (hflip.mp hsat) hacc
  · right
    exact ⟨hacc, hflip.mpr hacc⟩

theorem pointwise_self_embedding_implies_normalized_failure
    (h : PointwiseSemanticSelfEmbedding) :
    TotalityOrSemanticCounterexample := by
  intro M
  right
  rcases h M with ⟨x, _, hflip⟩
  exact ⟨x, self_embed_witness_gives_semanticMismatch M x hflip⟩

theorem totality_or_semantic_closes_p02
    (h : TotalityOrSemanticCounterexample) :
    P02TerminalFrontier.P02Target := by
  apply g21_pointwise_iff_p02_target.mp
  exact g21_iff_totality_or_semantic_counterexample.mpr h

#print axioms MCore.Real.P02UniversalFailureAlgebra.not_correctAt_iff_clock_or_semantic_mismatch
#print axioms MCore.Real.P02UniversalFailureAlgebra.g21_iff_totality_or_semantic_counterexample
#print axioms MCore.Real.P02UniversalFailureAlgebra.self_embed_witness_gives_semanticMismatch
#print axioms MCore.Real.P02UniversalFailureAlgebra.totality_or_semantic_closes_p02

end P02UniversalFailureAlgebra
end Real
end MCore
