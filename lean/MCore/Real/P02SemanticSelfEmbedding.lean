import MCore.Real.P02DiagonalFrontier

namespace MCore
namespace Real
namespace P02SemanticSelfEmbedding

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02TerminalFrontier
open P02DiagonalFrontier

/-- Exact semantic payload required by T5.A2.  This packages a bitstring
construction together with canonical validity and the semantic flip law.
No existence claim is made here. -/
structure SemanticSelfEmbedder where
  bits : PolyDTMCandidate → BitString
  valid :
    ∀ M : PolyDTMCandidate,
      CanonicalSATValid (bits M)
  flips :
    ∀ M : PolyDTMCandidate,
      SATBits circuitBitEncoding (bits M) ↔
        ¬ AcceptsAtDeclaredBound M (bits M)

def SemanticSelfEmbeddingGap : Prop :=
  Nonempty SemanticSelfEmbedder

def SemanticSelfEmbedder.toDiagonalFamily
    (S : SemanticSelfEmbedder) :
    DiagonalFamily where
  witness := fun M =>
    { bits := S.bits M
      valid := S.valid M
      flips := S.flips M }

def DiagonalFamily.toSemanticSelfEmbedder
    (D : DiagonalFamily) :
    SemanticSelfEmbedder where
  bits := fun M => (D.witness M).bits
  valid := fun M => (D.witness M).valid
  flips := fun M => (D.witness M).flips

theorem semantic_self_embedding_gap_iff_diagonal_fixed_point_gap :
    SemanticSelfEmbeddingGap ↔ DiagonalFixedPointGap := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.toDiagonalFamily⟩
  · rintro ⟨D⟩
    exact ⟨D.toSemanticSelfEmbedder⟩

theorem semantic_self_embedding_closes_p02
    (h : SemanticSelfEmbeddingGap) :
    P02Target := by
  exact diagonal_fixed_point_gap_closes_p02
    ((semantic_self_embedding_gap_iff_diagonal_fixed_point_gap).mp h)

#print axioms MCore.Real.P02SemanticSelfEmbedding.semantic_self_embedding_gap_iff_diagonal_fixed_point_gap
#print axioms MCore.Real.P02SemanticSelfEmbedding.semantic_self_embedding_closes_p02

end P02SemanticSelfEmbedding
end Real
end MCore
