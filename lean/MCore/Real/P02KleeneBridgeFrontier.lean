import MCore.Real.P02SemanticSelfEmbedding

namespace MCore
namespace Real
namespace P02KleeneBridgeFrontier

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02SemanticSelfEmbedding

/-- Exact bridge required to reuse an external recursion theorem safely.
It must encode every hardened deterministic candidate as data and decode enough
structure to build a canonical SAT bitstring witnessing semantic self-reference.
No inhabitant is asserted here. -/
structure CandidateCodingBridge where
  code : PolyDTMCandidate -> Nat
  selfBits : PolyDTMCandidate -> BitString
  valid :
    forall M : PolyDTMCandidate,
      P02DiagonalFrontier.CanonicalSATValid (selfBits M)
  flips :
    forall M : PolyDTMCandidate,
      SATBits circuitBitEncoding (selfBits M) <->
        ¬ P02DiagonalFrontier.AcceptsAtDeclaredBound M (selfBits M)

def CandidateCodingBridgeGap : Prop :=
  Nonempty CandidateCodingBridge

def CandidateCodingBridge.toSemanticSelfEmbedder
    (B : CandidateCodingBridge) :
    SemanticSelfEmbedder where
  bits := B.selfBits
  valid := B.valid
  flips := B.flips

theorem candidate_coding_bridge_closes_semantic_self_embedding
    (h : CandidateCodingBridgeGap) :
    SemanticSelfEmbeddingGap := by
  rcases h with ⟨B⟩
  exact ⟨B.toSemanticSelfEmbedder⟩

theorem candidate_coding_bridge_closes_p02
    (h : CandidateCodingBridgeGap) :
    P02TerminalFrontier.P02Target := by
  exact semantic_self_embedding_closes_p02
    (candidate_coding_bridge_closes_semantic_self_embedding h)

#print axioms MCore.Real.P02KleeneBridgeFrontier.candidate_coding_bridge_closes_semantic_self_embedding
#print axioms MCore.Real.P02KleeneBridgeFrontier.candidate_coding_bridge_closes_p02

end P02KleeneBridgeFrontier
end Real
end MCore
