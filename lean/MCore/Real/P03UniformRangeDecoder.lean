import MCore.Real.SourceRecovery
import MCore.Real.P03PerfectFlipDichotomy

namespace MCore
namespace Real
namespace P03UniformRangeDecoder

open CanonicalFinalProof
open CanonicalCircuitBits
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction
open P02ComplementRunRealization
open P02TableauDynamics
open PNPNTMTableauEncoding
open SourceRecovery

/--
A source decoder that receives only the encoded tableau bits.
Unlike decodeSourceBits, it receives neither the source length nor the clock.
This is the exact material interface needed by a physical perfect-flip
candidate.
-/
structure UniformRangeDecoder
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) where
  decode : BitString → Option BitString
  correct :
    ∀ x : BitString,
      decode (R_M M hTotal x) = some x

/--
The existing parameterized source recovery immediately gives the pointwise
existence statement.  What is still missing is one uniform decoder function
that discovers the metadata from the encoded input itself.
-/
theorem pointwise_source_recovery
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    ∃ n t,
      decodeSourceBits
          (complementToNTMCandidate M)
          n t
          (R_M M hTotal x) = some x := by
  refine ⟨x.length, M.timeBound x.length, ?_⟩
  simpa [R_M] using decodeSource_reduce M hTotal x

/--
The head block is at a metadata-independent clause position.
This is the first structural fact needed for a uniform decoder.
-/
theorem head_block_offset_independent
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    headBlockOffset (complementToNTMCandidate M) =
      initialStateClauseCount (complementToNTMCandidate M) := by
  rfl

/--
At reduction outputs the decoded circuit is exactly the concrete tableau.
This exposes all clock/radius metadata syntactically inside one circuit.
-/
theorem range_decodes_to_concrete_tableau
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    decodeCircuit (R_M M hTotal x) =
      some
        (ntmCNFCircuit
          (boundedExecTableauCNF_NTM
            (complementToNTMCandidate M)
            x
            (M.timeBound x.length))) := by
  simpa [R_M] using decodeCircuit_R_M M hTotal x

/--
The remaining constructive producer for the B branch.
It is deliberately weaker than PerfectFlip: it asks only for uniform recovery
of the previous source from a genuine reduction image.
-/
def UniformRangeDecoderLaw : Prop :=
  ∃ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M),
    Nonempty (UniformRangeDecoder M hTotal)

#print axioms MCore.Real.P03UniformRangeDecoder.pointwise_source_recovery
#print axioms MCore.Real.P03UniformRangeDecoder.head_block_offset_independent
#print axioms MCore.Real.P03UniformRangeDecoder.range_decodes_to_concrete_tableau

end P03UniformRangeDecoder
end Real
end MCore
