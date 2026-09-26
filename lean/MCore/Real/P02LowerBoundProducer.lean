import MCore.Real.CanonicalSATBoundary
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P02LowerBoundProducer

open CanonicalFinalProof
open FailProofAllGaps
open CanonicalSATBoundary
open CanonicalCircuitBits

/--
All producer lanes terminate in the already-hardened canonical object
`FailureGenerator (SATBits circuitBitEncoding)`.
No new notion of lower bound is introduced here.
-/
structure DiagonalAdviceData where
  fail_generator : FailureGenerator (SATBits circuitBitEncoding)

structure NonNaturalData where
  fail_generator : FailureGenerator (SATBits circuitBitEncoding)

structure GCTData where
  fail_generator : FailureGenerator (SATBits circuitBitEncoding)

structure MetaComplexityData where
  fail_generator : FailureGenerator (SATBits circuitBitEncoding)

inductive LowerBoundProducer where
  | diagonalAdvice (d : DiagonalAdviceData)
  | nonNatural (d : NonNaturalData)
  | gct (d : GCTData)
  | metaComplexity (d : MetaComplexityData)

/-- Every admitted producer is only a typed route to the existing fail
generator.  Hence transport is kernel-trivial and cannot weaken the target. -/
def LowerBoundProducer.toFailureGenerator :
    LowerBoundProducer →
      FailureGenerator (SATBits circuitBitEncoding)
  | .diagonalAdvice d => d.fail_generator
  | .nonNatural d => d.fail_generator
  | .gct d => d.fail_generator
  | .metaComplexity d => d.fail_generator

/-- Single normative OPEN_MATH root for all competing lower-bound lanes. -/
def LowerBoundProducerGap : Prop :=
  Nonempty LowerBoundProducer

theorem producer_gap_closes_sat_fail
    (h : LowerBoundProducerGap) :
    SATFailGap circuitBitEncoding := by
  rcases h with ⟨P⟩
  exact ⟨P.toFailureGenerator⟩

theorem producer_gap_closes_internal_separation
    (hNP : SATInNPGap circuitBitEncoding)
    (h : LowerBoundProducerGap) :
    PneqNP := by
  exact sat_internal_closure_implies_p_ne_np
    { encoding := circuitBitEncoding
      sat_in_np := hNP
      fail_generator := (Classical.choice (producer_gap_closes_sat_fail h)) }

/-- No producer is postulated here.  The theorem records the exact remaining
mathematical payload without adding axioms or sorry terms. -/
theorem producer_gap_iff_sat_fail :
    LowerBoundProducerGap ↔ SATFailGap circuitBitEncoding := by
  constructor
  · exact producer_gap_closes_sat_fail
  · intro h
    rcases h with ⟨G⟩
    exact ⟨.diagonalAdvice ⟨G⟩⟩

#print axioms MCore.Real.P02LowerBoundProducer.producer_gap_closes_sat_fail
#print axioms MCore.Real.P02LowerBoundProducer.producer_gap_closes_internal_separation
#print axioms MCore.Real.P02LowerBoundProducer.producer_gap_iff_sat_fail

end P02LowerBoundProducer
end Real
end MCore
