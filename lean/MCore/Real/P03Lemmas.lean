import MCore.Real.P03MaterialLaw
import MCore.Real.SourceRecovery

namespace MCore
namespace Real
namespace P03Lemmas

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02ComplementRunRealization
open P02TableauDynamics
open P02OddSemanticRecurrence
open P03MaterialLaw
open SourceRecovery

/--
Every concrete orbit step retains and decodes its immediate predecessor.

This is the non-prefix recovery law needed by P03: it uses the actual
ntmInitialCNF/source decoder and makes no claim that the predecessor is a
literal bit-prefix of the successor.
-/
@[simp] theorem decode_recovers_orbit_step
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (k : Nat) :
    decodeSourceBits
        (complementToNTMCandidate M)
        (Orbit (R_M M hTotal) seed k).length
        (M.timeBound (Orbit (R_M M hTotal) seed k).length)
        (Orbit (R_M M hTotal) seed (k + 1)) =
      some (Orbit (R_M M hTotal) seed k) := by
  simpa [Orbit, R_M] using
    (SourceRecovery.decodeSource_reduce
      M hTotal (Orbit (R_M M hTotal) seed k))

/--
The canonical full-support conflict witness necessarily includes the transition
block.  This is a structural fact about fullSupport only; it does not claim
that every minimal or relevant conflict must contain Transit.
-/
theorem full_conflict_support_contains_transition
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (hUnsat : CNFUnsat (boundedExecTableauCNF_NTM M x t)) :
    (((fullConflictExtractor M).locate x t hUnsat).support.transit = true) := by
  rfl

#print axioms MCore.Real.P03Lemmas.decode_recovers_orbit_step
#print axioms MCore.Real.P03Lemmas.full_conflict_support_contains_transition

end P03Lemmas
end Real
end MCore
