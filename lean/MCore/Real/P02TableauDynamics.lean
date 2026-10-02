import MCore.Real.TableauTemplate
import MCore.Real.P02OddSemanticRecurrence

namespace MCore
namespace Real
namespace P02TableauDynamics

open CanonicalFinalProof
open P02TotalCandidateKleeneReduction
open P02ComplementRunRealization
open PNPNTMTableauEncoding
open SourceRecovery
open TableauTemplate

/-- The concrete complemented Cook--Levin reduction on bitstrings. -/
def R_M
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    BitString → BitString :=
  fun x => (complementSemanticReduction M hTotal).reduce x

/-- Second iterate of the concrete reduction. -/
def R2_M
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) : BitString :=
  R_M M hTotal (R_M M hTotal x)

@[simp] theorem R2_M_eq
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    R2_M M hTotal x =
      R_M M hTotal (R_M M hTotal x) := by
  rfl

/--
Circuit-level expansion of one concrete reduction step.
This exposes the exact bounded tableau before source recovery is added.
-/
theorem decodeCircuit_R_M
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
  exact SourceRecovery.decodeCircuit_reduce M hTotal x

/--
The second iterate is itself another concrete complemented tableau encoding,
now using the length/clock of R_M x.
-/
theorem decodeCircuit_R2_M
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    decodeCircuit (R2_M M hTotal x) =
      some
        (ntmCNFCircuit
          (boundedExecTableauCNF_NTM
            (complementToNTMCandidate M)
            (R_M M hTotal x)
            (M.timeBound (R_M M hTotal x).length))) := by
  simpa [R2_M] using
    (SourceRecovery.decodeCircuit_reduce
      M hTotal (R_M M hTotal x))

/-
Next exact obligations, intentionally not postulated:
  decodeChain₁ : decodeSource ... (R_M M hTotal x) = some x
  decodeChain₂ : decodeSource ... (R2_M M hTotal x) = some (R_M M hTotal x)

Both reduce to the still-unimplemented computable extraction of the time-0
head/right unit clauses from the decoded NTMCNF.
-/

end P02TableauDynamics
end Real
end MCore
