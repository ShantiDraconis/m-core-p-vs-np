import MCore.Real.P02SemanticSelfSubstitution

namespace MCore
namespace Real
namespace P02RejectionImageEscape

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02SemanticSelfSubstitution

theorem totalClock_globalFlip_iff_correctOnRejectImage
    (M : PolyDTMCandidate)
    (hTotal : ∀ y : BitString, OwnClockHalts M y) :
    (∀ x : BitString,
        observedBit M (rejectCode M x) = !(observedBit M x)) ↔
      (∀ x : BitString,
        M.CorrectAt (SATBits circuitBitEncoding) (rejectCode M x)) := by
  constructor
  · intro hFlip x
    refine ⟨hTotal (rejectCode M x), ?_⟩
    have hSem := rejectCode_semantics M x
    have hx := hTotal x
    have hF := hFlip x
    unfold observedBit at hF
    constructor
    · intro hAcc
      have hSrcFalse :
          M.accepting
              (M.machine.run
                (M.timeBound x.length)
                (initialTMConfig M.machine x)).state = false := by
        cases hsrc :
            M.accepting
              (M.machine.run
                (M.timeBound x.length)
                (initialTMConfig M.machine x)).state <;>
          cases hdst :
            M.accepting
              (M.machine.run
                (M.timeBound (rejectCode M x).length)
                (initialTMConfig M.machine (rejectCode M x))).state <;>
          simp_all
      exact (hSem.mpr ⟨hx, hSrcFalse⟩)
    · intro hSat
      have hSrcFalse := (hSem.mp hSat).2
      cases hsrc :
          M.accepting
            (M.machine.run
              (M.timeBound x.length)
              (initialTMConfig M.machine x)).state <;>
        cases hdst :
          M.accepting
            (M.machine.run
              (M.timeBound (rejectCode M x).length)
              (initialTMConfig M.machine (rejectCode M x))).state <;>
        simp_all
  · intro hCorrect x
    have h :=
      correctAt_rejectCode_flip M x (hTotal x) (hCorrect x)
    unfold observedBit
    cases hsrc :
        M.accepting
          (M.machine.run
            (M.timeBound x.length)
            (initialTMConfig M.machine x)).state <;>
      cases hdst :
        M.accepting
          (M.machine.run
            (M.timeBound (rejectCode M x).length)
            (initialTMConfig M.machine (rejectCode M x))).state <;>
      simp_all

def RejectImageEscape : Prop :=
  ∀ M : PolyDTMCandidate,
    (∀ y : BitString, OwnClockHalts M y) →
      ∃ x : BitString,
        ¬ M.CorrectAt (SATBits circuitBitEncoding) (rejectCode M x)

theorem rejectImageEscape_iff_totalClockAntiAlternation :
    RejectImageEscape ↔ TotalClockAntiAlternation := by
  constructor
  · intro H M hTotal hFlip
    rcases H M hTotal with ⟨x, hFail⟩
    have hCorrectImage :=
      (totalClock_globalFlip_iff_correctOnRejectImage M hTotal).mp hFlip
    exact hFail (hCorrectImage x)
  · intro H M hTotal
    by_contra hNoEscape
    push_neg at hNoEscape
    have hFlip :=
      (totalClock_globalFlip_iff_correctOnRejectImage M hTotal).mpr hNoEscape
    exact H M hTotal hFlip

theorem rejectImageEscape_implies_universalFailure :
    RejectImageEscape →
      UniversalFailure (SATBits circuitBitEncoding) := by
  intro H
  exact totalClockSemanticCollision_implies_universal_failure
    (totalClockCollision_iff_antiAlternation.mpr
      (rejectImageEscape_iff_totalClockAntiAlternation.mp H))

#print axioms MCore.Real.P02RejectionImageEscape.totalClock_globalFlip_iff_correctOnRejectImage
#print axioms MCore.Real.P02RejectionImageEscape.rejectImageEscape_iff_totalClockAntiAlternation
#print axioms MCore.Real.P02RejectionImageEscape.rejectImageEscape_implies_universalFailure

end P02RejectionImageEscape
end Real
end MCore
