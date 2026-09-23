import MCore.Real.P02G21G22Attack

namespace MCore
namespace Research
namespace Prime2

open Real
open Real.CanonicalFinalProof
open Real.P02G21G22Attack

structure Prime2Candidate where
  code : Nat

structure Prime2Input where
  code : Nat

def Prime2CorrectAt (_M : Prime2Candidate) (_x : Prime2Input) : Prop :=
  True

structure ConservativePrime2Interpretation where
  mapCandidate : PolyDTMCandidate → Prime2Candidate
  mapInput : BitString → Prime2Input
  inputFaithful : Function.Injective mapInput
  failure_reflects :
    ∀ (M : PolyDTMCandidate) (x : BitString),
      ¬ Prime2CorrectAt (mapCandidate M) (mapInput x) →
      ¬ M.CorrectAt SATTarget x

def ConservativeInterpretationGap : Prop :=
  Nonempty ConservativePrime2Interpretation

def MappedPrime2UniversalFailure
    (I : ConservativePrime2Interpretation) : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ x : BitString,
      ¬ Prime2CorrectAt (I.mapCandidate M) (I.mapInput x)

theorem prime2SemanticFailureTransfer
    (I : ConservativePrime2Interpretation)
    (hPrime2 : MappedPrime2UniversalFailure I) :
    G21Pointwise := by
  intro M
  rcases hPrime2 M with ⟨x, hx⟩
  exact ⟨x, I.failure_reflects M x hx⟩

structure Prime2ResearchClosure where
  interpretation : ConservativePrime2Interpretation
  universalFailure : MappedPrime2UniversalFailure interpretation

theorem researchClosure_to_g21
    (R : Prime2ResearchClosure) :
    G21Pointwise :=
  prime2SemanticFailureTransfer
    R.interpretation
    R.universalFailure

theorem researchClosure_to_p02
    (R : Prime2ResearchClosure) :
    Real.P02TerminalFrontier.P02Target :=
  Real.P02G21G22Attack.g21_pointwise_iff_p02_target.mp
    (researchClosure_to_g21 R)

#print axioms MCore.Research.Prime2.prime2SemanticFailureTransfer
#print axioms MCore.Research.Prime2.researchClosure_to_g21
#print axioms MCore.Research.Prime2.researchClosure_to_p02

end Prime2
end Research
end MCore
