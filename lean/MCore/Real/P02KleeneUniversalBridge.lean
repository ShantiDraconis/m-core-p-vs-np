import Mathlib.Computability.PartrecCode
import MCore.Real.P02UniversalFailureMinCut

namespace MCore
namespace Real
namespace P02KleeneUniversalBridge

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02UniversalFailureMinCut

/-- Candidate's declared acceptance proposition at its own certified clock. -/
def DeclaredAccepts
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  M.accepting
      (M.machine.run
        (M.timeBound x.length)
        (initialTMConfig M.machine x)).state = true

/-- One effective recursion-theoretic diagonal compiler for one candidate. -/
structure EffectiveDiagonalCompiler (M : PolyDTMCandidate) where
  f : Nat.Partrec.Code → ℕ →. ℕ
  partrec : Nat.Partrec₂ f

/-- Transport from a recursion-theorem code fixed point into the exact
canonical SAT language.  This is the remaining semantic compiler/realizer
interface; it does not assume UniversalFailure or a separation certificate. -/
structure CanonicalSATFixedPointRealizer
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M) where
  bitsOf : Nat.Partrec.Code → BitString
  flips_of_fixed :
    ∀ c,
      Nat.Partrec.Code.eval c = K.f c →
      CanonicalSAT (bitsOf c) ↔
        ¬ DeclaredAccepts M (bitsOf c)

/-- Mathlib's recursion theorem supplies the code-level fixed point. -/
theorem kleene_fixed_point
    {M : PolyDTMCandidate}
    (K : EffectiveDiagonalCompiler M) :
    ∃ c : Nat.Partrec.Code,
      Nat.Partrec.Code.eval c = K.f c :=
  Nat.Partrec.Code.fixed_point₂ K.partrec

/-- Per-candidate package required to turn Kleene self-reference into a
canonical SAT counterexample. -/
structure CandidateKleeneBridge (M : PolyDTMCandidate) where
  compiler : EffectiveDiagonalCompiler M
  realizer : CanonicalSATFixedPointRealizer M compiler

noncomputable def fixedCode
    {M : PolyDTMCandidate}
    (B : CandidateKleeneBridge M) :
    Nat.Partrec.Code :=
  Classical.choose (kleene_fixed_point B.compiler)

theorem fixedCode_spec
    {M : PolyDTMCandidate}
    (B : CandidateKleeneBridge M) :
    Nat.Partrec.Code.eval (fixedCode B) =
      B.compiler.f (fixedCode B) :=
  Classical.choose_spec (kleene_fixed_point B.compiler)

noncomputable def counterexample
    {M : PolyDTMCandidate}
    (B : CandidateKleeneBridge M) :
    BitString :=
  B.realizer.bitsOf (fixedCode B)

/-- The recursion-theorem fixed point plus the semantic SAT realizer produces
a genuine failure of the original candidate at one concrete input. -/
theorem counterexample_fails
    {M : PolyDTMCandidate}
    (B : CandidateKleeneBridge M) :
    ¬ M.CorrectAt CanonicalSAT (counterexample B) := by
  have hflip :
      CanonicalSAT (counterexample B) ↔
        ¬ DeclaredAccepts M (counterexample B) := by
    exact B.realizer.flips_of_fixed
      (fixedCode B) (fixedCode_spec B)
  intro hCorrect
  rcases hCorrect with ⟨_, hSem⟩
  by_cases hAcc : DeclaredAccepts M (counterexample B)
  · have hSat : CanonicalSAT (counterexample B) :=
      hSem.mp hAcc
    exact (hflip.mp hSat) hAcc
  · have hSat : CanonicalSAT (counterexample B) :=
      hflip.mpr hAcc
    exact hAcc (hSem.mpr hSat)

/-- Uniform non-literal self-reference bridge.  Unlike the falsified literal
string fixed-point route, this quantifies over Mathlib partial-recursive codes
and delegates only the genuine compiler/semantic-realizer obligations. -/
structure KleeneUniversalBridge where
  bridge : ∀ M : PolyDTMCandidate, CandidateKleeneBridge M

noncomputable def KleeneUniversalBridge.toProducer
    (B : KleeneUniversalBridge) :
    UniversalCounterexampleProducer where
  counterexample := fun M => counterexample (B.bridge M)
  failure := by
    intro M
    apply (failureMode_iff_not_correctAt
      M (counterexample (B.bridge M))).mpr
    exact counterexample_fails (B.bridge M)

theorem kleene_bridge_implies_universal_failure
    (B : KleeneUniversalBridge) :
    UniversalFailure CanonicalSAT :=
  producer_implies_universal_failure B.toProducer

theorem kleene_bridge_closes_internal_endpoint
    (B : KleeneUniversalBridge) :
    PneqNP :=
  producer_closes_internal_endpoint B.toProducer

/-- Exact remaining non-literal self-reference construction target after the
recursion theorem itself has been discharged. -/
abbrev KleeneUniversalBridgeGap : Prop :=
  Nonempty KleeneUniversalBridge

#print axioms MCore.Real.P02KleeneUniversalBridge.kleene_fixed_point
#print axioms MCore.Real.P02KleeneUniversalBridge.counterexample_fails
#print axioms MCore.Real.P02KleeneUniversalBridge.KleeneUniversalBridge.toProducer
#print axioms MCore.Real.P02KleeneUniversalBridge.kleene_bridge_implies_universal_failure
#print axioms MCore.Real.P02KleeneUniversalBridge.kleene_bridge_closes_internal_endpoint

end P02KleeneUniversalBridge
end Real
end MCore
