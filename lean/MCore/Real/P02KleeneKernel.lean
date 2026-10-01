import Mathlib.Computability.PartrecCode
import MCore.Real.P02OperatorKernel

namespace MCore
namespace Real
namespace P02KleeneKernel

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02OperatorKernel

abbrev SATTarget : BitLanguage :=
  SATBits circuitBitEncoding

/-- Acceptance bit used by the canonical deterministic candidate at its
declared polynomial clock. -/
def DeclaredAccept
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  M.accepting
      (M.machine.run
        (M.timeBound x.length)
        (initialTMConfig M.machine x)).state = true

/-- Effective diagonal program family for one deterministic candidate. -/
structure EffectiveDiagonalCompiler (M : PolyDTMCandidate) where
  f : Nat.Partrec.Code → ℕ →. ℕ
  partrec : Nat.Partrec₂ f

/-- Canonical-SAT interpretation of recursion-theorem fixed points.
The field is a semantic flip, not the desired non-P conclusion. -/
structure SATFixedPointRealizer
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M) where
  bitsOf : Nat.Partrec.Code → BitString
  flip_of_fixed :
    ∀ c,
      Nat.Partrec.Code.eval c = K.f c →
      (SATTarget (bitsOf c) ↔ ¬ DeclaredAccept M (bitsOf c))

theorem kleene_fixed_point
    {M : PolyDTMCandidate}
    (K : EffectiveDiagonalCompiler M) :
    ∃ c : Nat.Partrec.Code,
      Nat.Partrec.Code.eval c = K.f c :=
  Nat.Partrec.Code.fixed_point₂ K.partrec

/-- A semantic flip on the recursion-theorem fixed point forces failure of
CorrectAt. This is pure downstream logic; no lower-bound premise is added. -/
theorem fixed_flip_fails
    (M : PolyDTMCandidate)
    (x : BitString)
    (hflip : SATTarget x ↔ ¬ DeclaredAccept M x) :
    ¬ M.CorrectAt SATTarget x := by
  intro hCorrect
  change
    M.machine.HaltsWithin
        (M.timeBound x.length)
        (initialTMConfig M.machine x) ∧
      (DeclaredAccept M x ↔ SATTarget x)
    at hCorrect
  rcases hCorrect with ⟨_, hcorr⟩
  by_cases hacc : DeclaredAccept M x
  · have hsat : SATTarget x := hcorr.mp hacc
    exact (hflip.mp hsat) hacc
  · have hsat : SATTarget x := hflip.mpr hacc
    exact hacc (hcorr.mpr hsat)

/-- The exact constructive bridge remaining after importing Kleene's theorem. -/
structure KleeneSATBridge where
  compiler : ∀ M : PolyDTMCandidate, EffectiveDiagonalCompiler M
  realizer :
    ∀ M : PolyDTMCandidate,
      SATFixedPointRealizer M (compiler M)

/-- A Kleene/SAT bridge mechanically produces the terminal P02 operator. -/
def KleeneSATBridge.toP02Producer
    (B : KleeneSATBridge) :
    CanonicalSATP02Producer := by
  refine
    { counterexample := fun M =>
        let c := Classical.choose (kleene_fixed_point (B.compiler M))
        (B.realizer M).bitsOf c
      sound := ?_ }
  intro M
  let c := Classical.choose (kleene_fixed_point (B.compiler M))
  have hc :
      Nat.Partrec.Code.eval c = (B.compiler M).f c :=
    Classical.choose_spec (kleene_fixed_point (B.compiler M))
  exact fixed_flip_fails M ((B.realizer M).bitsOf c)
    ((B.realizer M).flip_of_fixed c hc)

/-- The remaining OPEN_MATH can be attacked through this strictly smaller,
explicit two-map bridge. -/
def KleeneSATBridgeGap : Prop :=
  Nonempty KleeneSATBridge

theorem kleene_bridge_closes_p02
    (h : KleeneSATBridgeGap) :
    Nonempty CanonicalSATP02Producer := by
  rcases h with ⟨B⟩
  exact ⟨B.toP02Producer⟩

theorem kleene_bridge_closes_not_in_p
    (h : KleeneSATBridgeGap) :
    ¬ InP SATTarget := by
  exact canonicalSATProducer_iff_notInP.mp
    (kleene_bridge_closes_p02 h)

end P02KleeneKernel
end Real
end MCore
