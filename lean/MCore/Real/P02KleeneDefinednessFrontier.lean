import Mathlib.Computability.PartrecCode
import MCore.Real.P02KleeneBridge
import MCore.Real.P02BitStringNatCoding
import MCore.Real.P02CodeSemanticInput
import MCore.Real.P02CookLevinFromBoundedExec
import MCore.Real.P02TableauCompletenessClose

namespace MCore
namespace Real
namespace P02KleeneDefinednessFrontier

open CanonicalFinalProof
open CanonicalCircuitBits
open P02KleeneBridge
open P02BitStringNatCoding
open P02CodeSemanticInput
open P02CookLevinFromBoundedExec
open P02TableauCompletenessClose

/-- Exact semantic target for a Kleene code whose value at 0 is usable as a
canonical bitstring.  The recursion theorem itself gives extensional equality
of partial functions but not this definedness fact. -/
def DefinedAtZero (c : Nat.Partrec.Code) : Prop :=
  (c.eval 0).Dom

/-- A fixed point plus definedness at zero is enough to extract the concrete
natural value observed by the extensional self-input projection. -/
noncomputable def fixedPointValue
    (c : Nat.Partrec.Code)
    (hdom : DefinedAtZero c) : Nat :=
  (c.eval 0).get hdom

theorem selfInput_eq_decode_fixedPointValue
    (c : Nat.Partrec.Code)
    (hdom : DefinedAtZero c) :
    selfInput c = decodeBitsNatD (fixedPointValue c hdom) := by
  unfold selfInput fixedPointValue DefinedAtZero
  rw [dif_pos hdom]

/-- Minimal defined fixed-point obligation.  It deliberately does not assert
P02/G21 and does not hide a same-input equation. -/
structure DefinedKleeneFixedPoint
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M) where
  code : Nat.Partrec.Code
  fixed : Nat.Partrec.Code.eval code = K.f code
  defined_zero : DefinedAtZero code

/-- The ordinary Kleene theorem supplies code+fixed, but the repository still
needs a proof that an appropriate fixed point is defined at zero. -/
def KleeneDefinednessGap
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M) : Prop :=
  Nonempty (DefinedKleeneFixedPoint M K)

/-- Once a defined fixed point is available, extensional equality can be used
without any halting decision. -/
theorem fixedPoint_zero_eq
    {M : PolyDTMCandidate}
    {K : EffectiveDiagonalCompiler M}
    (F : DefinedKleeneFixedPoint M K) :
    F.code.eval 0 = K.f F.code 0 := by
  exact congrFun F.fixed 0

/-
AUDIT RESULT.

For a compiler that computes its output by first demanding the semantic value
of c.eval 0, the induced transformation is strict.  The everywhere-divergent
partial function is therefore a possible semantic fixed point.  Consequently
Nat.Partrec.Code.fixed_point₂ alone cannot justify DefinedAtZero.

This file isolates that missing fact explicitly rather than promoting a
partial fixed point to a SAT witness.
-/

#print axioms MCore.Real.P02KleeneDefinednessFrontier.selfInput_eq_decode_fixedPointValue
#print axioms MCore.Real.P02KleeneDefinednessFrontier.fixedPoint_zero_eq

end P02KleeneDefinednessFrontier
end Real
end MCore
