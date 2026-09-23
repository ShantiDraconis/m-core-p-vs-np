import MCore.Real.P02EffectiveCompilerConstruction
import MCore.Real.P02KleeneDefinednessFrontier

namespace MCore
namespace Real
namespace P02BoundedCompilerRoute

open CanonicalFinalProof
open CanonicalCircuitBits
open P02BitStringNatCoding
open P02CodeSemanticInput
open P02KleeneBridge
open P02KleeneDefinednessFrontier
open P02CookLevinFromBoundedExec
open P02EffectiveCompilerConstruction

/--
A bounded replacement for the semantic self-input is useful only if, at the
chosen Kleene code, the bounded observation agrees with the actual value at 0.
This interface deliberately makes that catch-up condition explicit rather than
silently assuming decidability of termination.
-/
structure BoundedSelfInputApproximation where
  observe : Nat.Partrec.Code → BitString
  catches :
    ∀ c : Nat.Partrec.Code,
      DefinedAtZero c →
      observe c = selfInput c

/--
Once a bounded/decidable observation is proved to catch the actual fixed-point
value, the existing Cook--Levin constructor can be reused unchanged.
-/
def boundedCompilerValue
    (A : BoundedSelfInputApproximation)
    (M : PolyDTMCandidate)
    (c : Nat.Partrec.Code) : Nat :=
  encodeBitsNat
    (encodeCircuit (rejectCircuit M (A.observe c)))

theorem boundedCompilerValue_eq_compilerValue
    (A : BoundedSelfInputApproximation)
    (M : PolyDTMCandidate)
    (c : Nat.Partrec.Code)
    (hdom : DefinedAtZero c) :
    boundedCompilerValue A M c =
      compilerValue M c := by
  unfold boundedCompilerValue compilerValue
  rw [A.catches c hdom]

/--
Fail-closed audit endpoint.  A computability proof for the bounded compiler
does not by itself close the terminal theorem: one still needs the catch-up
property above at every defined code (or a weaker theorem specialized to the
Kleene fixed point).  This records the exact residual obligation.
-/
def UniformBoundedCompilerComputable
    (A : BoundedSelfInputApproximation) : Prop :=
  ∀ M : PolyDTMCandidate,
    Computable (boundedCompilerValue A M)

theorem boundedRoute_to_terminal
    (A : BoundedSelfInputApproximation)
    (hComp : UniformBoundedCompilerComputable A)
    (hLift :
      ∀ M : PolyDTMCandidate,
        Computable (boundedCompilerValue A M) →
        Computable (compilerValue M)) :
    UniformCompilerValueComputable := by
  intro M
  exact hLift M (hComp M)

#print axioms MCore.Real.P02BoundedCompilerRoute.boundedCompilerValue_eq_compilerValue
#print axioms MCore.Real.P02BoundedCompilerRoute.boundedRoute_to_terminal

end P02BoundedCompilerRoute
end Real
end MCore
