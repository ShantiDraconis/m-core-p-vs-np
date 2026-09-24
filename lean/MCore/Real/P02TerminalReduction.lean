import MCore.Real.P02CookLevinFromBoundedExec

namespace MCore
namespace Real
namespace P02TerminalReduction

open CanonicalFinalProof
open P02KleeneBridge
open P02KleeneCookLevinBridge
open P02CookLevinFromBoundedExec
open P02BoundedComputationClose

/--
Uniform same-input transport for every polynomial deterministic candidate.
The compiler is explicit and the only semantic field is the existing
same_input_of_fixed obligation specialized to the concrete rejectCircuit.
-/
structure UniformSameInputTransport where
  compiler : ∀ M : PolyDTMCandidate, EffectiveDiagonalCompiler M
  transport :
    ∀ M : PolyDTMCandidate,
      SameInputTransport M (compiler M)

/--
Exact reduced P02 payload on the active lane.

Transition soundness is already constructed in P02BoundedComputationClose.
A tableau-completeness certificate therefore closes BoundedExecCorrectness,
which closes Cook-Levin correctness.  The only remaining independent
self-reference payload is UniformSameInputTransport.
-/
structure P02ReducedClosureData where
  tableauCompleteness : TableauCompletenessCertificate
  sameInput : UniformSameInputTransport

def P02ReducedClosureData.boundedExecCorrectness
    (D : P02ReducedClosureData) :
    BoundedExecCorrectness :=
  boundedExec_of_tableauCompleteness D.tableauCompleteness

def P02ReducedClosureData.toUniformCookLevinBridge
    (D : P02ReducedClosureData) :
    UniformCookLevinSameInputBridge where
  compiler := D.sameInput.compiler
  data := fun M =>
    dataOfBoundedExec
      D.boundedExecCorrectness
      (D.sameInput.transport M)

theorem P02ReducedClosureData.flips_of_fixed
    (D : P02ReducedClosureData)
    (M : PolyDTMCandidate)
    (c : Nat.Partrec.Code)
    (hfixed :
      Nat.Partrec.Code.eval c = (D.sameInput.compiler M).f c) :
    P02G21G22Attack.SATTarget
        ((D.toUniformCookLevinBridge.data M).bitsOf c) ↔
      ¬ P02DiagonalFrontier.AcceptsAtDeclaredBound M
        ((D.toUniformCookLevinBridge.data M).bitsOf c) :=
  (D.toUniformCookLevinBridge.data M).flips_of_fixed c hfixed

theorem P02ReducedClosureData.closes_G21
    (D : P02ReducedClosureData) :
    P02G21G22Attack.G21Pointwise :=
  uniformCookLevinBridge_closes_G21 D.toUniformCookLevinBridge

theorem P02ReducedClosureData.closes_P02Target
    (D : P02ReducedClosureData) :
    P02TerminalFrontier.P02Target :=
  uniformCookLevinBridge_closes_P02 D.toUniformCookLevinBridge

/-
Critical reduction:

TableauCompletenessCertificate
  -> BoundedExecCorrectness
  -> rejectCircuit_cook_levin_correct
  -> cook_levin_correct CLOSED

UniformSameInputTransport
  -> same_input_of_fixed

Both together:
  -> flips_of_fixed
  -> G21Pointwise
  -> P02Target

No P02Target/G21/flips premise occurs in either input structure.
-/

#print axioms MCore.Real.P02TerminalReduction.P02ReducedClosureData.flips_of_fixed
#print axioms MCore.Real.P02TerminalReduction.P02ReducedClosureData.closes_P02Target

end P02TerminalReduction
end Real
end MCore
