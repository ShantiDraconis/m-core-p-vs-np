import MCore.Real.P02TerminalForcingG2

namespace MCore
namespace Real
namespace P02G2CounterexampleAttack

open CanonicalFinalProof
open P02UniversalFailureWitnessMaterial
open P02TerminalForcingG2

/--
Canonical material frontier for G2.

The selector field is easy to inhabit as a bare function type. The mathematical
content is the coupled universal failure law for the chosen selector.
-/
def COUNTEREXAMPLE_MATERIAL_OPEN_MATH : Prop :=
  ∃ counterexample : PolyDTMCandidate → BitString,
    ∀ M : PolyDTMCandidate,
      ¬ M.CorrectAt
        P02TerminalForcingG2.CanonicalSAT
        (counterexample M)

/-- Bare selector inhabitation is structural only; it does not close any G2 payload. -/
def trivialSelector : CounterexampleSelector :=
  fun _ => []

theorem counterexampleSelector_nonempty :
    Nonempty CounterexampleSelector :=
  ⟨trivialSelector⟩

/-- Failure obligation for one explicitly supplied selector. -/
def SelectorFails (xM : CounterexampleSelector) : Prop :=
  ∀ M : PolyDTMCandidate,
    ¬ M.CorrectAt
      P02TerminalForcingG2.CanonicalSAT
      (xM M)

theorem selectorFails_iff_failureLaw
    (xM : CounterexampleSelector) :
    SelectorFails xM ↔ FailureLaw xM := by
  rfl

/--
Exact exposure audit: the coupled selector+failure frontier is definitionally
the same obligation as G2_TERMINAL. This theorem is an A-route equivalence only;
it is not a producer.
-/
theorem counterexampleMaterial_iff_terminal :
    COUNTEREXAMPLE_MATERIAL_OPEN_MATH ↔
      P02TerminalForcingG2.G2_TERMINAL := by
  rfl

/--
If the coupled terminal payload is ever materialized independently, it packages
into the already-audited UniversalFailureWitness constructor.
-/
def witnessOfCounterexampleMaterial
    (counterexample : PolyDTMCandidate → BitString)
    (fails : SelectorFails counterexample) :
    UniversalFailureWitness :=
  P02TerminalForcingG2.universalFailureWitnessOf counterexample fails

#print axioms MCore.Real.P02G2CounterexampleAttack.counterexampleSelector_nonempty
#print axioms MCore.Real.P02G2CounterexampleAttack.selectorFails_iff_failureLaw
#print axioms MCore.Real.P02G2CounterexampleAttack.counterexampleMaterial_iff_terminal
#print axioms MCore.Real.P02G2CounterexampleAttack.witnessOfCounterexampleMaterial

end P02G2CounterexampleAttack
end Real
end MCore
