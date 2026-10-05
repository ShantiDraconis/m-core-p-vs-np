import MCore.Real.P02TerminalForcingG2

namespace MCore
namespace Real
namespace P02G2CounterexampleAttack

open CanonicalFinalProof
open P02UniversalFailureWitnessMaterial
open P02TerminalForcingG2

/--
Canonical material frontier for G2.

This is intentionally only the two terminal payloads exposed directly:
1. a total uniform selector M ↦ x_M;
2. a proof that M fails on x_M.

No inhabitant is asserted here.
-/
def COUNTEREXAMPLE_MATERIAL_OPEN_MATH : Prop :=
  ∃ counterexample : PolyDTMCandidate → BitString,
    ∀ M : PolyDTMCandidate,
      ¬ M.CorrectAt
        P02TerminalForcingG2.CanonicalSAT
        (counterexample M)

/--
Exact exposure audit: the direct 0/2 payload frontier is definitionally the
same obligation as G2_TERMINAL. This theorem is an A-route equivalence only;
it is not a producer.
-/
theorem counterexampleMaterial_iff_terminal :
    COUNTEREXAMPLE_MATERIAL_OPEN_MATH ↔
      P02TerminalForcingG2.G2_TERMINAL := by
  rfl

/--
If the two terminal payloads are ever materialized independently, they package
into the already-audited UniversalFailureWitness constructor.
-/
def witnessOfCounterexampleMaterial
    (counterexample : PolyDTMCandidate → BitString)
    (fails :
      ∀ M : PolyDTMCandidate,
        ¬ M.CorrectAt
          P02TerminalForcingG2.CanonicalSAT
          (counterexample M)) :
    UniversalFailureWitness :=
  P02TerminalForcingG2.universalFailureWitnessOf counterexample fails

#print axioms MCore.Real.P02G2CounterexampleAttack.counterexampleMaterial_iff_terminal
#print axioms MCore.Real.P02G2CounterexampleAttack.witnessOfCounterexampleMaterial

end P02G2CounterexampleAttack
end Real
end MCore
