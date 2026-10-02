import MCore.Real.P03MaterialLaw
import MCore.Real.P02OddParityMixingFrontier

namespace MCore
namespace Real
namespace P04Closure

open CanonicalFinalProof
open P02OddSemanticRecurrence
open P02OddParityMixingFrontier
open P02TableauDynamics
open P03MaterialLaw

/--
Mechanical projection: one genuine P03 material witness yields the existing
odd semantic recurrence, with no additional mathematical assumption.
-/
theorem materialWitness_to_oddSemanticRecurrence
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (W : ClauseDerivedParityMixing M hTotal) :
    OddSemanticRecurrence M (R_M M hTotal) := by
  refine ⟨W.seed, W.i, W.j, W.odd_gap, ?_⟩
  exact W.phase_to_obs
    (Orbit (R_M M hTotal) W.seed W.i)
    (Orbit (R_M M hTotal) W.seed W.j)
    W.same_phase

/--
If and only if P03 is materially inhabited for every total candidate, the
existing P02 odd-parity frontier is supplied.  This theorem is conditional and
does not claim P03_MATERIAL_LAW itself.
-/
theorem p03_material_law_implies_oddParityMixing
    (H : P03_MATERIAL_LAW) :
    OddParityMixingConjecture := by
  intro M hTotal
  let W : ClauseDerivedParityMixing M hTotal :=
    Classical.choice (H M hTotal)
  let hOdd :
      OddSemanticRecurrence M (R_M M hTotal) :=
    materialWitness_to_oddSemanticRecurrence W
  exact ⟨witness_of_oddSemanticRecurrence hOdd⟩

/--
Conditional endpoint composition only.  This remains unusable as a final
closure until P03_MATERIAL_LAW is proved without placeholder proof terms or new assumptions.
-/
theorem p03_material_law_closes_internal_endpoint
    (H : P03_MATERIAL_LAW) :
    PneqNP :=
  oddParityMixing_closes_internal_endpoint
    (p03_material_law_implies_oddParityMixing H)

/--
Current fail-closed status.  Do not change these constants merely because the
conditional closure above compiles; they change only after a kernel-checked
inhabitant of P03_MATERIAL_LAW exists.
-/
def MATERIAL_GAPS : Nat := 1
def OPEN_BRIDGE : Nat := 1
def GREEN : Bool := false

#print axioms MCore.Real.P04Closure.materialWitness_to_oddSemanticRecurrence
#print axioms MCore.Real.P04Closure.p03_material_law_implies_oddParityMixing
#print axioms MCore.Real.P04Closure.p03_material_law_closes_internal_endpoint

end P04Closure
end Real
end MCore
