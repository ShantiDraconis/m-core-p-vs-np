import MCore.Real.P03InteractionConflict

namespace MCore
namespace Real
namespace P03TransitionSignature

open CanonicalFinalProof
open PNPNTMTableauEncoding
open P03MaterialLaw
open P03InteractionConflict

/--
A concrete transition-clause occurrence together with the real tableau step
from which that clause originates.
-/
structure TransitionClauseOccurrence
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (core : ClauseUnsatCore M x t) where
  step : Nat
  step_lt : step < t
  clause : NTMClause
  clause_in_core : clause ∈ core.clauses
  clause_in_step :
    clause ∈ ntmTransitionStepCNF M x t step

/--
Membership in the flattened transition CNF exposes the genuine time step.
No arithmetic decoding of variable numbers is used.
-/
theorem transition_clause_has_step
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    {clause : NTMClause}
    (h :
      clause ∈ ntmTransitionsCNF M x t) :
    ∃ s, s < t ∧
      clause ∈ ntmTransitionStepCNF M x t s := by
  unfold ntmTransitionsCNF at h
  rw [List.mem_flatMap] at h
  rcases h with ⟨s, hsRange, hsClause⟩
  exact ⟨s, List.mem_range.mp hsRange, hsClause⟩

/--
Every real Transit touch of an UNSAT core yields a concrete transition-step
occurrence.
-/
def occurrence_of_core_touch
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    {core : ClauseUnsatCore M x t}
    (hTouch :
      CoreTouches core (ntmTransitionsCNF M x t)) :
    TransitionClauseOccurrence M x t core := by
  rcases hTouch with ⟨clause, hCore, hTransit⟩
  rcases transition_clause_has_step hTransit with
    ⟨s, hs, hStep⟩
  exact
    { step := s
      step_lt := hs
      clause := clause
      clause_in_core := hCore
      clause_in_step := hStep }

/--
A genuine positive-time interaction conflict therefore exposes at least one
real transition step in every UNSAT core.
-/
def occurrence_of_interaction_core
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    (ht : 0 < t)
    (C : OrbitalInteractionConflict M x t)
    (core : ClauseUnsatCore M x t) :
    TransitionClauseOccurrence M x t core :=
  occurrence_of_core_touch
    (interaction_conflict_core_requires_transition ht C core)

#print axioms MCore.Real.P03TransitionSignature.transition_clause_has_step
#print axioms MCore.Real.P03TransitionSignature.occurrence_of_core_touch
#print axioms MCore.Real.P03TransitionSignature.occurrence_of_interaction_core

end P03TransitionSignature
end Real
end MCore
