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
A clause in one transition step comes from one concrete control-state /
head-symbol transition case.
-/
theorem transition_step_clause_has_case
    {M : PolyNTMCandidate}
    {x : BitString}
    {t s : Nat}
    {clause : NTMClause}
    (h :
      clause ∈ ntmTransitionStepCNF M x t s) :
    ∃ q : Fin (M.stateCount + 1),
      ∃ a : Option Bool,
        clause ∈ ntmTransitionCaseCNF M x t s q a := by
  unfold ntmTransitionStepCNF at h
  rw [List.mem_flatten] at h
  rcases h with ⟨casesForQ, hCasesForQ, hClause⟩
  rw [List.mem_ofFn] at hCasesForQ
  rcases hCasesForQ with ⟨q, rfl⟩
  rw [List.mem_flatMap] at hClause
  rcases hClause with ⟨a, _ha, hClause⟩
  exact ⟨q, a, hClause⟩

inductive TransitionCaseKind where
  | haltedStutter
  | activeChoice
  deriving DecidableEq, Repr

inductive ActiveClauseKind where
  | guardChoice
  | choiceGuard
  | atMostOneChoice
  | choiceEffect
  deriving DecidableEq, Repr

/--
One clause occurrence refined to the concrete transition case and, when the
case is active, to the exact syntactic region inside ntmActiveChoiceCNF.
-/
structure TransitionInteractionSignature
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (core : ClauseUnsatCore M x t) where
  step : Nat
  step_lt : step < t
  q : Fin (M.stateCount + 1)
  a : Option Bool
  clause : NTMClause
  clause_in_core : clause ∈ core.clauses
  clause_in_case : clause ∈ ntmTransitionCaseCNF M x t step q a
  kind : TransitionCaseKind
  halted_proof :
    kind = .haltedStutter →
      clause ∈ ntmHaltedStutterCNF M x t step q a
  active_proof :
    kind = .activeChoice →
      clause ∈ ntmActiveChoiceCNF M x t step q a

/--
A clause in an active transition case belongs to exactly one of the four
syntactic regions used to build ntmActiveChoiceCNF.  The theorem returns a
disjunction because these regions can overlap extensionally as lists.
-/
theorem active_clause_region
    {M : PolyNTMCandidate}
    {x : BitString}
    {t s : Nat}
    {q : Fin (M.stateCount + 1)}
    {a : Option Bool}
    {clause : NTMClause}
    (h : clause ∈ ntmActiveChoiceCNF M x t s q a) :
    clause = ntmGuardChoiceClause M x t s q a ∨
    (∃ p ∈ ntmIndexedTransitions (M.machine.transition q a),
      clause ∈ ntmChoiceGuardCNF M x t s q a p.1) ∨
    clause ∈ ntmAtMostOneChoiceCNF M x t s q a ∨
    (∃ p ∈ ntmIndexedTransitions (M.machine.transition q a),
      clause ∈ ntmChoiceEffectCNF M x t s q a p) := by
  unfold ntmActiveChoiceCNF at h
  simp only [List.mem_append, List.mem_singleton] at h
  rcases h with hGuard | hRest
  · exact Or.inl hGuard
  · rcases hRest with hChoiceGuard | hRest
    · rw [List.mem_flatMap] at hChoiceGuard
      rcases hChoiceGuard with ⟨p, hp, hcl⟩
      exact Or.inr (Or.inl ⟨p, hp, hcl⟩)
    · rcases hRest with hAtMost | hEffect
      · exact Or.inr (Or.inr (Or.inl hAtMost))
      · rw [List.mem_flatMap] at hEffect
        rcases hEffect with ⟨p, hp, hcl⟩
        exact Or.inr (Or.inr (Or.inr ⟨p, hp, hcl⟩))

/--
Refine one concrete occurrence to halted-vs-active by the actual candidate
state flags.  No semantic endpoint is assumed.
-/
def signature_of_occurrence
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    {core : ClauseUnsatCore M x t}
    (occ : TransitionClauseOccurrence M x t core) :
    TransitionInteractionSignature M x t core := by
  rcases transition_step_clause_has_case occ.clause_in_step with
    ⟨q, a, hCase⟩
  by_cases hHalt :
      M.machine.accepting q || M.machine.rejecting q
  · exact
      { step := occ.step
        step_lt := occ.step_lt
        q := q
        a := a
        clause := occ.clause
        clause_in_core := occ.clause_in_core
        clause_in_case := hCase
        kind := .haltedStutter
        halted_proof := by
          intro _
          simpa [ntmTransitionCaseCNF, hHalt] using hCase
        active_proof := by
          intro h
          cases h }
  · exact
      { step := occ.step
        step_lt := occ.step_lt
        q := q
        a := a
        clause := occ.clause
        clause_in_core := occ.clause_in_core
        clause_in_case := hCase
        kind := .activeChoice
        halted_proof := by
          intro h
          cases h
        active_proof := by
          intro _
          simpa [ntmTransitionCaseCNF, hHalt] using hCase }

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
#print axioms MCore.Real.P03TransitionSignature.transition_step_clause_has_case
#print axioms MCore.Real.P03TransitionSignature.active_clause_region
#print axioms MCore.Real.P03TransitionSignature.signature_of_occurrence
#print axioms MCore.Real.P03TransitionSignature.occurrence_of_core_touch
#print axioms MCore.Real.P03TransitionSignature.occurrence_of_interaction_core

end P03TransitionSignature
end Real
end MCore
