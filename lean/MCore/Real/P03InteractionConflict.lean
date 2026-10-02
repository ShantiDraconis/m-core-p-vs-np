import MCore.Real.P03Lemmas

namespace MCore
namespace Real
namespace P03InteractionConflict

open CanonicalFinalProof
open PNPNTMTableauEncoding
open P03MaterialLaw
open P03Lemmas

/--
A non-degenerate interaction conflict.

The prefix Init+Transit is satisfiable, Terminal is satisfiable in isolation,
but the complete tableau is unsatisfiable.  Thus the contradiction cannot be
explained by a terminal-empty-clause degeneracy or by an inconsistent physical
prefix alone.
-/
structure OrbitalInteractionConflict
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) where
  h_term_sat :
    CNFSat (ntmFinalAcceptanceCNF M t)
  h_prefix_sat :
    CNFSat (supportedCNF initTransitSupport M x t)
  h_whole_unsat :
    CNFUnsat (boundedExecTableauCNF_NTM M x t)

/-- Degenerate case: Terminal is already contradictory without Init/Transit. -/
def IsTerminalDegenerate
    (M : PolyNTMCandidate)
    (t : Nat) : Prop :=
  CNFUnsat (ntmFinalAcceptanceCNF M t)

/-- Genuine interaction case used by the P03 material route. -/
def IsInteractionConflict
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : Prop :=
  Nonempty (OrbitalInteractionConflict M x t)

/-- Every interaction conflict canonically yields the full conflict witness. -/
def OrbitalInteractionConflict.toClauseConflictWitness
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    (C : OrbitalInteractionConflict M x t) :
    ClauseConflictWitness M x t :=
  (fullConflictExtractor M).locate x t C.h_whole_unsat

/--
If Terminal is satisfiable, its accepting-state clause cannot be empty.
This separates genuine interaction conflicts from the [[]] terminal
degeneracy.
-/
theorem terminal_sat_implies_nonempty_lits
    {M : PolyNTMCandidate}
    {t : Nat}
    (h : CNFSat (ntmFinalAcceptanceCNF M t)) :
    ntmAcceptingStateLits M t ≠ [] := by
  intro hEmpty
  rcases h with ⟨sigma, hSat⟩
  simp [ntmFinalAcceptanceCNF, hEmpty, evalNTMCNF, evalNTMClause] at hSat

/--
For positive time, a terminal state variable cannot be the initial state
variable.  This is the only Init/Terminal separation fact that needs t > 0.
-/
theorem terminal_state_ne_initial_state
    (M : PolyNTMCandidate)
    (t : Nat)
    (ht : 0 < t)
    (q0 qt : Fin (M.stateCount + 1)) :
    ntmStateVar M t 0 q0 ≠ ntmStateVar M t t qt := by
  intro hEq
  have h := ntmStateVar_injective M t 0 t q0 qt hEq
  omega

/-- Terminal state variables lie strictly below the head-variable region. -/
theorem terminal_state_ne_initial_head
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (qt : Fin (M.stateCount + 1))
    (a : Option Bool) :
    ntmStateVar M t t qt ≠ ntmHeadVar M t 0 a := by
  exact stateVar_ne_headVar M x t t 0 qt a (by omega) (by omega)

/-- Terminal state variables cannot collide with initial left-tape variables. -/
theorem terminal_state_ne_initial_left
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat)
    (hi : i < ntmRadius x t)
    (qt : Fin (M.stateCount + 1))
    (a : Option Bool) :
    ntmStateVar M t t qt ≠ ntmLeftVar M x t 0 i a := by
  have hs := ntmStateVar_lt_headBase M t t qt (by omega)
  have hl := (ntmLeftVar_range M x t 0 i a (by omega) hi).1
  have hb : ntmHeadBase M t ≤ ntmLeftBase M x t := by
    simp [ntmLeftBase]
  omega

/-- Terminal state variables cannot collide with initial right-tape variables. -/
theorem terminal_state_ne_initial_right
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat)
    (hi : i < ntmRadius x t)
    (qt : Fin (M.stateCount + 1))
    (a : Option Bool) :
    ntmStateVar M t t qt ≠ ntmRightVar M x t 0 i a := by
  have hs := ntmStateVar_lt_headBase M t t qt (by omega)
  have hr := (ntmRightVar_range M x t 0 i a (by omega) hi).1
  have hb : ntmHeadBase M t ≤ ntmRightBase M x t := by
    simp [ntmRightBase, ntmLeftBase]
  omega

#print axioms MCore.Real.P03InteractionConflict.terminal_sat_implies_nonempty_lits
#print axioms MCore.Real.P03InteractionConflict.terminal_state_ne_initial_state
#print axioms MCore.Real.P03InteractionConflict.terminal_state_ne_initial_head
#print axioms MCore.Real.P03InteractionConflict.terminal_state_ne_initial_left
#print axioms MCore.Real.P03InteractionConflict.terminal_state_ne_initial_right

end P03InteractionConflict
end Real
end MCore
