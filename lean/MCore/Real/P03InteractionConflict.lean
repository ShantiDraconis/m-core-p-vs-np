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

#print axioms MCore.Real.P03InteractionConflict.terminal_sat_implies_nonempty_lits

end P03InteractionConflict
end Real
end MCore
