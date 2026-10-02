import MCore.Real.P02AntiModels
import MCore.Real.P02TableauDynamics

namespace MCore
namespace Real
namespace P03MaterialLaw

open CanonicalFinalProof
open PNPNTMTableauEncoding
open P02ComplementRunRealization
open P02TotalCandidateKleeneReduction
open P02TableauDynamics
open P02OddSemanticRecurrence

/--
The three concrete clause regions of the bounded Cook--Levin tableau.
This classification is syntactic and contains no acceptance bit.
-/
inductive ClausePhase where
  | init
  | transit
  | terminal
  deriving DecidableEq, Repr

/-- A CNF is unsatisfiable when no Boolean assignment satisfies it. -/
def CNFUnsat (F : NTMCNF) : Prop :=
  ∀ sigma : Assignment, evalNTMCNF sigma F = false

/-- Concrete clause block selected by a phase. -/
def phaseCNF
    (phase : ClausePhase)
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : NTMCNF :=
  match phase with
  | .init => ntmInitialCNF M x t
  | .transit => ntmTransitionsCNF M x t
  | .terminal => ntmFinalAcceptanceCNF M t

/--
A phase witness is evidence that one concrete tableau block is an
unsatisfiable core.  It is intentionally partial: satisfiable tableaux do not
have to manufacture an UNSAT phase.
-/
structure ClausePhaseWitness
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) where
  phase : ClausePhase
  unsat : CNFUnsat (phaseCNF phase M x t)

/--
Clause-derived phase extractor target.  The extractor is only required on
inputs for which the complete bounded tableau is unsatisfiable.

No DeclaredAccepts, ObsEquiv, OddGap, or P/NP endpoint occurs in the fields.
-/
structure ClausePhaseExtractor
    (M : PolyNTMCandidate) where
  locate :
    ∀ (x : BitString) (t : Nat),
      CNFUnsat (boundedExecTableauCNF_NTM M x t) →
      ClausePhaseWitness M x t

/--
The exact material parity-mixing target.

A proof must derive odd-distance repetition from concrete clause structure and
then independently justify that equal clause phase projects to ObsEquiv.  This
structure is deliberately uninhabited here.
-/
structure ClauseDerivedParityMixing
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) where
  extractor :
    ClausePhaseExtractor (complementToNTMCandidate M)
  seed : BitString
  i j : Nat
  odd_gap : OddGap i j
  phase_at :
    BitString → ClausePhase
  same_phase :
    phase_at
        (Orbit (R_M M hTotal) seed i) =
      phase_at
        (Orbit (R_M M hTotal) seed j)
  phase_to_obs :
    ∀ u v : BitString,
      phase_at u = phase_at v →
      ObsEquiv M u v

/--
Universal producer target for P03.  This is a proposition only; no axiom or
inhabitant is supplied.
-/
def P03_MATERIAL_LAW : Prop :=
  ∀ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M),
    Nonempty (ClauseDerivedParityMixing M hTotal)

/--
Fail-closed status marker.  The actual proof obligation is P03_MATERIAL_LAW.
-/
def MATERIAL_GAPS : Nat := 1
def OPEN_BRIDGE : Nat := 1
def GREEN : Bool := false

end P03MaterialLaw
end Real
end MCore
