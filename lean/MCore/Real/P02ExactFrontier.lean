import MCore.Real.CanonicalSATNTMAttack
import MCore.Real.FailProofAllGaps

namespace MCore
namespace Real
namespace P02ExactFrontier

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open CanonicalSATNTMAttack
open FailProofAllGaps

/-- The one fixed language used by both P01 and P02. -/
abbrev SATTarget : BitLanguage :=
  SATBits circuitBitEncoding

/-- P01: the same target must have a genuine hardened polynomial NTM. -/
abbrev P01 : Prop :=
  CanonicalSATMachineClosure

/-- P02: every hardened deterministic polynomial-time candidate must fail on
some concrete input for exactly the same target language. -/
abbrev P02 : Prop :=
  UniversalFailure SATTarget

/-- P02 is exactly non-membership in the repository's hardened P class. -/
theorem p02_iff_sat_not_in_p :
    P02 ↔ ¬ InP SATTarget :=
  universal_failure_iff_not_in_p

/-- The Skolemized failure-generator presentation is equivalent to P02; it
does not weaken the lower bound. -/
theorem failure_generator_iff_p02 :
    Nonempty (FailureGenerator SATTarget) ↔ P02 :=
  failure_generator_iff_universal_failure

/-- P01 + P02 close the internal P != NP endpoint. -/
theorem p01_p02_close_internal
    (hP01 : P01)
    (hP02 : P02) :
    PneqNP :=
  target_failure_implies_p_ne_np hP01 hP02

/-- A fully explicit internal closure package. -/
structure InternalSATSeparationClosure where
  p01 : P01
  p02 : P02

theorem internalSATSeparationClosure_closes
    (C : InternalSATSeparationClosure) :
    PneqNP :=
  p01_p02_close_internal C.p01 C.p02

/--
No abstract K-chain or component certificate is accepted as P02.  The field
below is intentionally the universal failure object itself.
-/
structure P02TerminalCertificate where
  universal_failure :
    ∀ candidate : PolyDTMCandidate,
      ∃ x : BitString,
        ¬ candidate.CorrectAt SATTarget x

def P02TerminalCertificate.toP02
    (C : P02TerminalCertificate) :
    P02 :=
  C.universal_failure

def P02TerminalCertificate.ofP02
    (h : P02) :
    P02TerminalCertificate :=
  { universal_failure := h }

theorem p02_terminal_certificate_iff :
    Nonempty P02TerminalCertificate ↔ P02 := by
  constructor
  · rintro ⟨C⟩
    exact C.toP02
  · intro h
    exact ⟨P02TerminalCertificate.ofP02 h⟩

#print axioms MCore.Real.P02ExactFrontier.p02_iff_sat_not_in_p
#print axioms MCore.Real.P02ExactFrontier.failure_generator_iff_p02
#print axioms MCore.Real.P02ExactFrontier.p01_p02_close_internal
#print axioms MCore.Real.P02ExactFrontier.internalSATSeparationClosure_closes
#print axioms MCore.Real.P02ExactFrontier.p02_terminal_certificate_iff

end P02ExactFrontier
end Real
end MCore
