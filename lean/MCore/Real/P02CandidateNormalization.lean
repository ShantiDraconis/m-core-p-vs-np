import MCore.Real.CanonicalFinalProof
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P02CandidateNormalization

open CanonicalFinalProof
open MachineRunLemmas

/--
Replace the time bound of a deterministic polynomial-time candidate by one
explicit monomial bound extracted from its existing PolynomialTimeBound proof.

The finite machine, blank proof, and accepting predicate are unchanged.
This is a bound normalization theorem only; it does not by itself construct
an effective enumeration of PolyDTMCandidate.
-/
def normalizedCandidate
    (M : PolyDTMCandidate)
    (coefficient exponent : Nat) :
    PolyDTMCandidate where
  stateCount := M.stateCount
  machine := M.machine
  blank_none := M.blank_none
  accepting := M.accepting
  timeBound := fun n => coefficient * (n + 1) ^ exponent
  time_poly := by
    refine ⟨coefficient, exponent, ?_⟩
    intro n
    exact Nat.le_refl _

@[simp] theorem normalizedCandidate_stateCount
    (M : PolyDTMCandidate)
    (c k : Nat) :
    (normalizedCandidate M c k).stateCount = M.stateCount := rfl

@[simp] theorem normalizedCandidate_machine
    (M : PolyDTMCandidate)
    (c k : Nat) :
    (normalizedCandidate M c k).machine = M.machine := rfl

@[simp] theorem normalizedCandidate_accepting
    (M : PolyDTMCandidate)
    (c k : Nat) :
    (normalizedCandidate M c k).accepting = M.accepting := rfl

@[simp] theorem normalizedCandidate_timeBound
    (M : PolyDTMCandidate)
    (c k n : Nat) :
    (normalizedCandidate M c k).timeBound n =
      c * (n + 1) ^ k := rfl

/--
Correctness at one input is preserved when the normalized explicit bound
dominates the original time bound.

The proof uses only deterministic run stability after a halting state:
once M has halted by its original fuel, extra fuel leaves the final
configuration unchanged.
-/
theorem correctAt_preserved_by_dominating_bound
    (M : PolyDTMCandidate)
    (c k : Nat)
    (hbound : ∀ n : Nat,
      M.timeBound n ≤ c * (n + 1) ^ k)
    (language : BitLanguage)
    (x : BitString)
    (hCorrect : M.CorrectAt language x) :
    (normalizedCandidate M c k).CorrectAt language x := by
  unfold PolyDTMCandidate.CorrectAt at hCorrect ⊢
  dsimp [normalizedCandidate] at *
  let config := initialTMConfig M.machine x
  change
    M.machine.HaltsWithin (M.timeBound x.length) config ∧
      (M.accepting
          (M.machine.run (M.timeBound x.length) config).state = true
        ↔ language x) at hCorrect
  change
    M.machine.HaltsWithin (c * (x.length + 1) ^ k) config ∧
      (M.accepting
          (M.machine.run (c * (x.length + 1) ^ k) config).state = true
        ↔ language x)
  rcases hCorrect with ⟨hhalt, hsem⟩
  have hle :
      M.timeBound x.length ≤ c * (x.length + 1) ^ k :=
    hbound x.length
  have hhalt' :
      M.machine.HaltsWithin (c * (x.length + 1) ^ k) config :=
    haltsWithin_mono M.machine config hle hhalt
  have hrun :
      M.machine.run (c * (x.length + 1) ^ k) config =
        M.machine.run (M.timeBound x.length) config := by
    exact run_to_larger_fuel_of_halt
      M.machine
      config
      (M.machine.run (M.timeBound x.length) config)
      hle
      rfl
      hhalt
  refine ⟨hhalt', ?_⟩
  rw [hrun]
  exact hsem

/--
G2.0 canonical normalization.

Every PolyDTMCandidate admits an explicit coefficient/exponent presentation
whose machine semantics are unchanged and whose pointwise CorrectAt facts are
preserved.

No diagonal witness, SAT lower bound, FailureGenerator, or P != NP conclusion
is produced here.
-/
theorem canonical_normalization :
    ∀ M : PolyDTMCandidate,
      ∃ coefficient exponent : Nat,
        ∃ M' : PolyDTMCandidate,
          M'.stateCount = M.stateCount ∧
          M'.machine = M.machine ∧
          M'.accepting = M.accepting ∧
          M'.timeBound =
            (fun n => coefficient * (n + 1) ^ exponent) ∧
          (∀ language : BitLanguage,
            ∀ x : BitString,
              M.CorrectAt language x →
                M'.CorrectAt language x) := by
  intro M
  rcases M.time_poly with ⟨coefficient, exponent, hbound⟩
  refine ⟨coefficient, exponent,
    normalizedCandidate M coefficient exponent, rfl, rfl, rfl, rfl, ?_⟩
  intro language x hCorrect
  exact correctAt_preserved_by_dominating_bound
    M coefficient exponent hbound language x hCorrect

/--
A compact G2.0 certificate object.  Keeping the witness packaged makes the
next gate consume only normalized candidates without re-extracting polynomial
constants.
-/
structure NormalizedCandidateWitness
    (M : PolyDTMCandidate) where
  coefficient : Nat
  exponent : Nat
  candidate : PolyDTMCandidate
  stateCount_eq : candidate.stateCount = M.stateCount
  machine_eq : candidate.machine = M.machine
  accepting_eq : candidate.accepting = M.accepting
  timeBound_eq :
    candidate.timeBound =
      (fun n => coefficient * (n + 1) ^ exponent)
  preserves_correctAt :
    ∀ language : BitLanguage,
      ∀ x : BitString,
        M.CorrectAt language x →
          candidate.CorrectAt language x

noncomputable def normalizationWitness
    (M : PolyDTMCandidate) :
    NormalizedCandidateWitness M := by
  classical
  rcases canonical_normalization M with
    ⟨coefficient, exponent, M',
      hState, hMachine, hAccept, hTime, hCorrect⟩
  exact
    { coefficient := coefficient
      exponent := exponent
      candidate := M'
      stateCount_eq := hState
      machine_eq := hMachine
      accepting_eq := hAccept
      timeBound_eq := hTime
      preserves_correctAt := hCorrect }

#print axioms MCore.Real.P02CandidateNormalization.correctAt_preserved_by_dominating_bound
#print axioms MCore.Real.P02CandidateNormalization.canonical_normalization
#print axioms MCore.Real.P02CandidateNormalization.normalizationWitness

end P02CandidateNormalization
end Real
end MCore
