import MCore.Real.P02DeterministicRejectionTableau

namespace MCore
namespace Real
namespace P02SemanticSelfSubstitution

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02DeterministicRejectionTableau

/-- Canonical encoded rejection tableau for candidate M on source input x,
using exactly M's own polynomial clock at x. -/
def rejectCode
    (M : PolyDTMCandidate)
    (x : BitString) : BitString :=
  encodeCircuit
    (boundedRejectCircuit_DTM M x (M.timeBound x.length))

/-- Material semantics of the encoded rejection tableau. -/
theorem rejectCode_semantics
    (M : PolyDTMCandidate)
    (x : BitString) :
    SATBits circuitBitEncoding (rejectCode M x) ↔
      M.machine.HaltsWithin
        (M.timeBound x.length)
        (initialTMConfig M.machine x) ∧
      M.accepting
        (M.machine.run
          (M.timeBound x.length)
          (initialTMConfig M.machine x)).state = false := by
  unfold rejectCode
  rw [encoded_sat_equivalence]
  exact rejection_tableau_correctness M x (M.timeBound x.length)

/-- If M is correct on rejectCode M x, then the output bit on the encoded
rejection tableau is the Boolean complement of the output bit on x,
provided M halts on x at its own clock. -/
theorem correctAt_rejectCode_flip
    (M : PolyDTMCandidate)
    (x : BitString)
    (hx :
      M.machine.HaltsWithin
        (M.timeBound x.length)
        (initialTMConfig M.machine x))
    (hCorrect :
      M.CorrectAt
        (SATBits circuitBitEncoding)
        (rejectCode M x)) :
    (M.accepting
        (M.machine.run
          (M.timeBound (rejectCode M x).length)
          (initialTMConfig M.machine (rejectCode M x))).state = true) ↔
      (M.accepting
        (M.machine.run
          (M.timeBound x.length)
          (initialTMConfig M.machine x)).state = false) := by
  rcases hCorrect with ⟨_, hiff⟩
  constructor
  · intro hacc
    exact (rejectCode_semantics M x).mp (hiff.mp hacc) |>.2
  · intro hrej
    exact hiff.mpr ((rejectCode_semantics M x).mpr ⟨hx, hrej⟩)

/-- Semantic closure is strictly weaker than literal self-code equality:
only M's observed acceptance bit must agree between x and rejectCode M x. -/
def SemanticClosureAt
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  M.accepting
      (M.machine.run
        (M.timeBound (rejectCode M x).length)
        (initialTMConfig M.machine (rejectCode M x))).state =
    M.accepting
      (M.machine.run
        (M.timeBound x.length)
        (initialTMConfig M.machine x)).state

/-- A semantic collision already forces failure of correctness on rejectCode.
No literal fixed point x = rejectCode M x is required. -/
theorem semantic_closure_forces_failure
    (M : PolyDTMCandidate)
    (x : BitString)
    (hx :
      M.machine.HaltsWithin
        (M.timeBound x.length)
        (initialTMConfig M.machine x))
    (hclose : SemanticClosureAt M x) :
    ¬ M.CorrectAt
        (SATBits circuitBitEncoding)
        (rejectCode M x) := by
  intro hCorrect
  have hflip := correctAt_rejectCode_flip M x hx hCorrect
  unfold SemanticClosureAt at hclose
  cases hsrc :
      M.accepting
        (M.machine.run
          (M.timeBound x.length)
          (initialTMConfig M.machine x)).state with
  | false =>
      have hcodeFalse :
          M.accepting
              (M.machine.run
                (M.timeBound (rejectCode M x).length)
                (initialTMConfig M.machine (rejectCode M x))).state = false := by
        simpa [hsrc] using hclose
      have hcodeTrue := hflip.mpr hsrc
      simp_all
  | true =>
      have hcodeTrue :
          M.accepting
              (M.machine.run
                (M.timeBound (rejectCode M x).length)
                (initialTMConfig M.machine (rejectCode M x))).state = true := by
        simpa [hsrc] using hclose
      have hsrcFalse := hflip.mp hcodeTrue
      simp_all

/-- Exact positive material remaining after the rejection-tableau gate:
for every candidate, find one source input on which it halts and whose
rejection code has the same observed acceptance bit. -/
def SemanticCollisionProducer : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ x : BitString,
      M.machine.HaltsWithin
        (M.timeBound x.length)
        (initialTMConfig M.machine x) ∧
      SemanticClosureAt M x

theorem semanticCollisionProducer_implies_universal_failure :
    SemanticCollisionProducer →
      UniversalFailure (SATBits circuitBitEncoding) := by
  intro H
  intro M
  rcases H M with ⟨x, hx, hclose⟩
  refine ⟨rejectCode M x, ?_⟩
  exact semantic_closure_forces_failure M x hx hclose

#print axioms MCore.Real.P02SemanticSelfSubstitution.rejectCode_semantics
#print axioms MCore.Real.P02SemanticSelfSubstitution.correctAt_rejectCode_flip
#print axioms MCore.Real.P02SemanticSelfSubstitution.semantic_closure_forces_failure
#print axioms MCore.Real.P02SemanticSelfSubstitution.semanticCollisionProducer_implies_universal_failure

end P02SemanticSelfSubstitution
end Real
end MCore
