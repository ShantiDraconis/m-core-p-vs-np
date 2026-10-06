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

/-- Own-clock halting predicate used to separate the trivial nonhalting
failure branch from the genuinely semantic branch. -/
def OwnClockHalts
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  M.machine.HaltsWithin
    (M.timeBound x.length)
    (initialTMConfig M.machine x)

/-- Any own-clock nonhalting input already falsifies CorrectAt directly. -/
theorem nonhalting_input_forces_failure
    (M : PolyDTMCandidate)
    (x : BitString)
    (hx : ¬ OwnClockHalts M x) :
    ¬ M.CorrectAt (SATBits circuitBitEncoding) x := by
  intro hCorrect
  exact hx hCorrect.1

/-- Strong sufficient producer retained for comparison. It is not the exact
remaining frontier because candidates with a nonhalting input already fail
CorrectAt without any semantic collision. -/
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


/-- Exact residual after discharging the trivial nonhalting branch:
only candidates that halt at their own clock on every input need a semantic
collision. -/
def TotalClockSemanticCollision : Prop :=
  ∀ M : PolyDTMCandidate,
    (∀ x : BitString, OwnClockHalts M x) →
      ∃ x : BitString, SemanticClosureAt M x


/-- Observable Boolean produced by M on input x at M's own clock. -/
def observedBit
    (M : PolyDTMCandidate)
    (x : BitString) : Bool :=
  M.accepting
    (M.machine.run
      (M.timeBound x.length)
      (initialTMConfig M.machine x)).state

theorem semanticClosureAt_iff_observed_eq
    (M : PolyDTMCandidate)
    (x : BitString) :
    SemanticClosureAt M x ↔
      observedBit M (rejectCode M x) = observedBit M x := by
  rfl

/-- For Booleans, failure of semantic closure is exactly a bit flip. -/
theorem not_semanticClosureAt_iff_flip
    (M : PolyDTMCandidate)
    (x : BitString) :
    ¬ SemanticClosureAt M x ↔
      observedBit M (rejectCode M x) = !(observedBit M x) := by
  rw [semanticClosureAt_iff_observed_eq]
  cases h0 : observedBit M x <;>
    cases h1 : observedBit M (rejectCode M x) <;>
    simp_all

/-- Global absence of collisions is exactly global alternation along rejectCode. -/
theorem no_semantic_collision_iff_global_flip
    (M : PolyDTMCandidate) :
    (¬ ∃ x : BitString, SemanticClosureAt M x) ↔
      (∀ x : BitString,
        observedBit M (rejectCode M x) = !(observedBit M x)) := by
  constructor
  · intro H x
    exact (not_semanticClosureAt_iff_flip M x).mp (by
      intro hx
      exact H ⟨x, hx⟩)
  · intro H hex
    rcases hex with ⟨x, hx⟩
    have hflip := H x
    have hnot := (not_semanticClosureAt_iff_flip M x).mpr hflip
    exact hnot hx

/-- Exact anti-alternation formulation of the total-clock residual. -/
def TotalClockAntiAlternation : Prop :=
  ∀ M : PolyDTMCandidate,
    (∀ x : BitString, OwnClockHalts M x) →
      ¬ (∀ x : BitString,
        observedBit M (rejectCode M x) = !(observedBit M x))

theorem totalClockCollision_iff_antiAlternation :
    TotalClockSemanticCollision ↔ TotalClockAntiAlternation := by
  constructor
  · intro H M htotal hflip
    rcases H M htotal with ⟨x, hclose⟩
    have hnot := (not_semanticClosureAt_iff_flip M x).mpr (hflip x)
    exact hnot hclose
  · intro H M htotal
    by_contra hnone
    have hflip :=
      (no_semantic_collision_iff_global_flip M).mp hnone
    exact H M htotal hflip

theorem totalClockSemanticCollision_implies_universal_failure :
    TotalClockSemanticCollision →
      UniversalFailure (SATBits circuitBitEncoding) := by
  intro H
  intro M
  classical
  by_cases htotal : ∀ x : BitString, OwnClockHalts M x
  · rcases H M htotal with ⟨x, hclose⟩
    refine ⟨rejectCode M x, ?_⟩
    exact semantic_closure_forces_failure M x (htotal x) hclose
  · push_neg at htotal
    rcases htotal with ⟨x, hx⟩
    exact ⟨x, nonhalting_input_forces_failure M x hx⟩

/-- Equivalent split form of the remaining sufficient material. -/
def TerminalSemanticSplit : Prop :=
  ∀ M : PolyDTMCandidate,
    (∃ x : BitString, ¬ OwnClockHalts M x) ∨
      (∃ x : BitString, OwnClockHalts M x ∧ SemanticClosureAt M x)

theorem totalClockSemanticCollision_implies_terminalSplit :
    TotalClockSemanticCollision → TerminalSemanticSplit := by
  intro H M
  classical
  by_cases htotal : ∀ x : BitString, OwnClockHalts M x
  · right
    rcases H M htotal with ⟨x, hclose⟩
    exact ⟨x, htotal x, hclose⟩
  · left
    push_neg at htotal
    exact htotal

theorem terminalSplit_implies_universal_failure :
    TerminalSemanticSplit →
      UniversalFailure (SATBits circuitBitEncoding) := by
  intro H M
  rcases H M with hnonhalt | hcollision
  · rcases hnonhalt with ⟨x, hx⟩
    exact ⟨x, nonhalting_input_forces_failure M x hx⟩
  · rcases hcollision with ⟨x, hx, hclose⟩
    exact ⟨rejectCode M x, semantic_closure_forces_failure M x hx hclose⟩

#print axioms MCore.Real.P02SemanticSelfSubstitution.rejectCode_semantics
#print axioms MCore.Real.P02SemanticSelfSubstitution.correctAt_rejectCode_flip
#print axioms MCore.Real.P02SemanticSelfSubstitution.semantic_closure_forces_failure
#print axioms MCore.Real.P02SemanticSelfSubstitution.semanticCollisionProducer_implies_universal_failure
#print axioms MCore.Real.P02SemanticSelfSubstitution.nonhalting_input_forces_failure
#print axioms MCore.Real.P02SemanticSelfSubstitution.totalClockSemanticCollision_implies_universal_failure
#print axioms MCore.Real.P02SemanticSelfSubstitution.not_semanticClosureAt_iff_flip
#print axioms MCore.Real.P02SemanticSelfSubstitution.no_semantic_collision_iff_global_flip
#print axioms MCore.Real.P02SemanticSelfSubstitution.totalClockCollision_iff_antiAlternation
#print axioms MCore.Real.P02SemanticSelfSubstitution.terminalSplit_implies_universal_failure

end P02SemanticSelfSubstitution
end Real
end MCore
