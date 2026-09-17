import MCore.CircuitC3

namespace MCore
namespace CircuitC4

open CircuitK1 CircuitC2 CircuitC3

/-- A finite, unnormalised restriction distribution. We keep weights in Nat so
C4 requires no probability axioms or analytic library. -/
structure WeightedRestriction where
  restriction : Restriction
  weight : Nat

/-- Weighted total drop over a finite sample. -/
def weightedDrop (sample : List WeightedRestriction) (c : Circuit) : Nat :=
  sample.foldr (fun x acc => x.weight * drop x.restriction c + acc) 0

/-- Total sample weight. -/
def totalWeight (sample : List WeightedRestriction) : Nat :=
  sample.foldr (fun x acc => x.weight + acc) 0

/-- Integer cross-multiplied formulation of a lower bound on expected drop:
`E[drop] >= numerator / denominator`, without division or rounding. -/
def ExpectedDropAtLeast
    (sample : List WeightedRestriction) (c : Circuit)
    (numerator denominator : Nat) : Prop :=
  numerator * totalWeight sample ≤ denominator * weightedDrop sample c

/-- Equal-weight two-point sample: one fixing x0=true, one leaving x0 free. -/
def demoSample : List WeightedRestriction :=
  [{ restriction := fixesZeroTrue, weight := 1 },
   { restriction := leavesZeroFree, weight := 1 }]

@[simp] theorem demo_totalWeight : totalWeight demoSample = 2 := by rfl

@[simp] theorem demo_weightedDrop : weightedDrop demoSample reducibleExample = 3 := by
  simp [weightedDrop, demoSample, drop, potential, restrictedSimplified,
    reducibleExample, fixesZeroTrue, leavesZeroFree, restrict, simplify, μ, size, depth]

/-- For the concrete two-point sample the exact average drop is 3/2. -/
theorem demo_expected_drop_three_halves :
    ExpectedDropAtLeast demoSample reducibleExample 3 2 := by
  simp [ExpectedDropAtLeast]

/-- Zero expected drop remains possible: duplicating the free restriction does
not create progress. This blocks promotion from one positive sample to a
universal distributional theorem. -/
def zeroDropSample : List WeightedRestriction :=
  [{ restriction := leavesZeroFree, weight := 1 },
   { restriction := leavesZeroFree, weight := 1 }]

@[simp] theorem zero_sample_weightedDrop :
    weightedDrop zeroDropSample oneInput = 0 := by
  simp [weightedDrop, zeroDropSample, drop, potential, restrictedSimplified,
    leavesZeroFree, oneInput, restrict, simplify, μ, size, depth]

theorem not_all_samples_positive :
    ¬ (∀ (sample : List WeightedRestriction) (c : Circuit),
      0 < totalWeight sample → 0 < weightedDrop sample c) := by
  intro h
  have hs := h zeroDropSample oneInput
  simp [zeroDropSample, totalWeight, zero_sample_weightedDrop] at hs

theorem c4_classical_endpoint_not_promoted : ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  c3_classical_endpoint_not_promoted

theorem c4_k10_not_promoted : ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  c3_k10_not_promoted

end CircuitC4
end MCore
