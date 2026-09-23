import MCore.C11.BranchingCost

namespace MCore
namespace Real
namespace P02RestrictionLowerBoundPattern

open C9 C10 C11 CircuitK1

/-- Exact amortized structural drop used by C11. -/
def amortizedDrop (α β : Nat) (ρ : Restriction) (t : FormulaTree) : Nat :=
  Potential α β t - Potential α β (D ρ t)

/-- C11 PaysOff is exactly the regime where the number of fixed branching bits
is strictly smaller than the certified potential drop. -/
theorem paysOff_implies_costBits_lt_amortizedDrop
    (α β : Nat) (ρ : Restriction) (t : FormulaTree)
    (h : PaysOff α β ρ t) :
    costBits ρ t < amortizedDrop α β ρ t := by
  unfold PaysOff amortizedDrop at *
  omega

/-- Separation-oriented local pattern: every progressing restriction fails to
amortize its branching bits. This is intentionally the opposite orientation
from C11 PaysOff. -/
def PersistentBranchingDeficit
    (α β : Nat) (t : FormulaTree) : Prop :=
  ∀ ρ : Restriction,
    RestrictionProgress ρ t →
      amortizedDrop α β ρ t ≤ costBits ρ t

theorem persistentBranchingDeficit_excludes_payoff
    (α β : Nat) (t : FormulaTree)
    (h : PersistentBranchingDeficit α β t) :
    ∀ ρ : Restriction,
      RestrictionProgress ρ t →
        ¬ PaysOff α β ρ t := by
  intro ρ hprog hpay
  have hlt := paysOff_implies_costBits_lt_amortizedDrop α β ρ t hpay
  have hle := h ρ hprog
  omega

/-- Quantitative family-level deficit with a uniform positive margin after n0. -/
def PersistentBranchingDeficitFamily
    (α β : Nat) (f : Nat → FormulaTree) : Prop :=
  ∃ (c n0 : Nat), 0 < c ∧
    ∀ n : Nat, n0 ≤ n →
      ∀ ρ : Restriction,
        RestrictionProgress ρ (f n) →
          amortizedDrop α β ρ (f n) ≤ costBits ρ (f n) ∧
          c ≤ costBits ρ (f n) - amortizedDrop α β ρ (f n)

theorem persistentFamily_excludes_eventual_payoff
    {α β : Nat} {f : Nat → FormulaTree}
    (h : PersistentBranchingDeficitFamily α β f) :
    ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
      ∀ ρ : Restriction,
        RestrictionProgress ρ (f n) →
          ¬ PaysOff α β ρ (f n) := by
  rcases h with ⟨c, n0, hc, h⟩
  refine ⟨n0, ?_⟩
  intro n hn ρ hprog hpay
  have hdef := (h n hn ρ hprog).1
  have hlt :=
    paysOff_implies_costBits_lt_amortizedDrop α β ρ (f n) hpay
  omega

/-- A family suitable for a SAT lower-bound transfer must contain a polynomial
reduction image of arbitrary canonical SAT inputs. Merely generating one
formula per n (as the current C12 experiments do) is not enough. -/
structure SATReductionIntoFamily
    (Family : FormulaTree → Prop) where
  reduce : BitString → FormulaTree
  sizeBound : Nat → Nat
  size_poly : CanonicalFinalProof.PolynomialTimeBound sizeBound
  size_le : ∀ x, CircuitK1.size (reduce x) ≤ sizeBound x.length
  lands : ∀ x, Family (reduce x)
  correct :
    ∀ x,
      CanonicalSATBoundary.SATBits CanonicalCircuitBits.circuitBitEncoding x ↔
        CircuitK1.SATLanguage (reduce x)

/-- What restriction lower bounds actually control is a restricted
decision-tree/branching model. To reach P02 one needs a genuine simulation
theorem from every hardened polynomial DTM deciding SAT to that branching
model. This field is intentionally explicit rather than hidden in OPEN_BRIDGE. -/
structure DTMToRestrictionTreeAdapter
    (Family : FormulaTree → Prop) where
  contradicts_poly_decider :
    (∃ R : SATReductionIntoFamily Family,
      True) →
    PersistentBranchingDeficitFamily 1 1
      (fun n => C12.randomKCNF n (2 * n + 1) 3 0) →
    ¬ CanonicalFinalProof.InP
      (CanonicalSATBoundary.SATBits CanonicalCircuitBits.circuitBitEncoding)

/-- Honest Lane-4 transfer target. The two mathematical producers are explicit:
a SAT reduction into the hard family and a DTM-to-restriction-tree simulation. -/
def RestrictionLowerBoundTransfer
    (Family : FormulaTree → Prop) : Prop :=
  Nonempty (SATReductionIntoFamily Family) ∧
  Nonempty (DTMToRestrictionTreeAdapter Family)

#print axioms MCore.Real.P02RestrictionLowerBoundPattern.paysOff_implies_costBits_lt_amortizedDrop
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.persistentBranchingDeficit_excludes_payoff
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.persistentFamily_excludes_eventual_payoff

end P02RestrictionLowerBoundPattern
end Real
end MCore
