import MCore.CircuitC7

namespace MCore
namespace CircuitC8

open CircuitK1 CircuitC2 CircuitC3 CircuitC4 CircuitC5 CircuitC6 CircuitC7

/-- One abstract branch of a restriction recurrence. `fixedVars` is the number
of variables eliminated and `potentialDrop` is the certified potential decrease. -/
structure RecurrenceBranch where
  fixedVars : Nat
  potentialDrop : Nat

/-- A branch makes strict progress if it fixes a variable or decreases the
potential. This is deliberately weaker than a SAT speedup claim. -/
def BranchProgress (b : RecurrenceBranch) : Prop :=
  0 < b.fixedVars ∨ 0 < b.potentialDrop

/-- Lexicographic scalar rank used only to certify termination of a finite
restriction descent: variables dominate potential by factor `potential + 1`. -/
def recurrenceRank (vars potential : Nat) : Nat :=
  vars * (potential + 1) + potential

/-- If at least one variable is fixed, the rank strictly decreases whenever the
new potential does not exceed the old potential. -/
theorem rank_decreases_when_variable_fixed
    (vars potential fixedVars newPotential : Nat)
    (hfix : 0 < fixedVars) (hfixle : fixedVars ≤ vars)
    (hpot : newPotential ≤ potential) :
    recurrenceRank (vars - fixedVars) newPotential < recurrenceRank vars potential := by
  unfold recurrenceRank
  have hv : vars - fixedVars < vars := Nat.sub_lt (Nat.zero_lt_of_lt hfix) hfix
  have hmul : (vars - fixedVars) * (potential + 1) < vars * (potential + 1) :=
    Nat.mul_lt_mul_of_pos_right hv (Nat.succ_pos potential)
  have hleft : (vars - fixedVars) * (newPotential + 1) ≤
      (vars - fixedVars) * (potential + 1) := by
    exact Nat.mul_le_mul_left _ (Nat.succ_le_succ hpot)
  omega

/-- If no variable is fixed but potential strictly drops, the same scalar rank
strictly decreases. -/
theorem rank_decreases_when_potential_drops
    (vars potential newPotential : Nat)
    (hpot : newPotential < potential) :
    recurrenceRank vars newPotential < recurrenceRank vars potential := by
  unfold recurrenceRank
  have hs : newPotential + 1 ≤ potential := Nat.succ_le_iff.mpr hpot
  omega

/-- The C7 good-mass condition provides an aggregate amount of certified
potential decrease. This is the exact interface available before any branching
factor or runtime theorem is supplied. -/
theorem good_mass_supplies_aggregate_progress
    (sample : List WeightedRestriction) (c : Circuit)
    (minGoodWeight minDrop : Nat)
    (h : GoodMassWitness sample c minGoodWeight minDrop) :
    minDrop * minGoodWeight ≤ weightedDrop sample c :=
  good_mass_implies_weightedDrop_lower_bound sample c minGoodWeight minDrop h

/-- Termination/progress alone cannot certify a nontrivial runtime saving. The
zero saving is always compatible with the current abstract interface. -/
def RuntimeSavingWitness (saving : Nat) : Prop := 0 < saving

theorem zero_is_not_runtime_saving : ¬ RuntimeSavingWitness 0 := by
  simp [RuntimeSavingWitness]

/-- Explicit firewall: C8 establishes descent machinery, not a Circuit-SAT
algorithm or Williams-style lower bound. -/
theorem c8_classical_endpoint_not_promoted : ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  c7_classical_endpoint_not_promoted

theorem c8_k10_not_promoted : ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  c7_k10_not_promoted

end CircuitC8
end MCore
